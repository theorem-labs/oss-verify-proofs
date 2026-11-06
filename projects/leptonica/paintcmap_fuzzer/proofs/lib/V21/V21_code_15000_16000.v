(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.H Require GcFlushU21.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_15020 : bv 32 := 0xfd010113.
Lemma F_15020 : fetch_word Ubsan.M.loaded_segments (0x15124 : word) = Some W_15020.
Proof. vm_refl. Qed.
Lemma D_15020 : decode_any W_15020 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15024 : bv 32 := 0x02113423.
Lemma F_15024 : fetch_word Ubsan.M.loaded_segments (0x15128 : word) = Some W_15024.
Proof. vm_refl. Qed.
Lemma D_15024 : decode_any W_15024 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15028 : bv 32 := 0x02813023.
Lemma F_15028 : fetch_word Ubsan.M.loaded_segments (0x1512c : word) = Some W_15028.
Proof. vm_refl. Qed.
Lemma D_15028 : decode_any W_15028 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1502c : bv 32 := 0x00913c23.
Lemma F_1502c : fetch_word Ubsan.M.loaded_segments (0x15130 : word) = Some W_1502c.
Proof. vm_refl. Qed.
Lemma D_1502c : decode_any W_1502c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15030 : bv 32 := 0x01213823.
Lemma F_15030 : fetch_word Ubsan.M.loaded_segments (0x15134 : word) = Some W_15030.
Proof. vm_refl. Qed.
Lemma D_15030 : decode_any W_15030 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15034 : bv 32 := 0x01313423.
Lemma F_15034 : fetch_word Ubsan.M.loaded_segments (0x15138 : word) = Some W_15034.
Proof. vm_refl. Qed.
Lemma D_15034 : decode_any W_15034 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15038 : bv 32 := 0x00050413.
Lemma F_15038 : fetch_word Ubsan.M.loaded_segments (0x1513c : word) = Some W_15038.
Proof. vm_refl. Qed.
Lemma D_15038 : decode_any W_15038 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1503c : bv 32 := 0x08058063.
Lemma F_1503c : fetch_word Ubsan.M.loaded_segments (0x15140 : word) = Some W_1503c.
Proof. vm_refl. Qed.
Lemma D_1503c : decode_any W_1503c = Some (Branch BC_EQ 11 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15040 : bv 32 := 0x00058493.
Lemma F_15040 : fetch_word Ubsan.M.loaded_segments (0x15144 : word) = Some W_15040.
Proof. vm_refl. Qed.
Lemma D_15040 : decode_any W_15040 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15044 : bv 32 := 0x1e858e63.
Lemma F_15044 : fetch_word Ubsan.M.loaded_segments (0x15148 : word) = Some W_15044.
Proof. vm_refl. Qed.
Lemma D_15044 : decode_any W_15044 = Some (Branch BC_EQ 11 8 508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15048 : bv 32 := 0x0074f513.
Lemma F_15048 : fetch_word Ubsan.M.loaded_segments (0x1514c : word) = Some W_15048.
Proof. vm_refl. Qed.
Lemma D_15048 : decode_any W_15048 = Some (OpImm ALU_AND 10 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1504c : bv 32 := 0x20051a63.
Lemma F_1504c : fetch_word Ubsan.M.loaded_segments (0x15150 : word) = Some W_1504c.
Proof. vm_refl. Qed.
Lemma D_1504c : decode_any W_1504c = Some (Branch BC_NE 10 0 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15050 : bv 32 := 0x0104a503.
Lemma F_15050 : fetch_word Ubsan.M.loaded_segments (0x15154 : word) = Some W_15050.
Proof. vm_refl. Qed.
Lemma D_15050 : decode_any W_15050 = Some (Load SZ4 true 10 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15054 : bv 32 := 0x200005b7.
Lemma F_15054 : fetch_word Ubsan.M.loaded_segments (0x15158 : word) = Some W_15054.
Proof. vm_refl. Qed.
Lemma D_15054 : decode_any W_15054 = Some (Lui 11 131072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15058 : bv 32 := 0x00b505b3.
Lemma F_15058 : fetch_word Ubsan.M.loaded_segments (0x1515c : word) = Some W_15058.
Proof. vm_refl. Qed.
Lemma D_15058 : decode_any W_15058 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1505c : bv 32 := 0x01e5d59b.
Lemma F_1505c : fetch_word Ubsan.M.loaded_segments (0x15160 : word) = Some W_1505c.
Proof. vm_refl. Qed.
Lemma D_1505c : decode_any W_1505c = Some (ShiftImm32 ALU_SRL 11 11 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15060 : bv 32 := 0x20059063.
Lemma F_15060 : fetch_word Ubsan.M.loaded_segments (0x15164 : word) = Some W_15060.
Proof. vm_refl. Qed.
Lemma D_15060 : decode_any W_15060 = Some (Branch BC_NE 11 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15064 : bv 32 := 0x0044a583.
Lemma F_15064 : fetch_word Ubsan.M.loaded_segments (0x15168 : word) = Some W_15064.
Proof. vm_refl. Qed.
Lemma D_15064 : decode_any W_15064 = Some (Load SZ4 true 11 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15068 : bv 32 := 0x0025151b.
Lemma F_15068 : fetch_word Ubsan.M.loaded_segments (0x1516c : word) = Some W_15068.
Proof. vm_refl. Qed.
Lemma D_15068 : decode_any W_15068 = Some (ShiftImm32 ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1506c : bv 32 := 0x02b50933.
Lemma F_1506c : fetch_word Ubsan.M.loaded_segments (0x15170 : word) = Some W_1506c.
Proof. vm_refl. Qed.
Lemma D_1506c : decode_any W_1506c = Some (Mul M_MUL 18 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15070 : bv 32 := 0x02b5053b.
Lemma F_15070 : fetch_word Ubsan.M.loaded_segments (0x15174 : word) = Some W_15070.
Proof. vm_refl. Qed.
Lemma D_15070 : decode_any W_15070 = Some (Mul32 M_MUL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15074 : bv 32 := 0x1f251663.
Lemma F_15074 : fetch_word Ubsan.M.loaded_segments (0x15178 : word) = Some W_15074.
Proof. vm_refl. Qed.
Lemma D_15074 : decode_any W_15074 = Some (Branch BC_NE 10 18 492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15078 : bv 32 := 0x08040463.
Lemma F_15078 : fetch_word Ubsan.M.loaded_segments (0x1517c : word) = Some W_15078.
Proof. vm_refl. Qed.
Lemma D_15078 : decode_any W_15078 = Some (Branch BC_EQ 8 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150b4 : bv 32 := 0x00000613.
Lemma F_150b4 : fetch_word Ubsan.M.loaded_segments (0x151b8 : word) = Some W_150b4.
Proof. vm_refl. Qed.
Lemma D_150b4 : decode_any W_150b4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150b8 : bv 32 := 0x02c0006f.
Lemma F_150b8 : fetch_word Ubsan.M.loaded_segments (0x151bc : word) = Some W_150b8.
Proof. vm_refl. Qed.
Lemma D_150b8 : decode_any W_150b8 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150e4 : bv 32 := 0x02813083.
Lemma F_150e4 : fetch_word Ubsan.M.loaded_segments (0x151e8 : word) = Some W_150e4.
Proof. vm_refl. Qed.
Lemma D_150e4 : decode_any W_150e4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150e8 : bv 32 := 0x02013403.
Lemma F_150e8 : fetch_word Ubsan.M.loaded_segments (0x151ec : word) = Some W_150e8.
Proof. vm_refl. Qed.
Lemma D_150e8 : decode_any W_150e8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150ec : bv 32 := 0x01813483.
Lemma F_150ec : fetch_word Ubsan.M.loaded_segments (0x151f0 : word) = Some W_150ec.
Proof. vm_refl. Qed.
Lemma D_150ec : decode_any W_150ec = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150f0 : bv 32 := 0x01013903.
Lemma F_150f0 : fetch_word Ubsan.M.loaded_segments (0x151f4 : word) = Some W_150f0.
Proof. vm_refl. Qed.
Lemma D_150f0 : decode_any W_150f0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150f4 : bv 32 := 0x00813983.
Lemma F_150f4 : fetch_word Ubsan.M.loaded_segments (0x151f8 : word) = Some W_150f4.
Proof. vm_refl. Qed.
Lemma D_150f4 : decode_any W_150f4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150f8 : bv 32 := 0x03010113.
Lemma F_150f8 : fetch_word Ubsan.M.loaded_segments (0x151fc : word) = Some W_150f8.
Proof. vm_refl. Qed.
Lemma D_150f8 : decode_any W_150f8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150fc : bv 32 := 0xd0dfe06f.
Lemma F_150fc : fetch_word Ubsan.M.loaded_segments (0x15200 : word) = Some W_150fc.
Proof. vm_refl. Qed.
Lemma D_150fc : decode_any W_150fc = Some (Jal 0 2092300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15100 : bv 32 := 0x00048513.
Lemma F_15100 : fetch_word Ubsan.M.loaded_segments (0x15204 : word) = Some W_15100.
Proof. vm_refl. Qed.
Lemma D_15100 : decode_any W_15100 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15104 : bv 32 := 0x885ff0ef.
Lemma F_15104 : fetch_word Ubsan.M.loaded_segments (0x15208 : word) = Some W_15104.
Proof. vm_refl. Qed.
Lemma D_15104 : decode_any W_15104 = Some (Jal 1 2095236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15108 : bv 32 := 0x06050463.
Lemma F_15108 : fetch_word Ubsan.M.loaded_segments (0x1520c : word) = Some W_15108.
Proof. vm_refl. Qed.
Lemma D_15108 : decode_any W_15108 = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1510c : bv 32 := 0x00050413.
Lemma F_1510c : fetch_word Ubsan.M.loaded_segments (0x15210 : word) = Some W_1510c.
Proof. vm_refl. Qed.
Lemma D_1510c : decode_any W_1510c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15110 : bv 32 := 0x00757513.
Lemma F_15110 : fetch_word Ubsan.M.loaded_segments (0x15214 : word) = Some W_15110.
Proof. vm_refl. Qed.
Lemma D_15110 : decode_any W_15110 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15114 : bv 32 := 0x14051663.
Lemma F_15114 : fetch_word Ubsan.M.loaded_segments (0x15218 : word) = Some W_15114.
Proof. vm_refl. Qed.
Lemma D_15114 : decode_any W_15114 = Some (Branch BC_NE 10 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15118 : bv 32 := 0x01046503.
Lemma F_15118 : fetch_word Ubsan.M.loaded_segments (0x1521c : word) = Some W_15118.
Proof. vm_refl. Qed.
Lemma D_15118 : decode_any W_15118 = Some (Load SZ4 false 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1511c : bv 32 := 0x00446583.
Lemma F_1511c : fetch_word Ubsan.M.loaded_segments (0x15220 : word) = Some W_1511c.
Proof. vm_refl. Qed.
Lemma D_1511c : decode_any W_1511c = Some (Load SZ4 false 11 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15120 : bv 32 := 0x00251513.
Lemma F_15120 : fetch_word Ubsan.M.loaded_segments (0x15224 : word) = Some W_15120.
Proof. vm_refl. Qed.
Lemma D_15120 : decode_any W_15120 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15124 : bv 32 := 0x02b516b3.
Lemma F_15124 : fetch_word Ubsan.M.loaded_segments (0x15228 : word) = Some W_15124.
Proof. vm_refl. Qed.
Lemma D_15124 : decode_any W_15124 = Some (Mul M_MULH 13 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15128 : bv 32 := 0x02b50633.
Lemma F_15128 : fetch_word Ubsan.M.loaded_segments (0x1522c : word) = Some W_15128.
Proof. vm_refl. Qed.
Lemma D_15128 : decode_any W_15128 = Some (Mul M_MUL 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1512c : bv 32 := 0x43f65513.
Lemma F_1512c : fetch_word Ubsan.M.loaded_segments (0x15230 : word) = Some W_1512c.
Proof. vm_refl. Qed.
Lemma D_1512c : decode_any W_1512c = Some (ShiftImm ALU_SRA 10 12 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15130 : bv 32 := 0x12a69863.
Lemma F_15130 : fetch_word Ubsan.M.loaded_segments (0x15234 : word) = Some W_15130.
Proof. vm_refl. Qed.
Lemma D_15130 : decode_any W_15130 = Some (Branch BC_NE 13 10 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15134 : bv 32 := 0x03843503.
Lemma F_15134 : fetch_word Ubsan.M.loaded_segments (0x15238 : word) = Some W_15134.
Proof. vm_refl. Qed.
Lemma D_15134 : decode_any W_15134 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15138 : bv 32 := 0x00000593.
Lemma F_15138 : fetch_word Ubsan.M.loaded_segments (0x1523c : word) = Some W_15138.
Proof. vm_refl. Qed.
Lemma D_15138 : decode_any W_15138 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1513c : bv 32 := 0x6040a0ef.
Lemma F_1513c : fetch_word Ubsan.M.loaded_segments (0x15240 : word) = Some W_1513c.
Proof. vm_refl. Qed.
Lemma D_1513c : decode_any W_1513c = Some (Jal 1 42500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15140 : bv 32 := 0x00747513.
Lemma F_15140 : fetch_word Ubsan.M.loaded_segments (0x15244 : word) = Some W_15140.
Proof. vm_refl. Qed.
Lemma D_15140 : decode_any W_15140 = Some (OpImm ALU_AND 10 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15144 : bv 32 := 0x0a050c63.
Lemma F_15144 : fetch_word Ubsan.M.loaded_segments (0x15248 : word) = Some W_15144.
Proof. vm_refl. Qed.
Lemma D_15144 : decode_any W_15144 = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15170 : bv 32 := 0x0000c517.
Lemma F_15170 : fetch_word Ubsan.M.loaded_segments (0x15274 : word) = Some W_15170.
Proof. vm_refl. Qed.
Lemma D_15170 : decode_any W_15170 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15174 : bv 32 := 0xbe453983.
Lemma F_15174 : fetch_word Ubsan.M.loaded_segments (0x15278 : word) = Some W_15174.
Proof. vm_refl. Qed.
Lemma D_15174 : decode_any W_15174 = Some (Load SZ8 true 19 10 3044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15178 : bv 32 := 0x0009a503.
Lemma F_15178 : fetch_word Ubsan.M.loaded_segments (0x1527c : word) = Some W_15178.
Proof. vm_refl. Qed.
Lemma D_15178 : decode_any W_15178 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1517c : bv 32 := 0x00600593.
Lemma F_1517c : fetch_word Ubsan.M.loaded_segments (0x15280 : word) = Some W_1517c.
Proof. vm_refl. Qed.
Lemma D_1517c : decode_any W_1517c = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15180 : bv 32 := 0x0ab55e63.
Lemma F_15180 : fetch_word Ubsan.M.loaded_segments (0x15284 : word) = Some W_15180.
Proof. vm_refl. Qed.
Lemma D_15180 : decode_any W_15180 = Some (Branch BC_GE 10 11 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15184 : bv 32 := 0xffffb517.
Lemma F_15184 : fetch_word Ubsan.M.loaded_segments (0x15288 : word) = Some W_15184.
Proof. vm_refl. Qed.
Lemma D_15184 : decode_any W_15184 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15188 : bv 32 := 0xffffb597.
Lemma F_15188 : fetch_word Ubsan.M.loaded_segments (0x1528c : word) = Some W_15188.
Proof. vm_refl. Qed.
Lemma D_15188 : decode_any W_15188 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1518c : bv 32 := 0x1bd50513.
Lemma F_1518c : fetch_word Ubsan.M.loaded_segments (0x15290 : word) = Some W_1518c.
Proof. vm_refl. Qed.
Lemma D_1518c : decode_any W_1518c = Some (OpImm ALU_ADD 10 10 445, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15190 : bv 32 := 0x6f458593.
Lemma F_15190 : fetch_word Ubsan.M.loaded_segments (0x15294 : word) = Some W_15190.
Proof. vm_refl. Qed.
Lemma D_15190 : decode_any W_15190 = Some (OpImm ALU_ADD 11 11 1780, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15194 : bv 32 := 0x00000613.
Lemma F_15194 : fetch_word Ubsan.M.loaded_segments (0x15298 : word) = Some W_15194.
Proof. vm_refl. Qed.
Lemma D_15194 : decode_any W_15194 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15198 : bv 32 := 0xc71fe0ef.
Lemma F_15198 : fetch_word Ubsan.M.loaded_segments (0x1529c : word) = Some W_15198.
Proof. vm_refl. Qed.
Lemma D_15198 : decode_any W_15198 = Some (Jal 1 2092144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1519c : bv 32 := 0x08050063.
Lemma F_1519c : fetch_word Ubsan.M.loaded_segments (0x152a0 : word) = Some W_1519c.
Proof. vm_refl. Qed.
Lemma D_1519c : decode_any W_1519c = Some (Branch BC_EQ 10 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151fc : bv 32 := 0x03843503.
Lemma F_151fc : fetch_word Ubsan.M.loaded_segments (0x15300 : word) = Some W_151fc.
Proof. vm_refl. Qed.
Lemma D_151fc : decode_any W_151fc = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15200 : bv 32 := 0x0384b583.
Lemma F_15200 : fetch_word Ubsan.M.loaded_segments (0x15304 : word) = Some W_15200.
Proof. vm_refl. Qed.
Lemma D_15200 : decode_any W_15200 = Some (Load SZ8 true 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15204 : bv 32 := 0x00b56633.
Lemma F_15204 : fetch_word Ubsan.M.loaded_segments (0x15308 : word) = Some W_15204.
Proof. vm_refl. Qed.
Lemma D_15204 : decode_any W_15204 = Some (Op ALU_OR 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15208 : bv 32 := 0x00367613.
Lemma F_15208 : fetch_word Ubsan.M.loaded_segments (0x1530c : word) = Some W_15208.
Proof. vm_refl. Qed.
Lemma D_15208 : decode_any W_15208 = Some (OpImm ALU_AND 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1520c : bv 32 := 0x04061a63.
Lemma F_1520c : fetch_word Ubsan.M.loaded_segments (0x15310 : word) = Some W_1520c.
Proof. vm_refl. Qed.
Lemma D_1520c : decode_any W_1520c = Some (Branch BC_NE 12 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15210 : bv 32 := 0x0009061b.
Lemma F_15210 : fetch_word Ubsan.M.loaded_segments (0x15314 : word) = Some W_15210.
Proof. vm_refl. Qed.
Lemma D_15210 : decode_any W_15210 = Some (OpImm32 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15214 : bv 32 := 0x1280a0ef.
Lemma F_15214 : fetch_word Ubsan.M.loaded_segments (0x15318 : word) = Some W_15214.
Proof. vm_refl. Qed.
Lemma D_15214 : decode_any W_15214 = Some (Jal 1 41256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15218 : bv 32 := 0x0280006f.
Lemma F_15218 : fetch_word Ubsan.M.loaded_segments (0x1531c : word) = Some W_15218.
Proof. vm_refl. Qed.
Lemma D_15218 : decode_any W_15218 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1521c : bv 32 := 0x0009a503.
Lemma F_1521c : fetch_word Ubsan.M.loaded_segments (0x15320 : word) = Some W_1521c.
Proof. vm_refl. Qed.
Lemma D_1521c : decode_any W_1521c = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15220 : bv 32 := 0x00500593.
Lemma F_15220 : fetch_word Ubsan.M.loaded_segments (0x15324 : word) = Some W_15220.
Proof. vm_refl. Qed.
Lemma D_15220 : decode_any W_15220 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15224 : bv 32 := 0x00a5cc63.
Lemma F_15224 : fetch_word Ubsan.M.loaded_segments (0x15328 : word) = Some W_15224.
Proof. vm_refl. Qed.
Lemma D_15224 : decode_any W_15224 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15228 : bv 32 := 0xffffb517.
Lemma F_15228 : fetch_word Ubsan.M.loaded_segments (0x1532c : word) = Some W_15228.
Proof. vm_refl. Qed.
Lemma D_15228 : decode_any W_15228 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1522c : bv 32 := 0xffffb597.
Lemma F_1522c : fetch_word Ubsan.M.loaded_segments (0x15330 : word) = Some W_1522c.
Proof. vm_refl. Qed.
Lemma D_1522c : decode_any W_1522c = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15230 : bv 32 := 0x11950513.
Lemma F_15230 : fetch_word Ubsan.M.loaded_segments (0x15334 : word) = Some W_15230.
Proof. vm_refl. Qed.
Lemma D_15230 : decode_any W_15230 = Some (OpImm ALU_ADD 10 10 281, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15234 : bv 32 := 0x61358593.
Lemma F_15234 : fetch_word Ubsan.M.loaded_segments (0x15338 : word) = Some W_15234.
Proof. vm_refl. Qed.
Lemma D_15234 : decode_any W_15234 = Some (OpImm ALU_ADD 11 11 1555, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15238 : bv 32 := 0xe7dff06f.
Lemma F_15238 : fetch_word Ubsan.M.loaded_segments (0x1533c : word) = Some W_15238.
Proof. vm_refl. Qed.
Lemma D_15238 : decode_any W_15238 = Some (Jal 0 2096764, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15240 : bv 32 := 0x00040513.
Lemma F_15240 : fetch_word Ubsan.M.loaded_segments (0x15344 : word) = Some W_15240.
Proof. vm_refl. Qed.
Lemma D_15240 : decode_any W_15240 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15244 : bv 32 := 0x02813083.
Lemma F_15244 : fetch_word Ubsan.M.loaded_segments (0x15348 : word) = Some W_15244.
Proof. vm_refl. Qed.
Lemma D_15244 : decode_any W_15244 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15248 : bv 32 := 0x02013403.
Lemma F_15248 : fetch_word Ubsan.M.loaded_segments (0x1534c : word) = Some W_15248.
Proof. vm_refl. Qed.
Lemma D_15248 : decode_any W_15248 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1524c : bv 32 := 0x01813483.
Lemma F_1524c : fetch_word Ubsan.M.loaded_segments (0x15350 : word) = Some W_1524c.
Proof. vm_refl. Qed.
Lemma D_1524c : decode_any W_1524c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15250 : bv 32 := 0x01013903.
Lemma F_15250 : fetch_word Ubsan.M.loaded_segments (0x15354 : word) = Some W_15250.
Proof. vm_refl. Qed.
Lemma D_15250 : decode_any W_15250 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15254 : bv 32 := 0x00813983.
Lemma F_15254 : fetch_word Ubsan.M.loaded_segments (0x15358 : word) = Some W_15254.
Proof. vm_refl. Qed.
Lemma D_15254 : decode_any W_15254 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15258 : bv 32 := 0x03010113.
Lemma F_15258 : fetch_word Ubsan.M.loaded_segments (0x1535c : word) = Some W_15258.
Proof. vm_refl. Qed.
Lemma D_15258 : decode_any W_15258 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1525c : bv 32 := 0x00008067.
Lemma F_1525c : fetch_word Ubsan.M.loaded_segments (0x15360 : word) = Some W_1525c.
Proof. vm_refl. Qed.
Lemma D_1525c : decode_any W_1525c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15550 : bv 32 := 0x00050a63.
Lemma F_15550 : fetch_word Ubsan.M.loaded_segments (0x15654 : word) = Some W_15550.
Proof. vm_refl. Qed.
Lemma D_15550 : decode_any W_15550 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15554 : bv 32 := 0x00757593.
Lemma F_15554 : fetch_word Ubsan.M.loaded_segments (0x15658 : word) = Some W_15554.
Proof. vm_refl. Qed.
Lemma D_15554 : decode_any W_15554 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15558 : bv 32 := 0x04059063.
Lemma F_15558 : fetch_word Ubsan.M.loaded_segments (0x1565c : word) = Some W_15558.
Proof. vm_refl. Qed.
Lemma D_15558 : decode_any W_15558 = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1555c : bv 32 := 0x00852503.
Lemma F_1555c : fetch_word Ubsan.M.loaded_segments (0x15660 : word) = Some W_1555c.
Proof. vm_refl. Qed.
Lemma D_1555c : decode_any W_1555c = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15560 : bv 32 := 0x00008067.
Lemma F_15560 : fetch_word Ubsan.M.loaded_segments (0x15664 : word) = Some W_15560.
Proof. vm_refl. Qed.
Lemma D_15560 : decode_any W_15560 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1559c : bv 32 := 0x00050a63.
Lemma F_1559c : fetch_word Ubsan.M.loaded_segments (0x156a0 : word) = Some W_1559c.
Proof. vm_refl. Qed.
Lemma D_1559c : decode_any W_1559c = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155a0 : bv 32 := 0x00757593.
Lemma F_155a0 : fetch_word Ubsan.M.loaded_segments (0x156a4 : word) = Some W_155a0.
Proof. vm_refl. Qed.
Lemma D_155a0 : decode_any W_155a0 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155a4 : bv 32 := 0x04059063.
Lemma F_155a4 : fetch_word Ubsan.M.loaded_segments (0x156a8 : word) = Some W_155a4.
Proof. vm_refl. Qed.
Lemma D_155a4 : decode_any W_155a4 = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155a8 : bv 32 := 0x03853503.
Lemma F_155a8 : fetch_word Ubsan.M.loaded_segments (0x156ac : word) = Some W_155a8.
Proof. vm_refl. Qed.
Lemma D_155a8 : decode_any W_155a8 = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155ac : bv 32 := 0x00008067.
Lemma F_155ac : fetch_word Ubsan.M.loaded_segments (0x156b0 : word) = Some W_155ac.
Proof. vm_refl. Qed.
Lemma D_155ac : decode_any W_155ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155e8 : bv 32 := 0x00050a63.
Lemma F_155e8 : fetch_word Ubsan.M.loaded_segments (0x156ec : word) = Some W_155e8.
Proof. vm_refl. Qed.
Lemma D_155e8 : decode_any W_155e8 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155ec : bv 32 := 0x00757593.
Lemma F_155ec : fetch_word Ubsan.M.loaded_segments (0x156f0 : word) = Some W_155ec.
Proof. vm_refl. Qed.
Lemma D_155ec : decode_any W_155ec = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155f0 : bv 32 := 0x04059063.
Lemma F_155f0 : fetch_word Ubsan.M.loaded_segments (0x156f4 : word) = Some W_155f0.
Proof. vm_refl. Qed.
Lemma D_155f0 : decode_any W_155f0 = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155f4 : bv 32 := 0x03053503.
Lemma F_155f4 : fetch_word Ubsan.M.loaded_segments (0x156f8 : word) = Some W_155f4.
Proof. vm_refl. Qed.
Lemma D_155f4 : decode_any W_155f4 = Some (Load SZ8 true 10 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155f8 : bv 32 := 0x00008067.
Lemma F_155f8 : fetch_word Ubsan.M.loaded_segments (0x156fc : word) = Some W_155f8.
Proof. vm_refl. Qed.
Lemma D_155f8 : decode_any W_155f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15680 : bv 32 := 0xfd010113.
Lemma F_15680 : fetch_word Ubsan.M.loaded_segments (0x15784 : word) = Some W_15680.
Proof. vm_refl. Qed.
Lemma D_15680 : decode_any W_15680 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15684 : bv 32 := 0x02113423.
Lemma F_15684 : fetch_word Ubsan.M.loaded_segments (0x15788 : word) = Some W_15684.
Proof. vm_refl. Qed.
Lemma D_15684 : decode_any W_15684 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15688 : bv 32 := 0x02813023.
Lemma F_15688 : fetch_word Ubsan.M.loaded_segments (0x1578c : word) = Some W_15688.
Proof. vm_refl. Qed.
Lemma D_15688 : decode_any W_15688 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568c : bv 32 := 0x00913c23.
Lemma F_1568c : fetch_word Ubsan.M.loaded_segments (0x15790 : word) = Some W_1568c.
Proof. vm_refl. Qed.
Lemma D_1568c : decode_any W_1568c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15690 : bv 32 := 0x01213823.
Lemma F_15690 : fetch_word Ubsan.M.loaded_segments (0x15794 : word) = Some W_15690.
Proof. vm_refl. Qed.
Lemma D_15690 : decode_any W_15690 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15694 : bv 32 := 0x06050063.
Lemma F_15694 : fetch_word Ubsan.M.loaded_segments (0x15798 : word) = Some W_15694.
Proof. vm_refl. Qed.
Lemma D_15694 : decode_any W_15694 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15698 : bv 32 := 0x00058413.
Lemma F_15698 : fetch_word Ubsan.M.loaded_segments (0x1579c : word) = Some W_15698.
Proof. vm_refl. Qed.
Lemma D_15698 : decode_any W_15698 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1569c : bv 32 := 0x00050913.
Lemma F_1569c : fetch_word Ubsan.M.loaded_segments (0x157a0 : word) = Some W_1569c.
Proof. vm_refl. Qed.
Lemma D_1569c : decode_any W_1569c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156a0 : bv 32 := 0x00c10593.
Lemma F_156a0 : fetch_word Ubsan.M.loaded_segments (0x157a4 : word) = Some W_156a0.
Proof. vm_refl. Qed.
Lemma D_156a0 : decode_any W_156a0 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156a4 : bv 32 := 0x00810613.
Lemma F_156a4 : fetch_word Ubsan.M.loaded_segments (0x157a8 : word) = Some W_156a4.
Proof. vm_refl. Qed.
Lemma D_156a4 : decode_any W_156a4 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156a8 : bv 32 := 0x00410693.
Lemma F_156a8 : fetch_word Ubsan.M.loaded_segments (0x157ac : word) = Some W_156a8.
Proof. vm_refl. Qed.
Lemma D_156a8 : decode_any W_156a8 = Some (OpImm ALU_ADD 13 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156ac : bv 32 := 0xc38ff0ef.
Lemma F_156ac : fetch_word Ubsan.M.loaded_segments (0x157b0 : word) = Some W_156ac.
Proof. vm_refl. Qed.
Lemma D_156ac : decode_any W_156ac = Some (Jal 1 2094136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156b0 : bv 32 := 0x00412503.
Lemma F_156b0 : fetch_word Ubsan.M.loaded_segments (0x157b4 : word) = Some W_156b0.
Proof. vm_refl. Qed.
Lemma D_156b0 : decode_any W_156b0 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156b4 : bv 32 := 0x02000593.
Lemma F_156b4 : fetch_word Ubsan.M.loaded_segments (0x157b8 : word) = Some W_156b4.
Proof. vm_refl. Qed.
Lemma D_156b4 : decode_any W_156b4 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156b8 : bv 32 := 0x18b50c63.
Lemma F_156b8 : fetch_word Ubsan.M.loaded_segments (0x157bc : word) = Some W_156b8.
Proof. vm_refl. Qed.
Lemma D_156b8 : decode_any W_156b8 = Some (Branch BC_EQ 10 11 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15850 : bv 32 := 0x00000513.
Lemma F_15850 : fetch_word Ubsan.M.loaded_segments (0x15954 : word) = Some W_15850.
Proof. vm_refl. Qed.
Lemma D_15850 : decode_any W_15850 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15854 : bv 32 := 0x02813083.
Lemma F_15854 : fetch_word Ubsan.M.loaded_segments (0x15958 : word) = Some W_15854.
Proof. vm_refl. Qed.
Lemma D_15854 : decode_any W_15854 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15858 : bv 32 := 0x02013403.
Lemma F_15858 : fetch_word Ubsan.M.loaded_segments (0x1595c : word) = Some W_15858.
Proof. vm_refl. Qed.
Lemma D_15858 : decode_any W_15858 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585c : bv 32 := 0x01813483.
Lemma F_1585c : fetch_word Ubsan.M.loaded_segments (0x15960 : word) = Some W_1585c.
Proof. vm_refl. Qed.
Lemma D_1585c : decode_any W_1585c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15860 : bv 32 := 0x01013903.
Lemma F_15860 : fetch_word Ubsan.M.loaded_segments (0x15964 : word) = Some W_15860.
Proof. vm_refl. Qed.
Lemma D_15860 : decode_any W_15860 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15864 : bv 32 := 0x03010113.
Lemma F_15864 : fetch_word Ubsan.M.loaded_segments (0x15968 : word) = Some W_15864.
Proof. vm_refl. Qed.
Lemma D_15864 : decode_any W_15864 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15868 : bv 32 := 0x00008067.
Lemma F_15868 : fetch_word Ubsan.M.loaded_segments (0x1596c : word) = Some W_15868.
Proof. vm_refl. Qed.
Lemma D_15868 : decode_any W_15868 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15870 : bv 32 := 0x06050863.
Lemma F_15870 : fetch_word Ubsan.M.loaded_segments (0x15974 : word) = Some W_15870.
Proof. vm_refl. Qed.
Lemma D_15870 : decode_any W_15870 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15874 : bv 32 := 0x00757713.
Lemma F_15874 : fetch_word Ubsan.M.loaded_segments (0x15978 : word) = Some W_15874.
Proof. vm_refl. Qed.
Lemma D_15874 : decode_any W_15874 = Some (OpImm ALU_AND 14 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15878 : bv 32 := 0x0c071463.
Lemma F_15878 : fetch_word Ubsan.M.loaded_segments (0x1597c : word) = Some W_15878.
Proof. vm_refl. Qed.
Lemma D_15878 : decode_any W_15878 = Some (Branch BC_NE 14 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1587c : bv 32 := 0x00c52783.
Lemma F_1587c : fetch_word Ubsan.M.loaded_segments (0x15980 : word) = Some W_1587c.
Proof. vm_refl. Qed.
Lemma D_1587c : decode_any W_1587c = Some (Load SZ4 true 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15880 : bv 32 := 0x01052703.
Lemma F_15880 : fetch_word Ubsan.M.loaded_segments (0x15984 : word) = Some W_15880.
Proof. vm_refl. Qed.
Lemma D_15880 : decode_any W_15880 = Some (Load SZ4 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15884 : bv 32 := 0x08f75463.
Lemma F_15884 : fetch_word Ubsan.M.loaded_segments (0x15988 : word) = Some W_15884.
Proof. vm_refl. Qed.
Lemma D_15884 : decode_any W_15884 = Some (Branch BC_GE 14 15 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15888 : bv 32 := 0x00053803.
Lemma F_15888 : fetch_word Ubsan.M.loaded_segments (0x1598c : word) = Some W_15888.
Proof. vm_refl. Qed.
Lemma D_15888 : decode_any W_15888 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1588c : bv 32 := 0x00271793.
Lemma F_1588c : fetch_word Ubsan.M.loaded_segments (0x15990 : word) = Some W_1588c.
Proof. vm_refl. Qed.
Lemma D_1588c : decode_any W_1588c = Some (ShiftImm ALU_SLL 15 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15890 : bv 32 := 0x00f807b3.
Lemma F_15890 : fetch_word Ubsan.M.loaded_segments (0x15994 : word) = Some W_15890.
Proof. vm_refl. Qed.
Lemma D_15890 : decode_any W_15890 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15894 : bv 32 := 0x010038b3.
Lemma F_15894 : fetch_word Ubsan.M.loaded_segments (0x15998 : word) = Some W_15894.
Proof. vm_refl. Qed.
Lemma D_15894 : decode_any W_15894 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15898 : bv 32 := 0x0017b293.
Lemma F_15898 : fetch_word Ubsan.M.loaded_segments (0x1599c : word) = Some W_15898.
Proof. vm_refl. Qed.
Lemma D_15898 : decode_any W_15898 = Some (OpImm ALU_SLTU 5 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1589c : bv 32 := 0x0a588263.
Lemma F_1589c : fetch_word Ubsan.M.loaded_segments (0x159a0 : word) = Some W_1589c.
Proof. vm_refl. Qed.
Lemma D_1589c : decode_any W_1589c = Some (Branch BC_EQ 17 5 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158a0 : bv 32 := 0x0107b8b3.
Lemma F_158a0 : fetch_word Ubsan.M.loaded_segments (0x159a4 : word) = Some W_158a0.
Proof. vm_refl. Qed.
Lemma D_158a0 : decode_any W_158a0 = Some (Op ALU_SLTU 17 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158a4 : bv 32 := 0x00072293.
Lemma F_158a4 : fetch_word Ubsan.M.loaded_segments (0x159a8 : word) = Some W_158a4.
Proof. vm_refl. Qed.
Lemma D_158a4 : decode_any W_158a4 = Some (OpImm ALU_SLT 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158a8 : bv 32 := 0x0058c8b3.
Lemma F_158a8 : fetch_word Ubsan.M.loaded_segments (0x159ac : word) = Some W_158a8.
Proof. vm_refl. Qed.
Lemma D_158a8 : decode_any W_158a8 = Some (Op ALU_XOR 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158ac : bv 32 := 0x0018c893.
Lemma F_158ac : fetch_word Ubsan.M.loaded_segments (0x159b0 : word) = Some W_158ac.
Proof. vm_refl. Qed.
Lemma D_158ac : decode_any W_158ac = Some (OpImm ALU_XOR 17 17 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158b0 : bv 32 := 0x08088863.
Lemma F_158b0 : fetch_word Ubsan.M.loaded_segments (0x159b4 : word) = Some W_158b0.
Proof. vm_refl. Qed.
Lemma D_158b0 : decode_any W_158b0 = Some (Branch BC_EQ 17 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158b4 : bv 32 := 0x08080663.
Lemma F_158b4 : fetch_word Ubsan.M.loaded_segments (0x159b8 : word) = Some W_158b4.
Proof. vm_refl. Qed.
Lemma D_158b4 : decode_any W_158b4 = Some (Branch BC_EQ 16 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158b8 : bv 32 := 0x00b78123.
Lemma F_158b8 : fetch_word Ubsan.M.loaded_segments (0x159bc : word) = Some W_158b8.
Proof. vm_refl. Qed.
Lemma D_158b8 : decode_any W_158b8 = Some (Store SZ1 15 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158bc : bv 32 := 0x08078263.
Lemma F_158bc : fetch_word Ubsan.M.loaded_segments (0x159c0 : word) = Some W_158bc.
Proof. vm_refl. Qed.
Lemma D_158bc : decode_any W_158bc = Some (Branch BC_EQ 15 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c0 : bv 32 := 0xfff00813.
Lemma F_158c0 : fetch_word Ubsan.M.loaded_segments (0x159c4 : word) = Some W_158c0.
Proof. vm_refl. Qed.
Lemma D_158c0 : decode_any W_158c0 = Some (OpImm ALU_ADD 16 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c4 : bv 32 := 0x00170713.
Lemma F_158c4 : fetch_word Ubsan.M.loaded_segments (0x159c8 : word) = Some W_158c4.
Proof. vm_refl. Qed.
Lemma D_158c4 : decode_any W_158c4 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c8 : bv 32 := 0x00d78023.
Lemma F_158c8 : fetch_word Ubsan.M.loaded_segments (0x159cc : word) = Some W_158c8.
Proof. vm_refl. Qed.
Lemma D_158c8 : decode_any W_158c8 = Some (Store SZ1 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158cc : bv 32 := 0x00c780a3.
Lemma F_158cc : fetch_word Ubsan.M.loaded_segments (0x159d0 : word) = Some W_158cc.
Proof. vm_refl. Qed.
Lemma D_158cc : decode_any W_158cc = Some (Store SZ1 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d0 : bv 32 := 0x010781a3.
Lemma F_158d0 : fetch_word Ubsan.M.loaded_segments (0x159d4 : word) = Some W_158d0.
Proof. vm_refl. Qed.
Lemma D_158d0 : decode_any W_158d0 = Some (Store SZ1 15 16 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d4 : bv 32 := 0x00e52823.
Lemma F_158d4 : fetch_word Ubsan.M.loaded_segments (0x159d8 : word) = Some W_158d4.
Proof. vm_refl. Qed.
Lemma D_158d4 : decode_any W_158d4 = Some (Store SZ4 10 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d8 : bv 32 := 0x00000513.
Lemma F_158d8 : fetch_word Ubsan.M.loaded_segments (0x159dc : word) = Some W_158d8.
Proof. vm_refl. Qed.
Lemma D_158d8 : decode_any W_158d8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158dc : bv 32 := 0x00008067.
Lemma F_158dc : fetch_word Ubsan.M.loaded_segments (0x159e0 : word) = Some W_158dc.
Proof. vm_refl. Qed.
Lemma D_158dc : decode_any W_158dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1590c : bv 32 := 0x0000b517.
Lemma F_1590c : fetch_word Ubsan.M.loaded_segments (0x15a10 : word) = Some W_1590c.
Proof. vm_refl. Qed.
Lemma D_1590c : decode_any W_1590c = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15910 : bv 32 := 0x44853503.
Lemma F_15910 : fetch_word Ubsan.M.loaded_segments (0x15a14 : word) = Some W_15910.
Proof. vm_refl. Qed.
Lemma D_15910 : decode_any W_15910 = Some (Load SZ8 true 10 10 1096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15914 : bv 32 := 0x00052503.
Lemma F_15914 : fetch_word Ubsan.M.loaded_segments (0x15a18 : word) = Some W_15914.
Proof. vm_refl. Qed.
Lemma D_15914 : decode_any W_15914 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15918 : bv 32 := 0x00500593.
Lemma F_15918 : fetch_word Ubsan.M.loaded_segments (0x15a1c : word) = Some W_15918.
Proof. vm_refl. Qed.
Lemma D_15918 : decode_any W_15918 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1591c : bv 32 := 0x00a5ce63.
Lemma F_1591c : fetch_word Ubsan.M.loaded_segments (0x15a20 : word) = Some W_1591c.
Proof. vm_refl. Qed.
Lemma D_1591c : decode_any W_1591c = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15920 : bv 32 := 0xffffb517.
Lemma F_15920 : fetch_word Ubsan.M.loaded_segments (0x15a24 : word) = Some W_15920.
Proof. vm_refl. Qed.
Lemma D_15920 : decode_any W_15920 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15924 : bv 32 := 0xffffb597.
Lemma F_15924 : fetch_word Ubsan.M.loaded_segments (0x15a28 : word) = Some W_15924.
Proof. vm_refl. Qed.
Lemma D_15924 : decode_any W_15924 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15928 : bv 32 := 0x14550513.
Lemma F_15928 : fetch_word Ubsan.M.loaded_segments (0x15a2c : word) = Some W_15928.
Proof. vm_refl. Qed.
Lemma D_15928 : decode_any W_15928 = Some (OpImm ALU_ADD 10 10 325, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1592c : bv 32 := 0x09358593.
Lemma F_1592c : fetch_word Ubsan.M.loaded_segments (0x15a30 : word) = Some W_1592c.
Proof. vm_refl. Qed.
Lemma D_1592c : decode_any W_1592c = Some (OpImm ALU_ADD 11 11 147, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15930 : bv 32 := 0x00100613.
Lemma F_15930 : fetch_word Ubsan.M.loaded_segments (0x15a34 : word) = Some W_15930.
Proof. vm_refl. Qed.
Lemma D_15930 : decode_any W_15930 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15934 : bv 32 := 0xc04fe06f.
Lemma F_15934 : fetch_word Ubsan.M.loaded_segments (0x15a38 : word) = Some W_15934.
Proof. vm_refl. Qed.
Lemma D_15934 : decode_any W_15934 = Some (Jal 0 2089988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15944 : bv 32 := 0xfe010113.
Lemma F_15944 : fetch_word Ubsan.M.loaded_segments (0x15a48 : word) = Some W_15944.
Proof. vm_refl. Qed.
Lemma D_15944 : decode_any W_15944 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15948 : bv 32 := 0x00113c23.
Lemma F_15948 : fetch_word Ubsan.M.loaded_segments (0x15a4c : word) = Some W_15948.
Proof. vm_refl. Qed.
Lemma D_15948 : decode_any W_15948 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1594c : bv 32 := 0x00813823.
Lemma F_1594c : fetch_word Ubsan.M.loaded_segments (0x15a50 : word) = Some W_1594c.
Proof. vm_refl. Qed.
Lemma D_1594c : decode_any W_1594c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15950 : bv 32 := 0x00913423.
Lemma F_15950 : fetch_word Ubsan.M.loaded_segments (0x15a54 : word) = Some W_15950.
Proof. vm_refl. Qed.
Lemma D_15950 : decode_any W_15950 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15954 : bv 32 := 0x06050c63.
Lemma F_15954 : fetch_word Ubsan.M.loaded_segments (0x15a58 : word) = Some W_15954.
Proof. vm_refl. Qed.
Lemma D_15954 : decode_any W_15954 = Some (Branch BC_EQ 10 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15958 : bv 32 := 0x00050413.
Lemma F_15958 : fetch_word Ubsan.M.loaded_segments (0x15a5c : word) = Some W_15958.
Proof. vm_refl. Qed.
Lemma D_15958 : decode_any W_15958 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595c : bv 32 := 0x00410613.
Lemma F_1595c : fetch_word Ubsan.M.loaded_segments (0x15a60 : word) = Some W_1595c.
Proof. vm_refl. Qed.
Lemma D_1595c : decode_any W_1595c = Some (OpImm ALU_ADD 12 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15960 : bv 32 := 0x00000593.
Lemma F_15960 : fetch_word Ubsan.M.loaded_segments (0x15a64 : word) = Some W_15960.
Proof. vm_refl. Qed.
Lemma D_15960 : decode_any W_15960 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15964 : bv 32 := 0x0f8000ef.
Lemma F_15964 : fetch_word Ubsan.M.loaded_segments (0x15a68 : word) = Some W_15964.
Proof. vm_refl. Qed.
Lemma D_15964 : decode_any W_15964 = Some (Jal 1 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15968 : bv 32 := 0x00412503.
Lemma F_15968 : fetch_word Ubsan.M.loaded_segments (0x15a6c : word) = Some W_15968.
Proof. vm_refl. Qed.
Lemma D_15968 : decode_any W_15968 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1596c : bv 32 := 0x08050e63.
Lemma F_1596c : fetch_word Ubsan.M.loaded_segments (0x15a70 : word) = Some W_1596c.
Proof. vm_refl. Qed.
Lemma D_1596c : decode_any W_1596c = Some (Branch BC_EQ 10 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15970 : bv 32 := 0x00100513.
Lemma F_15970 : fetch_word Ubsan.M.loaded_segments (0x15a74 : word) = Some W_15970.
Proof. vm_refl. Qed.
Lemma D_15970 : decode_any W_15970 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15974 : bv 32 := 0x01800593.
Lemma F_15974 : fetch_word Ubsan.M.loaded_segments (0x15a78 : word) = Some W_15974.
Proof. vm_refl. Qed.
Lemma D_15974 : decode_any W_15974 = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15978 : bv 32 := 0x758020ef.
Lemma F_15978 : fetch_word Ubsan.M.loaded_segments (0x15a7c : word) = Some W_15978.
Proof. vm_refl. Qed.
Lemma D_15978 : decode_any W_15978 = Some (Jal 1 10072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1597c : bv 32 := 0x00747593.
Lemma F_1597c : fetch_word Ubsan.M.loaded_segments (0x15a80 : word) = Some W_1597c.
Proof. vm_refl. Qed.
Lemma D_1597c : decode_any W_1597c = Some (OpImm ALU_AND 11 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15980 : bv 32 := 0x0c059c63.
Lemma F_15980 : fetch_word Ubsan.M.loaded_segments (0x15a84 : word) = Some W_15980.
Proof. vm_refl. Qed.
Lemma D_15980 : decode_any W_15980 = Some (Branch BC_NE 11 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15984 : bv 32 := 0x00050493.
Lemma F_15984 : fetch_word Ubsan.M.loaded_segments (0x15a88 : word) = Some W_15984.
Proof. vm_refl. Qed.
Lemma D_15984 : decode_any W_15984 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15988 : bv 32 := 0x00c42503.
Lemma F_15988 : fetch_word Ubsan.M.loaded_segments (0x15a8c : word) = Some W_15988.
Proof. vm_refl. Qed.
Lemma D_15988 : decode_any W_15988 = Some (Load SZ4 true 10 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1598c : bv 32 := 0x0025159b.
Lemma F_1598c : fetch_word Ubsan.M.loaded_segments (0x15a90 : word) = Some W_1598c.
Proof. vm_refl. Qed.
Lemma D_1598c : decode_any W_1598c = Some (ShiftImm32 ALU_SLL 11 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15990 : bv 32 := 0x00100513.
Lemma F_15990 : fetch_word Ubsan.M.loaded_segments (0x15a94 : word) = Some W_15990.
Proof. vm_refl. Qed.
Lemma D_15990 : decode_any W_15990 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15994 : bv 32 := 0x73c020ef.
Lemma F_15994 : fetch_word Ubsan.M.loaded_segments (0x15a98 : word) = Some W_15994.
Proof. vm_refl. Qed.
Lemma D_15994 : decode_any W_15994 = Some (Jal 1 10044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15998 : bv 32 := 0x0c048063.
Lemma F_15998 : fetch_word Ubsan.M.loaded_segments (0x15a9c : word) = Some W_15998.
Proof. vm_refl. Qed.
Lemma D_15998 : decode_any W_15998 = Some (Branch BC_EQ 9 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1599c : bv 32 := 0x0074f593.
Lemma F_1599c : fetch_word Ubsan.M.loaded_segments (0x15aa0 : word) = Some W_1599c.
Proof. vm_refl. Qed.
Lemma D_1599c : decode_any W_1599c = Some (OpImm ALU_AND 11 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159a0 : bv 32 := 0x0a059c63.
Lemma F_159a0 : fetch_word Ubsan.M.loaded_segments (0x15aa4 : word) = Some W_159a0.
Proof. vm_refl. Qed.
Lemma D_159a0 : decode_any W_159a0 = Some (Branch BC_NE 11 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159a4 : bv 32 := 0x00a4b023.
Lemma F_159a4 : fetch_word Ubsan.M.loaded_segments (0x15aa8 : word) = Some W_159a4.
Proof. vm_refl. Qed.
Lemma D_159a4 : decode_any W_159a4 = Some (Store SZ8 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159a8 : bv 32 := 0x01042603.
Lemma F_159a8 : fetch_word Ubsan.M.loaded_segments (0x15aac : word) = Some W_159a8.
Proof. vm_refl. Qed.
Lemma D_159a8 : decode_any W_159a8 = Some (Load SZ4 true 12 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159ac : bv 32 := 0x00043583.
Lemma F_159ac : fetch_word Ubsan.M.loaded_segments (0x15ab0 : word) = Some W_159ac.
Proof. vm_refl. Qed.
Lemma D_159ac : decode_any W_159ac = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159b0 : bv 32 := 0x00261613.
Lemma F_159b0 : fetch_word Ubsan.M.loaded_segments (0x15ab4 : word) = Some W_159b0.
Proof. vm_refl. Qed.
Lemma D_159b0 : decode_any W_159b0 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159b4 : bv 32 := 0x189090ef.
Lemma F_159b4 : fetch_word Ubsan.M.loaded_segments (0x15ab8 : word) = Some W_159b4.
Proof. vm_refl. Qed.
Lemma D_159b4 : decode_any W_159b4 = Some (Jal 1 39304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159b8 : bv 32 := 0x01042503.
Lemma F_159b8 : fetch_word Ubsan.M.loaded_segments (0x15abc : word) = Some W_159b8.
Proof. vm_refl. Qed.
Lemma D_159b8 : decode_any W_159b8 = Some (Load SZ4 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159bc : bv 32 := 0x00a4a823.
Lemma F_159bc : fetch_word Ubsan.M.loaded_segments (0x15ac0 : word) = Some W_159bc.
Proof. vm_refl. Qed.
Lemma D_159bc : decode_any W_159bc = Some (Store SZ4 9 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159c0 : bv 32 := 0x00843503.
Lemma F_159c0 : fetch_word Ubsan.M.loaded_segments (0x15ac4 : word) = Some W_159c0.
Proof. vm_refl. Qed.
Lemma D_159c0 : decode_any W_159c0 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159c4 : bv 32 := 0x00a4b423.
Lemma F_159c4 : fetch_word Ubsan.M.loaded_segments (0x15ac8 : word) = Some W_159c4.
Proof. vm_refl. Qed.
Lemma D_159c4 : decode_any W_159c4 = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159c8 : bv 32 := 0x0780006f.
Lemma F_159c8 : fetch_word Ubsan.M.loaded_segments (0x15acc : word) = Some W_159c8.
Proof. vm_refl. Qed.
Lemma D_159c8 : decode_any W_159c8 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a40 : bv 32 := 0x00048513.
Lemma F_15a40 : fetch_word Ubsan.M.loaded_segments (0x15b44 : word) = Some W_15a40.
Proof. vm_refl. Qed.
Lemma D_15a40 : decode_any W_15a40 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a44 : bv 32 := 0x01813083.
Lemma F_15a44 : fetch_word Ubsan.M.loaded_segments (0x15b48 : word) = Some W_15a44.
Proof. vm_refl. Qed.
Lemma D_15a44 : decode_any W_15a44 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a48 : bv 32 := 0x01013403.
Lemma F_15a48 : fetch_word Ubsan.M.loaded_segments (0x15b4c : word) = Some W_15a48.
Proof. vm_refl. Qed.
Lemma D_15a48 : decode_any W_15a48 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a4c : bv 32 := 0x00813483.
Lemma F_15a4c : fetch_word Ubsan.M.loaded_segments (0x15b50 : word) = Some W_15a4c.
Proof. vm_refl. Qed.
Lemma D_15a4c : decode_any W_15a4c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a50 : bv 32 := 0x02010113.
Lemma F_15a50 : fetch_word Ubsan.M.loaded_segments (0x15b54 : word) = Some W_15a50.
Proof. vm_refl. Qed.
Lemma D_15a50 : decode_any W_15a50 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a54 : bv 32 := 0x00008067.
Lemma F_15a54 : fetch_word Ubsan.M.loaded_segments (0x15b58 : word) = Some W_15a54.
Proof. vm_refl. Qed.
Lemma D_15a54 : decode_any W_15a54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e0c : bv 32 := 0x08070863.
Lemma F_15e0c : fetch_word Ubsan.M.loaded_segments (0x15f10 : word) = Some W_15e0c.
Proof. vm_refl. Qed.
Lemma D_15e0c : decode_any W_15e0c = Some (Branch BC_EQ 14 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e10 : bv 32 := 0x00377793.
Lemma F_15e10 : fetch_word Ubsan.M.loaded_segments (0x15f14 : word) = Some W_15e10.
Proof. vm_refl. Qed.
Lemma D_15e10 : decode_any W_15e10 = Some (OpImm ALU_AND 15 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e14 : bv 32 := 0x0e079663.
Lemma F_15e14 : fetch_word Ubsan.M.loaded_segments (0x15f18 : word) = Some W_15e14.
Proof. vm_refl. Qed.
Lemma D_15e14 : decode_any W_15e14 = Some (Branch BC_NE 15 0 236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e18 : bv 32 := 0x00072023.
Lemma F_15e18 : fetch_word Ubsan.M.loaded_segments (0x15f1c : word) = Some W_15e18.
Proof. vm_refl. Qed.
Lemma D_15e18 : decode_any W_15e18 = Some (Store SZ4 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e1c : bv 32 := 0x0a050863.
Lemma F_15e1c : fetch_word Ubsan.M.loaded_segments (0x15f20 : word) = Some W_15e1c.
Proof. vm_refl. Qed.
Lemma D_15e1c : decode_any W_15e1c = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e20 : bv 32 := 0x00757793.
Lemma F_15e20 : fetch_word Ubsan.M.loaded_segments (0x15f24 : word) = Some W_15e20.
Proof. vm_refl. Qed.
Lemma D_15e20 : decode_any W_15e20 = Some (OpImm ALU_AND 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e24 : bv 32 := 0x0c079e63.
Lemma F_15e24 : fetch_word Ubsan.M.loaded_segments (0x15f28 : word) = Some W_15e24.
Proof. vm_refl. Qed.
Lemma D_15e24 : decode_any W_15e24 = Some (Branch BC_NE 15 0 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e28 : bv 32 := 0x00050893.
Lemma F_15e28 : fetch_word Ubsan.M.loaded_segments (0x15f2c : word) = Some W_15e28.
Proof. vm_refl. Qed.
Lemma D_15e28 : decode_any W_15e28 = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e2c : bv 32 := 0x01052783.
Lemma F_15e2c : fetch_word Ubsan.M.loaded_segments (0x15f30 : word) = Some W_15e2c.
Proof. vm_refl. Qed.
Lemma D_15e2c : decode_any W_15e2c = Some (Load SZ4 true 15 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e30 : bv 32 := 0x00100513.
Lemma F_15e30 : fetch_word Ubsan.M.loaded_segments (0x15f34 : word) = Some W_15e30.
Proof. vm_refl. Qed.
Lemma D_15e30 : decode_any W_15e30 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e34 : bv 32 := 0x08f05a63.
Lemma F_15e34 : fetch_word Ubsan.M.loaded_segments (0x15f38 : word) = Some W_15e34.
Proof. vm_refl. Qed.
Lemma D_15e34 : decode_any W_15e34 = Some (Branch BC_GE 0 15 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e38 : bv 32 := 0x00000813.
Lemma F_15e38 : fetch_word Ubsan.M.loaded_segments (0x15f3c : word) = Some W_15e38.
Proof. vm_refl. Qed.
Lemma D_15e38 : decode_any W_15e38 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e3c : bv 32 := 0x0008b883.
Lemma F_15e3c : fetch_word Ubsan.M.loaded_segments (0x15f40 : word) = Some W_15e3c.
Proof. vm_refl. Qed.
Lemma D_15e3c : decode_any W_15e3c = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e40 : bv 32 := 0x00188293.
Lemma F_15e40 : fetch_word Ubsan.M.loaded_segments (0x15f44 : word) = Some W_15e40.
Proof. vm_refl. Qed.
Lemma D_15e40 : decode_any W_15e40 = Some (OpImm ALU_ADD 5 17 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e44 : bv 32 := 0x01103333.
Lemma F_15e44 : fetch_word Ubsan.M.loaded_segments (0x15f48 : word) = Some W_15e44.
Proof. vm_refl. Qed.
Lemma D_15e44 : decode_any W_15e44 = Some (Op ALU_SLTU 6 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e48 : bv 32 := 0x00088393.
Lemma F_15e48 : fetch_word Ubsan.M.loaded_segments (0x15f4c : word) = Some W_15e48.
Proof. vm_refl. Qed.
Lemma D_15e48 : decode_any W_15e48 = Some (OpImm ALU_ADD 7 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e4c : bv 32 := 0x0180006f.
Lemma F_15e4c : fetch_word Ubsan.M.loaded_segments (0x15f50 : word) = Some W_15e4c.
Proof. vm_refl. Qed.
Lemma D_15e4c : decode_any W_15e4c = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e50 : bv 32 := 0x00180813.
Lemma F_15e50 : fetch_word Ubsan.M.loaded_segments (0x15f54 : word) = Some W_15e50.
Proof. vm_refl. Qed.
Lemma D_15e50 : decode_any W_15e50 = Some (OpImm ALU_ADD 16 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e54 : bv 32 := 0x00438393.
Lemma F_15e54 : fetch_word Ubsan.M.loaded_segments (0x15f58 : word) = Some W_15e54.
Proof. vm_refl. Qed.
Lemma D_15e54 : decode_any W_15e54 = Some (OpImm ALU_ADD 7 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e58 : bv 32 := 0xfff78793.
Lemma F_15e58 : fetch_word Ubsan.M.loaded_segments (0x15f5c : word) = Some W_15e58.
Proof. vm_refl. Qed.
Lemma D_15e58 : decode_any W_15e58 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e5c : bv 32 := 0x00428293.
Lemma F_15e5c : fetch_word Ubsan.M.loaded_segments (0x15f60 : word) = Some W_15e5c.
Proof. vm_refl. Qed.
Lemma D_15e5c : decode_any W_15e5c = Some (OpImm ALU_ADD 5 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e60 : bv 32 := 0x06078463.
Lemma F_15e60 : fetch_word Ubsan.M.loaded_segments (0x15f64 : word) = Some W_15e60.
Proof. vm_refl. Qed.
Lemma D_15e60 : decode_any W_15e60 = Some (Branch BC_EQ 15 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e64 : bv 32 := 0x0913ee63.
Lemma F_15e64 : fetch_word Ubsan.M.loaded_segments (0x15f68 : word) = Some W_15e64.
Proof. vm_refl. Qed.
Lemma D_15e64 : decode_any W_15e64 = Some (Branch BC_LTU 7 17 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e68 : bv 32 := 0x0013be13.
Lemma F_15e68 : fetch_word Ubsan.M.loaded_segments (0x15f6c : word) = Some W_15e68.
Proof. vm_refl. Qed.
Lemma D_15e68 : decode_any W_15e68 = Some (OpImm ALU_SLTU 28 7 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e6c : bv 32 := 0x01c34e33.
Lemma F_15e6c : fetch_word Ubsan.M.loaded_segments (0x15f70 : word) = Some W_15e6c.
Proof. vm_refl. Qed.
Lemma D_15e6c : decode_any W_15e6c = Some (Op ALU_XOR 28 6 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e70 : bv 32 := 0x080e0863.
Lemma F_15e70 : fetch_word Ubsan.M.loaded_segments (0x15f74 : word) = Some W_15e70.
Proof. vm_refl. Qed.
Lemma D_15e70 : decode_any W_15e70 = Some (Branch BC_EQ 28 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e74 : bv 32 := 0x08088663.
Lemma F_15e74 : fetch_word Ubsan.M.loaded_segments (0x15f78 : word) = Some W_15e74.
Proof. vm_refl. Qed.
Lemma D_15e74 : decode_any W_15e74 = Some (Branch BC_EQ 17 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e78 : bv 32 := 0x0012ce03.
Lemma F_15e78 : fetch_word Ubsan.M.loaded_segments (0x15f7c : word) = Some W_15e78.
Proof. vm_refl. Qed.
Lemma D_15e78 : decode_any W_15e78 = Some (Load SZ1 false 28 5 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e7c : bv 32 := 0xfdc59ae3.
Lemma F_15e7c : fetch_word Ubsan.M.loaded_segments (0x15f80 : word) = Some W_15e7c.
Proof. vm_refl. Qed.
Lemma D_15e7c : decode_any W_15e7c = Some (Branch BC_NE 11 28 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e80 : bv 32 := 0x0002ce03.
Lemma F_15e80 : fetch_word Ubsan.M.loaded_segments (0x15f84 : word) = Some W_15e80.
Proof. vm_refl. Qed.
Lemma D_15e80 : decode_any W_15e80 = Some (Load SZ1 false 28 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e84 : bv 32 := 0xfdc616e3.
Lemma F_15e84 : fetch_word Ubsan.M.loaded_segments (0x15f88 : word) = Some W_15e84.
Proof. vm_refl. Qed.
Lemma D_15e84 : decode_any W_15e84 = Some (Branch BC_NE 12 28 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e88 : bv 32 := 0xfff2ce03.
Lemma F_15e88 : fetch_word Ubsan.M.loaded_segments (0x15f8c : word) = Some W_15e88.
Proof. vm_refl. Qed.
Lemma D_15e88 : decode_any W_15e88 = Some (Load SZ1 false 28 5 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e8c : bv 32 := 0xfdc692e3.
Lemma F_15e8c : fetch_word Ubsan.M.loaded_segments (0x15f90 : word) = Some W_15e8c.
Proof. vm_refl. Qed.
Lemma D_15e8c : decode_any W_15e8c = Some (Branch BC_NE 13 28 8132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e90 : bv 32 := 0x00000513.
Lemma F_15e90 : fetch_word Ubsan.M.loaded_segments (0x15f94 : word) = Some W_15e90.
Proof. vm_refl. Qed.
Lemma D_15e90 : decode_any W_15e90 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e94 : bv 32 := 0x01072023.
Lemma F_15e94 : fetch_word Ubsan.M.loaded_segments (0x15f98 : word) = Some W_15e94.
Proof. vm_refl. Qed.
Lemma D_15e94 : decode_any W_15e94 = Some (Store SZ4 14 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e98 : bv 32 := 0x00008067.
Lemma F_15e98 : fetch_word Ubsan.M.loaded_segments (0x15f9c : word) = Some W_15e98.
Proof. vm_refl. Qed.
Lemma D_15e98 : decode_any W_15e98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ec8 : bv 32 := 0x00008067.
Lemma F_15ec8 : fetch_word Ubsan.M.loaded_segments (0x15fcc : word) = Some W_15ec8.
Proof. vm_refl. Qed.
Lemma D_15ec8 : decode_any W_15ec8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f04 : bv 32 := 0x00050a63.
Lemma F_15f04 : fetch_word Ubsan.M.loaded_segments (0x16008 : word) = Some W_15f04.
Proof. vm_refl. Qed.
Lemma D_15f04 : decode_any W_15f04 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f08 : bv 32 := 0x00757593.
Lemma F_15f08 : fetch_word Ubsan.M.loaded_segments (0x1600c : word) = Some W_15f08.
Proof. vm_refl. Qed.
Lemma D_15f08 : decode_any W_15f08 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f0c : bv 32 := 0x04059063.
Lemma F_15f0c : fetch_word Ubsan.M.loaded_segments (0x16010 : word) = Some W_15f0c.
Proof. vm_refl. Qed.
Lemma D_15f0c : decode_any W_15f0c = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f10 : bv 32 := 0x01052503.
Lemma F_15f10 : fetch_word Ubsan.M.loaded_segments (0x16014 : word) = Some W_15f10.
Proof. vm_refl. Qed.
Lemma D_15f10 : decode_any W_15f10 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f14 : bv 32 := 0x00008067.
Lemma F_15f14 : fetch_word Ubsan.M.loaded_segments (0x16018 : word) = Some W_15f14.
Proof. vm_refl. Qed.
Lemma D_15f14 : decode_any W_15f14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
