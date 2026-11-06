(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.H Require GcFlushS15.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_17270 : bv 32 := 0xfd010113.
Lemma F_17270 : fetch_word Plain.M.loaded_segments (0x172c8 : word) = Some W_17270.
Proof. vm_refl. Qed.
Lemma D_17270 : decode_any W_17270 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17274 : bv 32 := 0x02113423.
Lemma F_17274 : fetch_word Plain.M.loaded_segments (0x172cc : word) = Some W_17274.
Proof. vm_refl. Qed.
Lemma D_17274 : decode_any W_17274 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17278 : bv 32 := 0x02813023.
Lemma F_17278 : fetch_word Plain.M.loaded_segments (0x172d0 : word) = Some W_17278.
Proof. vm_refl. Qed.
Lemma D_17278 : decode_any W_17278 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1727c : bv 32 := 0x00913c23.
Lemma F_1727c : fetch_word Plain.M.loaded_segments (0x172d4 : word) = Some W_1727c.
Proof. vm_refl. Qed.
Lemma D_1727c : decode_any W_1727c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17280 : bv 32 := 0x01213823.
Lemma F_17280 : fetch_word Plain.M.loaded_segments (0x172d8 : word) = Some W_17280.
Proof. vm_refl. Qed.
Lemma D_17280 : decode_any W_17280 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17284 : bv 32 := 0x01313423.
Lemma F_17284 : fetch_word Plain.M.loaded_segments (0x172dc : word) = Some W_17284.
Proof. vm_refl. Qed.
Lemma D_17284 : decode_any W_17284 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17288 : bv 32 := 0x00050413.
Lemma F_17288 : fetch_word Plain.M.loaded_segments (0x172e0 : word) = Some W_17288.
Proof. vm_refl. Qed.
Lemma D_17288 : decode_any W_17288 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1728c : bv 32 := 0x06058063.
Lemma F_1728c : fetch_word Plain.M.loaded_segments (0x172e4 : word) = Some W_1728c.
Proof. vm_refl. Qed.
Lemma D_1728c : decode_any W_1728c = Some (Branch BC_EQ 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17290 : bv 32 := 0x00058493.
Lemma F_17290 : fetch_word Plain.M.loaded_segments (0x172e8 : word) = Some W_17290.
Proof. vm_refl. Qed.
Lemma D_17290 : decode_any W_17290 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17294 : bv 32 := 0x18858e63.
Lemma F_17294 : fetch_word Plain.M.loaded_segments (0x172ec : word) = Some W_17294.
Proof. vm_refl. Qed.
Lemma D_17294 : decode_any W_17294 = Some (Branch BC_EQ 11 8 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17298 : bv 32 := 0x0044a503.
Lemma F_17298 : fetch_word Plain.M.loaded_segments (0x172f0 : word) = Some W_17298.
Proof. vm_refl. Qed.
Lemma D_17298 : decode_any W_17298 = Some (Load SZ4 true 10 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1729c : bv 32 := 0x0104a583.
Lemma F_1729c : fetch_word Plain.M.loaded_segments (0x172f4 : word) = Some W_1729c.
Proof. vm_refl. Qed.
Lemma D_1729c : decode_any W_1729c = Some (Load SZ4 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_172a0 : bv 32 := 0x02a58533.
Lemma F_172a0 : fetch_word Plain.M.loaded_segments (0x172f8 : word) = Some W_172a0.
Proof. vm_refl. Qed.
Lemma D_172a0 : decode_any W_172a0 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_172a4 : bv 32 := 0x0025191b.
Lemma F_172a4 : fetch_word Plain.M.loaded_segments (0x172fc : word) = Some W_172a4.
Proof. vm_refl. Qed.
Lemma D_172a4 : decode_any W_172a4 = Some (ShiftImm32 ALU_SLL 18 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_172a8 : bv 32 := 0x08040463.
Lemma F_172a8 : fetch_word Plain.M.loaded_segments (0x17300 : word) = Some W_172a8.
Proof. vm_refl. Qed.
Lemma D_172a8 : decode_any W_172a8 = Some (Branch BC_EQ 8 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_172e4 : bv 32 := 0x00000613.
Lemma F_172e4 : fetch_word Plain.M.loaded_segments (0x1733c : word) = Some W_172e4.
Proof. vm_refl. Qed.
Lemma D_172e4 : decode_any W_172e4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_172e8 : bv 32 := 0x02c0006f.
Lemma F_172e8 : fetch_word Plain.M.loaded_segments (0x17340 : word) = Some W_172e8.
Proof. vm_refl. Qed.
Lemma D_172e8 : decode_any W_172e8 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17314 : bv 32 := 0x02813083.
Lemma F_17314 : fetch_word Plain.M.loaded_segments (0x1736c : word) = Some W_17314.
Proof. vm_refl. Qed.
Lemma D_17314 : decode_any W_17314 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17318 : bv 32 := 0x02013403.
Lemma F_17318 : fetch_word Plain.M.loaded_segments (0x17370 : word) = Some W_17318.
Proof. vm_refl. Qed.
Lemma D_17318 : decode_any W_17318 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1731c : bv 32 := 0x01813483.
Lemma F_1731c : fetch_word Plain.M.loaded_segments (0x17374 : word) = Some W_1731c.
Proof. vm_refl. Qed.
Lemma D_1731c : decode_any W_1731c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17320 : bv 32 := 0x01013903.
Lemma F_17320 : fetch_word Plain.M.loaded_segments (0x17378 : word) = Some W_17320.
Proof. vm_refl. Qed.
Lemma D_17320 : decode_any W_17320 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17324 : bv 32 := 0x00813983.
Lemma F_17324 : fetch_word Plain.M.loaded_segments (0x1737c : word) = Some W_17324.
Proof. vm_refl. Qed.
Lemma D_17324 : decode_any W_17324 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17328 : bv 32 := 0x03010113.
Lemma F_17328 : fetch_word Plain.M.loaded_segments (0x17380 : word) = Some W_17328.
Proof. vm_refl. Qed.
Lemma D_17328 : decode_any W_17328 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1732c : bv 32 := 0x8f4fe06f.
Lemma F_1732c : fetch_word Plain.M.loaded_segments (0x17384 : word) = Some W_1732c.
Proof. vm_refl. Qed.
Lemma D_1732c : decode_any W_1732c = Some (Jal 0 2089204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17330 : bv 32 := 0x00048513.
Lemma F_17330 : fetch_word Plain.M.loaded_segments (0x17388 : word) = Some W_17330.
Proof. vm_refl. Qed.
Lemma D_17330 : decode_any W_17330 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17334 : bv 32 := 0x8e5ff0ef.
Lemma F_17334 : fetch_word Plain.M.loaded_segments (0x1738c : word) = Some W_17334.
Proof. vm_refl. Qed.
Lemma D_17334 : decode_any W_17334 = Some (Jal 1 2095332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17338 : bv 32 := 0x04050263.
Lemma F_17338 : fetch_word Plain.M.loaded_segments (0x17390 : word) = Some W_17338.
Proof. vm_refl. Qed.
Lemma D_17338 : decode_any W_17338 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1733c : bv 32 := 0x00050413.
Lemma F_1733c : fetch_word Plain.M.loaded_segments (0x17394 : word) = Some W_1733c.
Proof. vm_refl. Qed.
Lemma D_1733c : decode_any W_1733c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17340 : bv 32 := 0x00456583.
Lemma F_17340 : fetch_word Plain.M.loaded_segments (0x17398 : word) = Some W_17340.
Proof. vm_refl. Qed.
Lemma D_17340 : decode_any W_17340 = Some (Load SZ4 false 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17344 : bv 32 := 0x01056603.
Lemma F_17344 : fetch_word Plain.M.loaded_segments (0x1739c : word) = Some W_17344.
Proof. vm_refl. Qed.
Lemma D_17344 : decode_any W_17344 = Some (Load SZ4 false 12 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17348 : bv 32 := 0x03853503.
Lemma F_17348 : fetch_word Plain.M.loaded_segments (0x173a0 : word) = Some W_17348.
Proof. vm_refl. Qed.
Lemma D_17348 : decode_any W_17348 = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1734c : bv 32 := 0x02b60633.
Lemma F_1734c : fetch_word Plain.M.loaded_segments (0x173a4 : word) = Some W_1734c.
Proof. vm_refl. Qed.
Lemma D_1734c : decode_any W_1734c = Some (Mul M_MUL 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17350 : bv 32 := 0x00261613.
Lemma F_17350 : fetch_word Plain.M.loaded_segments (0x173a8 : word) = Some W_17350.
Proof. vm_refl. Qed.
Lemma D_17350 : decode_any W_17350 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17354 : bv 32 := 0x00000593.
Lemma F_17354 : fetch_word Plain.M.loaded_segments (0x173ac : word) = Some W_17354.
Proof. vm_refl. Qed.
Lemma D_17354 : decode_any W_17354 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17358 : bv 32 := 0x49d130ef.
Lemma F_17358 : fetch_word Plain.M.loaded_segments (0x173b0 : word) = Some W_17358.
Proof. vm_refl. Qed.
Lemma D_17358 : decode_any W_17358 = Some (Jal 1 81052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1735c : bv 32 := 0x0c40006f.
Lemma F_1735c : fetch_word Plain.M.loaded_segments (0x173b4 : word) = Some W_1735c.
Proof. vm_refl. Qed.
Lemma D_1735c : decode_any W_1735c = Some (Jal 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1737c : bv 32 := 0x00015517.
Lemma F_1737c : fetch_word Plain.M.loaded_segments (0x173d4 : word) = Some W_1737c.
Proof. vm_refl. Qed.
Lemma D_1737c : decode_any W_1737c = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17380 : bv 32 := 0x3ac53983.
Lemma F_17380 : fetch_word Plain.M.loaded_segments (0x173d8 : word) = Some W_17380.
Proof. vm_refl. Qed.
Lemma D_17380 : decode_any W_17380 = Some (Load SZ8 true 19 10 940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17384 : bv 32 := 0x0009a503.
Lemma F_17384 : fetch_word Plain.M.loaded_segments (0x173dc : word) = Some W_17384.
Proof. vm_refl. Qed.
Lemma D_17384 : decode_any W_17384 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17388 : bv 32 := 0x00600593.
Lemma F_17388 : fetch_word Plain.M.loaded_segments (0x173e0 : word) = Some W_17388.
Proof. vm_refl. Qed.
Lemma D_17388 : decode_any W_17388 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1738c : bv 32 := 0x04b55263.
Lemma F_1738c : fetch_word Plain.M.loaded_segments (0x173e4 : word) = Some W_1738c.
Proof. vm_refl. Qed.
Lemma D_1738c : decode_any W_1738c = Some (Branch BC_GE 10 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17390 : bv 32 := 0xffff9517.
Lemma F_17390 : fetch_word Plain.M.loaded_segments (0x173e8 : word) = Some W_17390.
Proof. vm_refl. Qed.
Lemma D_17390 : decode_any W_17390 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17394 : bv 32 := 0xffffa597.
Lemma F_17394 : fetch_word Plain.M.loaded_segments (0x173ec : word) = Some W_17394.
Proof. vm_refl. Qed.
Lemma D_17394 : decode_any W_17394 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17398 : bv 32 := 0x13750513.
Lemma F_17398 : fetch_word Plain.M.loaded_segments (0x173f0 : word) = Some W_17398.
Proof. vm_refl. Qed.
Lemma D_17398 : decode_any W_17398 = Some (OpImm ALU_ADD 10 10 311, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1739c : bv 32 := 0xa1d58593.
Lemma F_1739c : fetch_word Plain.M.loaded_segments (0x173f4 : word) = Some W_1739c.
Proof. vm_refl. Qed.
Lemma D_1739c : decode_any W_1739c = Some (OpImm ALU_ADD 11 11 2589, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173a0 : bv 32 := 0x00000613.
Lemma F_173a0 : fetch_word Plain.M.loaded_segments (0x173f8 : word) = Some W_173a0.
Proof. vm_refl. Qed.
Lemma D_173a0 : decode_any W_173a0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173a4 : bv 32 := 0x87cfe0ef.
Lemma F_173a4 : fetch_word Plain.M.loaded_segments (0x173fc : word) = Some W_173a4.
Proof. vm_refl. Qed.
Lemma D_173a4 : decode_any W_173a4 = Some (Jal 1 2089084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173a8 : bv 32 := 0x00050413.
Lemma F_173a8 : fetch_word Plain.M.loaded_segments (0x17400 : word) = Some W_173a8.
Proof. vm_refl. Qed.
Lemma D_173a8 : decode_any W_173a8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173ac : bv 32 := 0x06051a63.
Lemma F_173ac : fetch_word Plain.M.loaded_segments (0x17404 : word) = Some W_173ac.
Proof. vm_refl. Qed.
Lemma D_173ac : decode_any W_173ac = Some (Branch BC_NE 10 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173b0 : bv 32 := 0x0009a503.
Lemma F_173b0 : fetch_word Plain.M.loaded_segments (0x17408 : word) = Some W_173b0.
Proof. vm_refl. Qed.
Lemma D_173b0 : decode_any W_173b0 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173b4 : bv 32 := 0x00500593.
Lemma F_173b4 : fetch_word Plain.M.loaded_segments (0x1740c : word) = Some W_173b4.
Proof. vm_refl. Qed.
Lemma D_173b4 : decode_any W_173b4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173b8 : bv 32 := 0x00a5cc63.
Lemma F_173b8 : fetch_word Plain.M.loaded_segments (0x17410 : word) = Some W_173b8.
Proof. vm_refl. Qed.
Lemma D_173b8 : decode_any W_173b8 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173bc : bv 32 := 0xffff9517.
Lemma F_173bc : fetch_word Plain.M.loaded_segments (0x17414 : word) = Some W_173bc.
Proof. vm_refl. Qed.
Lemma D_173bc : decode_any W_173bc = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173c0 : bv 32 := 0xffffa597.
Lemma F_173c0 : fetch_word Plain.M.loaded_segments (0x17418 : word) = Some W_173c0.
Proof. vm_refl. Qed.
Lemma D_173c0 : decode_any W_173c0 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173c4 : bv 32 := 0x10b50513.
Lemma F_173c4 : fetch_word Plain.M.loaded_segments (0x1741c : word) = Some W_173c4.
Proof. vm_refl. Qed.
Lemma D_173c4 : decode_any W_173c4 = Some (OpImm ALU_ADD 10 10 267, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173c8 : bv 32 := 0x99758593.
Lemma F_173c8 : fetch_word Plain.M.loaded_segments (0x17420 : word) = Some W_173c8.
Proof. vm_refl. Qed.
Lemma D_173c8 : decode_any W_173c8 = Some (OpImm ALU_ADD 11 11 2455, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173cc : bv 32 := 0xf19ff06f.
Lemma F_173cc : fetch_word Plain.M.loaded_segments (0x17424 : word) = Some W_173cc.
Proof. vm_refl. Qed.
Lemma D_173cc : decode_any W_173cc = Some (Jal 0 2096920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17420 : bv 32 := 0x03843503.
Lemma F_17420 : fetch_word Plain.M.loaded_segments (0x17478 : word) = Some W_17420.
Proof. vm_refl. Qed.
Lemma D_17420 : decode_any W_17420 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17424 : bv 32 := 0x0384b583.
Lemma F_17424 : fetch_word Plain.M.loaded_segments (0x1747c : word) = Some W_17424.
Proof. vm_refl. Qed.
Lemma D_17424 : decode_any W_17424 = Some (Load SZ8 true 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17428 : bv 32 := 0x00090613.
Lemma F_17428 : fetch_word Plain.M.loaded_segments (0x17480 : word) = Some W_17428.
Proof. vm_refl. Qed.
Lemma D_17428 : decode_any W_17428 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1742c : bv 32 := 0x7c4130ef.
Lemma F_1742c : fetch_word Plain.M.loaded_segments (0x17484 : word) = Some W_1742c.
Proof. vm_refl. Qed.
Lemma D_1742c : decode_any W_1742c = Some (Jal 1 79812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17430 : bv 32 := 0x00040513.
Lemma F_17430 : fetch_word Plain.M.loaded_segments (0x17488 : word) = Some W_17430.
Proof. vm_refl. Qed.
Lemma D_17430 : decode_any W_17430 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17434 : bv 32 := 0x02813083.
Lemma F_17434 : fetch_word Plain.M.loaded_segments (0x1748c : word) = Some W_17434.
Proof. vm_refl. Qed.
Lemma D_17434 : decode_any W_17434 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17438 : bv 32 := 0x02013403.
Lemma F_17438 : fetch_word Plain.M.loaded_segments (0x17490 : word) = Some W_17438.
Proof. vm_refl. Qed.
Lemma D_17438 : decode_any W_17438 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1743c : bv 32 := 0x01813483.
Lemma F_1743c : fetch_word Plain.M.loaded_segments (0x17494 : word) = Some W_1743c.
Proof. vm_refl. Qed.
Lemma D_1743c : decode_any W_1743c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17440 : bv 32 := 0x01013903.
Lemma F_17440 : fetch_word Plain.M.loaded_segments (0x17498 : word) = Some W_17440.
Proof. vm_refl. Qed.
Lemma D_17440 : decode_any W_17440 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17444 : bv 32 := 0x00813983.
Lemma F_17444 : fetch_word Plain.M.loaded_segments (0x1749c : word) = Some W_17444.
Proof. vm_refl. Qed.
Lemma D_17444 : decode_any W_17444 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17448 : bv 32 := 0x03010113.
Lemma F_17448 : fetch_word Plain.M.loaded_segments (0x174a0 : word) = Some W_17448.
Proof. vm_refl. Qed.
Lemma D_17448 : decode_any W_17448 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1744c : bv 32 := 0x00008067.
Lemma F_1744c : fetch_word Plain.M.loaded_segments (0x174a4 : word) = Some W_1744c.
Proof. vm_refl. Qed.
Lemma D_1744c : decode_any W_1744c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17908 : bv 32 := 0xfd010113.
Lemma F_17908 : fetch_word Plain.M.loaded_segments (0x17960 : word) = Some W_17908.
Proof. vm_refl. Qed.
Lemma D_17908 : decode_any W_17908 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1790c : bv 32 := 0x02113423.
Lemma F_1790c : fetch_word Plain.M.loaded_segments (0x17964 : word) = Some W_1790c.
Proof. vm_refl. Qed.
Lemma D_1790c : decode_any W_1790c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17910 : bv 32 := 0x02813023.
Lemma F_17910 : fetch_word Plain.M.loaded_segments (0x17968 : word) = Some W_17910.
Proof. vm_refl. Qed.
Lemma D_17910 : decode_any W_17910 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17914 : bv 32 := 0x00913c23.
Lemma F_17914 : fetch_word Plain.M.loaded_segments (0x1796c : word) = Some W_17914.
Proof. vm_refl. Qed.
Lemma D_17914 : decode_any W_17914 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17918 : bv 32 := 0x01213823.
Lemma F_17918 : fetch_word Plain.M.loaded_segments (0x17970 : word) = Some W_17918.
Proof. vm_refl. Qed.
Lemma D_17918 : decode_any W_17918 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1791c : bv 32 := 0x06050063.
Lemma F_1791c : fetch_word Plain.M.loaded_segments (0x17974 : word) = Some W_1791c.
Proof. vm_refl. Qed.
Lemma D_1791c : decode_any W_1791c = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17920 : bv 32 := 0x00050493.
Lemma F_17920 : fetch_word Plain.M.loaded_segments (0x17978 : word) = Some W_17920.
Proof. vm_refl. Qed.
Lemma D_17920 : decode_any W_17920 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17924 : bv 32 := 0x00058913.
Lemma F_17924 : fetch_word Plain.M.loaded_segments (0x1797c : word) = Some W_17924.
Proof. vm_refl. Qed.
Lemma D_17924 : decode_any W_17924 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17928 : bv 32 := 0x00c10593.
Lemma F_17928 : fetch_word Plain.M.loaded_segments (0x17980 : word) = Some W_17928.
Proof. vm_refl. Qed.
Lemma D_17928 : decode_any W_17928 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1792c : bv 32 := 0x00810613.
Lemma F_1792c : fetch_word Plain.M.loaded_segments (0x17984 : word) = Some W_1792c.
Proof. vm_refl. Qed.
Lemma D_1792c : decode_any W_1792c = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17930 : bv 32 := 0x00410693.
Lemma F_17930 : fetch_word Plain.M.loaded_segments (0x17988 : word) = Some W_17930.
Proof. vm_refl. Qed.
Lemma D_17930 : decode_any W_17930 = Some (OpImm ALU_ADD 13 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17934 : bv 32 := 0xc1cff0ef.
Lemma F_17934 : fetch_word Plain.M.loaded_segments (0x1798c : word) = Some W_17934.
Proof. vm_refl. Qed.
Lemma D_17934 : decode_any W_17934 = Some (Jal 1 2094108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17938 : bv 32 := 0x00412503.
Lemma F_17938 : fetch_word Plain.M.loaded_segments (0x17990 : word) = Some W_17938.
Proof. vm_refl. Qed.
Lemma D_17938 : decode_any W_17938 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1793c : bv 32 := 0x02000593.
Lemma F_1793c : fetch_word Plain.M.loaded_segments (0x17994 : word) = Some W_1793c.
Proof. vm_refl. Qed.
Lemma D_1793c : decode_any W_1793c = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17940 : bv 32 := 0x12b50463.
Lemma F_17940 : fetch_word Plain.M.loaded_segments (0x17998 : word) = Some W_17940.
Proof. vm_refl. Qed.
Lemma D_17940 : decode_any W_17940 = Some (Branch BC_EQ 10 11 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a68 : bv 32 := 0x00000513.
Lemma F_17a68 : fetch_word Plain.M.loaded_segments (0x17ac0 : word) = Some W_17a68.
Proof. vm_refl. Qed.
Lemma D_17a68 : decode_any W_17a68 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a6c : bv 32 := 0x02813083.
Lemma F_17a6c : fetch_word Plain.M.loaded_segments (0x17ac4 : word) = Some W_17a6c.
Proof. vm_refl. Qed.
Lemma D_17a6c : decode_any W_17a6c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a70 : bv 32 := 0x02013403.
Lemma F_17a70 : fetch_word Plain.M.loaded_segments (0x17ac8 : word) = Some W_17a70.
Proof. vm_refl. Qed.
Lemma D_17a70 : decode_any W_17a70 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a74 : bv 32 := 0x01813483.
Lemma F_17a74 : fetch_word Plain.M.loaded_segments (0x17acc : word) = Some W_17a74.
Proof. vm_refl. Qed.
Lemma D_17a74 : decode_any W_17a74 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a78 : bv 32 := 0x01013903.
Lemma F_17a78 : fetch_word Plain.M.loaded_segments (0x17ad0 : word) = Some W_17a78.
Proof. vm_refl. Qed.
Lemma D_17a78 : decode_any W_17a78 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a7c : bv 32 := 0x03010113.
Lemma F_17a7c : fetch_word Plain.M.loaded_segments (0x17ad4 : word) = Some W_17a7c.
Proof. vm_refl. Qed.
Lemma D_17a7c : decode_any W_17a7c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a80 : bv 32 := 0x00008067.
Lemma F_17a80 : fetch_word Plain.M.loaded_segments (0x17ad8 : word) = Some W_17a80.
Proof. vm_refl. Qed.
Lemma D_17a80 : decode_any W_17a80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e94 : bv 32 := 0xfe010113.
Lemma F_17e94 : fetch_word Plain.M.loaded_segments (0x17eec : word) = Some W_17e94.
Proof. vm_refl. Qed.
Lemma D_17e94 : decode_any W_17e94 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e98 : bv 32 := 0x00113c23.
Lemma F_17e98 : fetch_word Plain.M.loaded_segments (0x17ef0 : word) = Some W_17e98.
Proof. vm_refl. Qed.
Lemma D_17e98 : decode_any W_17e98 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e9c : bv 32 := 0x00813823.
Lemma F_17e9c : fetch_word Plain.M.loaded_segments (0x17ef4 : word) = Some W_17e9c.
Proof. vm_refl. Qed.
Lemma D_17e9c : decode_any W_17e9c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ea0 : bv 32 := 0x00913423.
Lemma F_17ea0 : fetch_word Plain.M.loaded_segments (0x17ef8 : word) = Some W_17ea0.
Proof. vm_refl. Qed.
Lemma D_17ea0 : decode_any W_17ea0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ea4 : bv 32 := 0x06050463.
Lemma F_17ea4 : fetch_word Plain.M.loaded_segments (0x17efc : word) = Some W_17ea4.
Proof. vm_refl. Qed.
Lemma D_17ea4 : decode_any W_17ea4 = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ea8 : bv 32 := 0x00050413.
Lemma F_17ea8 : fetch_word Plain.M.loaded_segments (0x17f00 : word) = Some W_17ea8.
Proof. vm_refl. Qed.
Lemma D_17ea8 : decode_any W_17ea8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17eac : bv 32 := 0x00410613.
Lemma F_17eac : fetch_word Plain.M.loaded_segments (0x17f04 : word) = Some W_17eac.
Proof. vm_refl. Qed.
Lemma D_17eac : decode_any W_17eac = Some (OpImm ALU_ADD 12 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17eb0 : bv 32 := 0x00000593.
Lemma F_17eb0 : fetch_word Plain.M.loaded_segments (0x17f08 : word) = Some W_17eb0.
Proof. vm_refl. Qed.
Lemma D_17eb0 : decode_any W_17eb0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17eb4 : bv 32 := 0x0dc000ef.
Lemma F_17eb4 : fetch_word Plain.M.loaded_segments (0x17f0c : word) = Some W_17eb4.
Proof. vm_refl. Qed.
Lemma D_17eb4 : decode_any W_17eb4 = Some (Jal 1 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17eb8 : bv 32 := 0x00412503.
Lemma F_17eb8 : fetch_word Plain.M.loaded_segments (0x17f10 : word) = Some W_17eb8.
Proof. vm_refl. Qed.
Lemma D_17eb8 : decode_any W_17eb8 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ebc : bv 32 := 0x08050663.
Lemma F_17ebc : fetch_word Plain.M.loaded_segments (0x17f14 : word) = Some W_17ebc.
Proof. vm_refl. Qed.
Lemma D_17ebc : decode_any W_17ebc = Some (Branch BC_EQ 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ec0 : bv 32 := 0x00100513.
Lemma F_17ec0 : fetch_word Plain.M.loaded_segments (0x17f18 : word) = Some W_17ec0.
Proof. vm_refl. Qed.
Lemma D_17ec0 : decode_any W_17ec0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ec4 : bv 32 := 0x01800593.
Lemma F_17ec4 : fetch_word Plain.M.loaded_segments (0x17f1c : word) = Some W_17ec4.
Proof. vm_refl. Qed.
Lemma D_17ec4 : decode_any W_17ec4 = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ec8 : bv 32 := 0x781080ef.
Lemma F_17ec8 : fetch_word Plain.M.loaded_segments (0x17f20 : word) = Some W_17ec8.
Proof. vm_refl. Qed.
Lemma D_17ec8 : decode_any W_17ec8 = Some (Jal 1 36736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ecc : bv 32 := 0x00050493.
Lemma F_17ecc : fetch_word Plain.M.loaded_segments (0x17f24 : word) = Some W_17ecc.
Proof. vm_refl. Qed.
Lemma D_17ecc : decode_any W_17ecc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ed0 : bv 32 := 0x00c42503.
Lemma F_17ed0 : fetch_word Plain.M.loaded_segments (0x17f28 : word) = Some W_17ed0.
Proof. vm_refl. Qed.
Lemma D_17ed0 : decode_any W_17ed0 = Some (Load SZ4 true 10 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ed4 : bv 32 := 0x0025159b.
Lemma F_17ed4 : fetch_word Plain.M.loaded_segments (0x17f2c : word) = Some W_17ed4.
Proof. vm_refl. Qed.
Lemma D_17ed4 : decode_any W_17ed4 = Some (ShiftImm32 ALU_SLL 11 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ed8 : bv 32 := 0x00100513.
Lemma F_17ed8 : fetch_word Plain.M.loaded_segments (0x17f30 : word) = Some W_17ed8.
Proof. vm_refl. Qed.
Lemma D_17ed8 : decode_any W_17ed8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17edc : bv 32 := 0x76d080ef.
Lemma F_17edc : fetch_word Plain.M.loaded_segments (0x17f34 : word) = Some W_17edc.
Proof. vm_refl. Qed.
Lemma D_17edc : decode_any W_17edc = Some (Jal 1 36716, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ee0 : bv 32 := 0x00a4b023.
Lemma F_17ee0 : fetch_word Plain.M.loaded_segments (0x17f38 : word) = Some W_17ee0.
Proof. vm_refl. Qed.
Lemma D_17ee0 : decode_any W_17ee0 = Some (Store SZ8 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ee4 : bv 32 := 0x01042603.
Lemma F_17ee4 : fetch_word Plain.M.loaded_segments (0x17f3c : word) = Some W_17ee4.
Proof. vm_refl. Qed.
Lemma D_17ee4 : decode_any W_17ee4 = Some (Load SZ4 true 12 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ee8 : bv 32 := 0x00043583.
Lemma F_17ee8 : fetch_word Plain.M.loaded_segments (0x17f40 : word) = Some W_17ee8.
Proof. vm_refl. Qed.
Lemma D_17ee8 : decode_any W_17ee8 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17eec : bv 32 := 0x00261613.
Lemma F_17eec : fetch_word Plain.M.loaded_segments (0x17f44 : word) = Some W_17eec.
Proof. vm_refl. Qed.
Lemma D_17eec : decode_any W_17eec = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ef0 : bv 32 := 0x501120ef.
Lemma F_17ef0 : fetch_word Plain.M.loaded_segments (0x17f48 : word) = Some W_17ef0.
Proof. vm_refl. Qed.
Lemma D_17ef0 : decode_any W_17ef0 = Some (Jal 1 77056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ef4 : bv 32 := 0x00048513.
Lemma F_17ef4 : fetch_word Plain.M.loaded_segments (0x17f4c : word) = Some W_17ef4.
Proof. vm_refl. Qed.
Lemma D_17ef4 : decode_any W_17ef4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ef8 : bv 32 := 0x01042583.
Lemma F_17ef8 : fetch_word Plain.M.loaded_segments (0x17f50 : word) = Some W_17ef8.
Proof. vm_refl. Qed.
Lemma D_17ef8 : decode_any W_17ef8 = Some (Load SZ4 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17efc : bv 32 := 0x00b4a823.
Lemma F_17efc : fetch_word Plain.M.loaded_segments (0x17f54 : word) = Some W_17efc.
Proof. vm_refl. Qed.
Lemma D_17efc : decode_any W_17efc = Some (Store SZ4 9 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f00 : bv 32 := 0x00843583.
Lemma F_17f00 : fetch_word Plain.M.loaded_segments (0x17f58 : word) = Some W_17f00.
Proof. vm_refl. Qed.
Lemma D_17f00 : decode_any W_17f00 = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f04 : bv 32 := 0x00b4b423.
Lemma F_17f04 : fetch_word Plain.M.loaded_segments (0x17f5c : word) = Some W_17f04.
Proof. vm_refl. Qed.
Lemma D_17f04 : decode_any W_17f04 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f08 : bv 32 := 0x0740006f.
Lemma F_17f08 : fetch_word Plain.M.loaded_segments (0x17f60 : word) = Some W_17f08.
Proof. vm_refl. Qed.
Lemma D_17f08 : decode_any W_17f08 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f7c : bv 32 := 0x01813083.
Lemma F_17f7c : fetch_word Plain.M.loaded_segments (0x17fd4 : word) = Some W_17f7c.
Proof. vm_refl. Qed.
Lemma D_17f7c : decode_any W_17f7c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f80 : bv 32 := 0x01013403.
Lemma F_17f80 : fetch_word Plain.M.loaded_segments (0x17fd8 : word) = Some W_17f80.
Proof. vm_refl. Qed.
Lemma D_17f80 : decode_any W_17f80 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f84 : bv 32 := 0x00813483.
Lemma F_17f84 : fetch_word Plain.M.loaded_segments (0x17fdc : word) = Some W_17f84.
Proof. vm_refl. Qed.
Lemma D_17f84 : decode_any W_17f84 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f88 : bv 32 := 0x02010113.
Lemma F_17f88 : fetch_word Plain.M.loaded_segments (0x17fe0 : word) = Some W_17f88.
Proof. vm_refl. Qed.
Lemma D_17f88 : decode_any W_17f88 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f8c : bv 32 := 0x00008067.
Lemma F_17f8c : fetch_word Plain.M.loaded_segments (0x17fe4 : word) = Some W_17f8c.
Proof. vm_refl. Qed.
Lemma D_17f8c : decode_any W_17f8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

