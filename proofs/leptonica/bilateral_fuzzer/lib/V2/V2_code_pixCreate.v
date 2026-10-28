(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_192d0 : bv 32 := 0xff010113.
Lemma F_192d0 : fetch_word Ubsan.M.loaded_segments (0x192d0 : word) = Some W_192d0.
Proof. vm_refl. Qed.
Lemma D_192d0 : decode_any W_192d0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_192d4 : bv 32 := 0x00113423.
Lemma F_192d4 : fetch_word Ubsan.M.loaded_segments (0x192d4 : word) = Some W_192d4.
Proof. vm_refl. Qed.
Lemma D_192d4 : decode_any W_192d4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_192d8 : bv 32 := 0x00813023.
Lemma F_192d8 : fetch_word Ubsan.M.loaded_segments (0x192d8 : word) = Some W_192d8.
Proof. vm_refl. Qed.
Lemma D_192d8 : decode_any W_192d8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_192dc : bv 32 := 0x098000ef.
Lemma F_192dc : fetch_word Ubsan.M.loaded_segments (0x192dc : word) = Some W_192dc.
Proof. vm_refl. Qed.
Lemma D_192dc : decode_any W_192dc = Some (Jal 1 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_192e0 : bv 32 := 0x04050263.
Lemma F_192e0 : fetch_word Ubsan.M.loaded_segments (0x192e0 : word) = Some W_192e0.
Proof. vm_refl. Qed.
Lemma D_192e0 : decode_any W_192e0 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_192e4 : bv 32 := 0x00757593.
Lemma F_192e4 : fetch_word Ubsan.M.loaded_segments (0x192e4 : word) = Some W_192e4.
Proof. vm_refl. Qed.
Lemma D_192e4 : decode_any W_192e4 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_192e8 : bv 32 := 0x08059463.
Lemma F_192e8 : fetch_word Ubsan.M.loaded_segments (0x192e8 : word) = Some W_192e8.
Proof. vm_refl. Qed.
Lemma D_192e8 : decode_any W_192e8 = Some (Branch BC_NE 11 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_192ec : bv 32 := 0x01056583.
Lemma F_192ec : fetch_word Ubsan.M.loaded_segments (0x192ec : word) = Some W_192ec.
Proof. vm_refl. Qed.
Lemma D_192ec : decode_any W_192ec = Some (Load SZ4 false 11 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_192f0 : bv 32 := 0x00456603.
Lemma F_192f0 : fetch_word Ubsan.M.loaded_segments (0x192f0 : word) = Some W_192f0.
Proof. vm_refl. Qed.
Lemma D_192f0 : decode_any W_192f0 = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_192f4 : bv 32 := 0x00259593.
Lemma F_192f4 : fetch_word Ubsan.M.loaded_segments (0x192f4 : word) = Some W_192f4.
Proof. vm_refl. Qed.
Lemma D_192f4 : decode_any W_192f4 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_192f8 : bv 32 := 0x02c596b3.
Lemma F_192f8 : fetch_word Ubsan.M.loaded_segments (0x192f8 : word) = Some W_192f8.
Proof. vm_refl. Qed.
Lemma D_192f8 : decode_any W_192f8 = Some (Mul M_MULH 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_192fc : bv 32 := 0x02c58633.
Lemma F_192fc : fetch_word Ubsan.M.loaded_segments (0x192fc : word) = Some W_192fc.
Proof. vm_refl. Qed.
Lemma D_192fc : decode_any W_192fc = Some (Mul M_MUL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19300 : bv 32 := 0x43f65593.
Lemma F_19300 : fetch_word Ubsan.M.loaded_segments (0x19300 : word) = Some W_19300.
Proof. vm_refl. Qed.
Lemma D_19300 : decode_any W_19300 = Some (ShiftImm ALU_SRA 11 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_19304 : bv 32 := 0x06b69663.
Lemma F_19304 : fetch_word Ubsan.M.loaded_segments (0x19304 : word) = Some W_19304.
Proof. vm_refl. Qed.
Lemma D_19304 : decode_any W_19304 = Some (Branch BC_NE 13 11 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_19308 : bv 32 := 0x03853583.
Lemma F_19308 : fetch_word Ubsan.M.loaded_segments (0x19308 : word) = Some W_19308.
Proof. vm_refl. Qed.
Lemma D_19308 : decode_any W_19308 = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1930c : bv 32 := 0x00050413.
Lemma F_1930c : fetch_word Ubsan.M.loaded_segments (0x1930c : word) = Some W_1930c.
Proof. vm_refl. Qed.
Lemma D_1930c : decode_any W_1930c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19310 : bv 32 := 0x00058513.
Lemma F_19310 : fetch_word Ubsan.M.loaded_segments (0x19310 : word) = Some W_19310.
Proof. vm_refl. Qed.
Lemma D_19310 : decode_any W_19310 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19314 : bv 32 := 0x00000593.
Lemma F_19314 : fetch_word Ubsan.M.loaded_segments (0x19314 : word) = Some W_19314.
Proof. vm_refl. Qed.
Lemma D_19314 : decode_any W_19314 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19318 : bv 32 := 0x5682a0ef.
Lemma F_19318 : fetch_word Ubsan.M.loaded_segments (0x19318 : word) = Some W_19318.
Proof. vm_refl. Qed.
Lemma D_19318 : decode_any W_19318 = Some (Jal 1 173416, 4%Z).
Proof. vm_refl. Qed.

Definition W_1931c : bv 32 := 0x00040513.
Lemma F_1931c : fetch_word Ubsan.M.loaded_segments (0x1931c : word) = Some W_1931c.
Proof. vm_refl. Qed.
Lemma D_1931c : decode_any W_1931c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19320 : bv 32 := 0x0400006f.
Lemma F_19320 : fetch_word Ubsan.M.loaded_segments (0x19320 : word) = Some W_19320.
Proof. vm_refl. Qed.
Lemma D_19320 : decode_any W_19320 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_19324 : bv 32 := 0x0002c517.
Lemma F_19324 : fetch_word Ubsan.M.loaded_segments (0x19324 : word) = Some W_19324.
Proof. vm_refl. Qed.
Lemma D_19324 : decode_any W_19324 = Some (Auipc 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_19328 : bv 32 := 0xb7453503.
Lemma F_19328 : fetch_word Ubsan.M.loaded_segments (0x19328 : word) = Some W_19328.
Proof. vm_refl. Qed.
Lemma D_19328 : decode_any W_19328 = Some (Load SZ8 true 10 10 2932, 4%Z).
Proof. vm_refl. Qed.

Definition W_1932c : bv 32 := 0x00052503.
Lemma F_1932c : fetch_word Ubsan.M.loaded_segments (0x1932c : word) = Some W_1932c.
Proof. vm_refl. Qed.
Lemma D_1932c : decode_any W_1932c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19330 : bv 32 := 0x00500593.
Lemma F_19330 : fetch_word Ubsan.M.loaded_segments (0x19330 : word) = Some W_19330.
Proof. vm_refl. Qed.
Lemma D_19330 : decode_any W_19330 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_19334 : bv 32 := 0x02a5c463.
Lemma F_19334 : fetch_word Ubsan.M.loaded_segments (0x19334 : word) = Some W_19334.
Proof. vm_refl. Qed.
Lemma D_19334 : decode_any W_19334 = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19338 : bv 32 := 0xffff7517.
Lemma F_19338 : fetch_word Ubsan.M.loaded_segments (0x19338 : word) = Some W_19338.
Proof. vm_refl. Qed.
Lemma D_19338 : decode_any W_19338 = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_1933c : bv 32 := 0xffff8597.
Lemma F_1933c : fetch_word Ubsan.M.loaded_segments (0x1933c : word) = Some W_1933c.
Proof. vm_refl. Qed.
Lemma D_1933c : decode_any W_1933c = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_19340 : bv 32 := 0x42d50513.
Lemma F_19340 : fetch_word Ubsan.M.loaded_segments (0x19340 : word) = Some W_19340.
Proof. vm_refl. Qed.
Lemma D_19340 : decode_any W_19340 = Some (OpImm ALU_ADD 10 10 1069, 4%Z).
Proof. vm_refl. Qed.

Definition W_19344 : bv 32 := 0xab058593.
Lemma F_19344 : fetch_word Ubsan.M.loaded_segments (0x19344 : word) = Some W_19344.
Proof. vm_refl. Qed.
Lemma D_19344 : decode_any W_19344 = Some (OpImm ALU_ADD 11 11 2736, 4%Z).
Proof. vm_refl. Qed.

Definition W_19348 : bv 32 := 0x00000613.
Lemma F_19348 : fetch_word Ubsan.M.loaded_segments (0x19348 : word) = Some W_19348.
Proof. vm_refl. Qed.
Lemma D_19348 : decode_any W_19348 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1934c : bv 32 := 0x00813083.
Lemma F_1934c : fetch_word Ubsan.M.loaded_segments (0x1934c : word) = Some W_1934c.
Proof. vm_refl. Qed.
Lemma D_1934c : decode_any W_1934c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19350 : bv 32 := 0x00013403.
Lemma F_19350 : fetch_word Ubsan.M.loaded_segments (0x19350 : word) = Some W_19350.
Proof. vm_refl. Qed.
Lemma D_19350 : decode_any W_19350 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19354 : bv 32 := 0x01010113.
Lemma F_19354 : fetch_word Ubsan.M.loaded_segments (0x19354 : word) = Some W_19354.
Proof. vm_refl. Qed.
Lemma D_19354 : decode_any W_19354 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19358 : bv 32 := 0xb6dfe06f.
Lemma F_19358 : fetch_word Ubsan.M.loaded_segments (0x19358 : word) = Some W_19358.
Proof. vm_refl. Qed.
Lemma D_19358 : decode_any W_19358 = Some (Jal 0 2091884, 4%Z).
Proof. vm_refl. Qed.

Definition W_1935c : bv 32 := 0x00000513.
Lemma F_1935c : fetch_word Ubsan.M.loaded_segments (0x1935c : word) = Some W_1935c.
Proof. vm_refl. Qed.
Lemma D_1935c : decode_any W_1935c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19360 : bv 32 := 0x00813083.
Lemma F_19360 : fetch_word Ubsan.M.loaded_segments (0x19360 : word) = Some W_19360.
Proof. vm_refl. Qed.
Lemma D_19360 : decode_any W_19360 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19364 : bv 32 := 0x00013403.
Lemma F_19364 : fetch_word Ubsan.M.loaded_segments (0x19364 : word) = Some W_19364.
Proof. vm_refl. Qed.
Lemma D_19364 : decode_any W_19364 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19368 : bv 32 := 0x01010113.
Lemma F_19368 : fetch_word Ubsan.M.loaded_segments (0x19368 : word) = Some W_19368.
Proof. vm_refl. Qed.
Lemma D_19368 : decode_any W_19368 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1936c : bv 32 := 0x00008067.
Lemma F_1936c : fetch_word Ubsan.M.loaded_segments (0x1936c : word) = Some W_1936c.
Proof. vm_refl. Qed.
Lemma D_1936c : decode_any W_1936c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19370 : bv 32 := 0xc0001073.
Lemma F_19370 : fetch_word Ubsan.M.loaded_segments (0x19370 : word) = Some W_19370.
Proof. vm_refl. Qed.
Lemma D_19370 : decode_any W_19370 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.

Definition W_19374 : bv 32 := 0xfe010113.
Lemma F_19374 : fetch_word Ubsan.M.loaded_segments (0x19374 : word) = Some W_19374.
Proof. vm_refl. Qed.
Lemma D_19374 : decode_any W_19374 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_19378 : bv 32 := 0x00113c23.
Lemma F_19378 : fetch_word Ubsan.M.loaded_segments (0x19378 : word) = Some W_19378.
Proof. vm_refl. Qed.
Lemma D_19378 : decode_any W_19378 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1937c : bv 32 := 0x00813823.
Lemma F_1937c : fetch_word Ubsan.M.loaded_segments (0x1937c : word) = Some W_1937c.
Proof. vm_refl. Qed.
Lemma D_1937c : decode_any W_1937c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19380 : bv 32 := 0x00913423.
Lemma F_19380 : fetch_word Ubsan.M.loaded_segments (0x19380 : word) = Some W_19380.
Proof. vm_refl. Qed.
Lemma D_19380 : decode_any W_19380 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19384 : bv 32 := 0x00058493.
Lemma F_19384 : fetch_word Ubsan.M.loaded_segments (0x19384 : word) = Some W_19384.
Proof. vm_refl. Qed.
Lemma D_19384 : decode_any W_19384 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19388 : bv 32 := 0x134000ef.
Lemma F_19388 : fetch_word Ubsan.M.loaded_segments (0x19388 : word) = Some W_19388.
Proof. vm_refl. Qed.
Lemma D_19388 : decode_any W_19388 = Some (Jal 1 308, 4%Z).
Proof. vm_refl. Qed.

Definition W_1938c : bv 32 := 0x04050863.
Lemma F_1938c : fetch_word Ubsan.M.loaded_segments (0x1938c : word) = Some W_1938c.
Proof. vm_refl. Qed.
Lemma D_1938c : decode_any W_1938c = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_19390 : bv 32 := 0x00050413.
Lemma F_19390 : fetch_word Ubsan.M.loaded_segments (0x19390 : word) = Some W_19390.
Proof. vm_refl. Qed.
Lemma D_19390 : decode_any W_19390 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19394 : bv 32 := 0x00757513.
Lemma F_19394 : fetch_word Ubsan.M.loaded_segments (0x19394 : word) = Some W_19394.
Proof. vm_refl. Qed.
Lemma D_19394 : decode_any W_19394 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_19398 : bv 32 := 0x12051063.
Lemma F_19398 : fetch_word Ubsan.M.loaded_segments (0x19398 : word) = Some W_19398.
Proof. vm_refl. Qed.
Lemma D_19398 : decode_any W_19398 = Some (Branch BC_NE 10 0 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_1939c : bv 32 := 0x01042503.
Lemma F_1939c : fetch_word Ubsan.M.loaded_segments (0x1939c : word) = Some W_1939c.
Proof. vm_refl. Qed.
Lemma D_1939c : decode_any W_1939c = Some (Load SZ4 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_193a0 : bv 32 := 0x00251513.
Lemma F_193a0 : fetch_word Ubsan.M.loaded_segments (0x193a0 : word) = Some W_193a0.
Proof. vm_refl. Qed.
Lemma D_193a0 : decode_any W_193a0 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_193a4 : bv 32 := 0x029515b3.
Lemma F_193a4 : fetch_word Ubsan.M.loaded_segments (0x193a4 : word) = Some W_193a4.
Proof. vm_refl. Qed.
Lemma D_193a4 : decode_any W_193a4 = Some (Mul M_MULH 11 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_193a8 : bv 32 := 0x02950533.
Lemma F_193a8 : fetch_word Ubsan.M.loaded_segments (0x193a8 : word) = Some W_193a8.
Proof. vm_refl. Qed.
Lemma D_193a8 : decode_any W_193a8 = Some (Mul M_MUL 10 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_193ac : bv 32 := 0x43f55613.
Lemma F_193ac : fetch_word Ubsan.M.loaded_segments (0x193ac : word) = Some W_193ac.
Proof. vm_refl. Qed.
Lemma D_193ac : decode_any W_193ac = Some (ShiftImm ALU_SRA 12 10 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_193b0 : bv 32 := 0x10c59463.
Lemma F_193b0 : fetch_word Ubsan.M.loaded_segments (0x193b0 : word) = Some W_193b0.
Proof. vm_refl. Qed.
Lemma D_193b0 : decode_any W_193b0 = Some (Branch BC_NE 11 12 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_193b4 : bv 32 := 0x0002d597.
Lemma F_193b4 : fetch_word Ubsan.M.loaded_segments (0x193b4 : word) = Some W_193b4.
Proof. vm_refl. Qed.
Lemma D_193b4 : decode_any W_193b4 = Some (Auipc 11 45, 4%Z).
Proof. vm_refl. Qed.

Definition W_193b8 : bv 32 := 0xb6458493.
Lemma F_193b8 : fetch_word Ubsan.M.loaded_segments (0x193b8 : word) = Some W_193b8.
Proof. vm_refl. Qed.
Lemma D_193b8 : decode_any W_193b8 = Some (OpImm ALU_ADD 9 11 2916, 4%Z).
Proof. vm_refl. Qed.

Definition W_193bc : bv 32 := 0x0004b583.
Lemma F_193bc : fetch_word Ubsan.M.loaded_segments (0x193bc : word) = Some W_193bc.
Proof. vm_refl. Qed.
Lemma D_193bc : decode_any W_193bc = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_193c0 : bv 32 := 0x000580e7.
Lemma F_193c0 : fetch_word Ubsan.M.loaded_segments (0x193c0 : word) = Some W_193c0.
Proof. vm_refl. Qed.
Lemma D_193c0 : decode_any W_193c0 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_193c4 : bv 32 := 0x04050a63.
Lemma F_193c4 : fetch_word Ubsan.M.loaded_segments (0x193c4 : word) = Some W_193c4.
Proof. vm_refl. Qed.
Lemma D_193c4 : decode_any W_193c4 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_193c8 : bv 32 := 0x02a43c23.
Lemma F_193c8 : fetch_word Ubsan.M.loaded_segments (0x193c8 : word) = Some W_193c8.
Proof. vm_refl. Qed.
Lemma D_193c8 : decode_any W_193c8 = Some (Store SZ8 8 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_193cc : bv 32 := 0x00040513.
Lemma F_193cc : fetch_word Ubsan.M.loaded_segments (0x193cc : word) = Some W_193cc.
Proof. vm_refl. Qed.
Lemma D_193cc : decode_any W_193cc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_193d0 : bv 32 := 0x00000593.
Lemma F_193d0 : fetch_word Ubsan.M.loaded_segments (0x193d0 : word) = Some W_193d0.
Proof. vm_refl. Qed.
Lemma D_193d0 : decode_any W_193d0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_193d4 : bv 32 := 0x141020ef.
Lemma F_193d4 : fetch_word Ubsan.M.loaded_segments (0x193d4 : word) = Some W_193d4.
Proof. vm_refl. Qed.
Lemma D_193d4 : decode_any W_193d4 = Some (Jal 1 10560, 4%Z).
Proof. vm_refl. Qed.

Definition W_193d8 : bv 32 := 0x0c80006f.
Lemma F_193d8 : fetch_word Ubsan.M.loaded_segments (0x193d8 : word) = Some W_193d8.
Proof. vm_refl. Qed.
Lemma D_193d8 : decode_any W_193d8 = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_193dc : bv 32 := 0x0002c517.
Lemma F_193dc : fetch_word Ubsan.M.loaded_segments (0x193dc : word) = Some W_193dc.
Proof. vm_refl. Qed.
Lemma D_193dc : decode_any W_193dc = Some (Auipc 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_193e0 : bv 32 := 0xabc53503.
Lemma F_193e0 : fetch_word Ubsan.M.loaded_segments (0x193e0 : word) = Some W_193e0.
Proof. vm_refl. Qed.
Lemma D_193e0 : decode_any W_193e0 = Some (Load SZ8 true 10 10 2748, 4%Z).
Proof. vm_refl. Qed.

Definition W_193e4 : bv 32 := 0x00052503.
Lemma F_193e4 : fetch_word Ubsan.M.loaded_segments (0x193e4 : word) = Some W_193e4.
Proof. vm_refl. Qed.
Lemma D_193e4 : decode_any W_193e4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_193e8 : bv 32 := 0x00500593.
Lemma F_193e8 : fetch_word Ubsan.M.loaded_segments (0x193e8 : word) = Some W_193e8.
Proof. vm_refl. Qed.
Lemma D_193e8 : decode_any W_193e8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_193ec : bv 32 := 0x0aa5c863.
Lemma F_193ec : fetch_word Ubsan.M.loaded_segments (0x193ec : word) = Some W_193ec.
Proof. vm_refl. Qed.
Lemma D_193ec : decode_any W_193ec = Some (Branch BC_LT 11 10 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_193f0 : bv 32 := 0xffff7517.
Lemma F_193f0 : fetch_word Ubsan.M.loaded_segments (0x193f0 : word) = Some W_193f0.
Proof. vm_refl. Qed.
Lemma D_193f0 : decode_any W_193f0 = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_193f4 : bv 32 := 0xffff7597.
Lemma F_193f4 : fetch_word Ubsan.M.loaded_segments (0x193f4 : word) = Some W_193f4.
Proof. vm_refl. Qed.
Lemma D_193f4 : decode_any W_193f4 = Some (Auipc 11 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_193f8 : bv 32 := 0x37550513.
Lemma F_193f8 : fetch_word Ubsan.M.loaded_segments (0x193f8 : word) = Some W_193f8.
Proof. vm_refl. Qed.
Lemma D_193f8 : decode_any W_193f8 = Some (OpImm ALU_ADD 10 10 885, 4%Z).
Proof. vm_refl. Qed.

Definition W_193fc : bv 32 := 0x6ce58593.
Lemma F_193fc : fetch_word Ubsan.M.loaded_segments (0x193fc : word) = Some W_193fc.
Proof. vm_refl. Qed.
Lemma D_193fc : decode_any W_193fc = Some (OpImm ALU_ADD 11 11 1742, 4%Z).
Proof. vm_refl. Qed.

Definition W_19400 : bv 32 := 0x00000613.
Lemma F_19400 : fetch_word Ubsan.M.loaded_segments (0x19400 : word) = Some W_19400.
Proof. vm_refl. Qed.
Lemma D_19400 : decode_any W_19400 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19404 : bv 32 := 0x01813083.
Lemma F_19404 : fetch_word Ubsan.M.loaded_segments (0x19404 : word) = Some W_19404.
Proof. vm_refl. Qed.
Lemma D_19404 : decode_any W_19404 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19408 : bv 32 := 0x01013403.
Lemma F_19408 : fetch_word Ubsan.M.loaded_segments (0x19408 : word) = Some W_19408.
Proof. vm_refl. Qed.
Lemma D_19408 : decode_any W_19408 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1940c : bv 32 := 0x00813483.
Lemma F_1940c : fetch_word Ubsan.M.loaded_segments (0x1940c : word) = Some W_1940c.
Proof. vm_refl. Qed.
Lemma D_1940c : decode_any W_1940c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19410 : bv 32 := 0x02010113.
Lemma F_19410 : fetch_word Ubsan.M.loaded_segments (0x19410 : word) = Some W_19410.
Proof. vm_refl. Qed.
Lemma D_19410 : decode_any W_19410 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19414 : bv 32 := 0xab1fe06f.
Lemma F_19414 : fetch_word Ubsan.M.loaded_segments (0x19414 : word) = Some W_19414.
Proof. vm_refl. Qed.
Lemma D_19414 : decode_any W_19414 = Some (Jal 0 2091696, 4%Z).
Proof. vm_refl. Qed.

Definition W_19418 : bv 32 := 0x01440513.
Lemma F_19418 : fetch_word Ubsan.M.loaded_segments (0x19418 : word) = Some W_19418.
Proof. vm_refl. Qed.
Lemma D_19418 : decode_any W_19418 = Some (OpImm ALU_ADD 10 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1941c : bv 32 := 0xfff00593.
Lemma F_1941c : fetch_word Ubsan.M.loaded_segments (0x1941c : word) = Some W_1941c.
Proof. vm_refl. Qed.
Lemma D_1941c : decode_any W_1941c = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_19420 : bv 32 := 0x06b5252f.
Lemma F_19420 : fetch_word Ubsan.M.loaded_segments (0x19420 : word) = Some W_19420.
Proof. vm_refl. Qed.
Lemma D_19420 : decode_any W_19420 = Some (Amo AMO_ADD AW true true 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_19424 : bv 32 := 0x00100593.
Lemma F_19424 : fetch_word Ubsan.M.loaded_segments (0x19424 : word) = Some W_19424.
Proof. vm_refl. Qed.
Lemma D_19424 : decode_any W_19424 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19428 : bv 32 := 0x04b51063.
Lemma F_19428 : fetch_word Ubsan.M.loaded_segments (0x19428 : word) = Some W_19428.
Proof. vm_refl. Qed.
Lemma D_19428 : decode_any W_19428 = Some (Branch BC_NE 10 11 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1942c : bv 32 := 0x03843503.
Lemma F_1942c : fetch_word Ubsan.M.loaded_segments (0x1942c : word) = Some W_1942c.
Proof. vm_refl. Qed.
Lemma D_1942c : decode_any W_1942c = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_19430 : bv 32 := 0x00050663.
Lemma F_19430 : fetch_word Ubsan.M.loaded_segments (0x19430 : word) = Some W_19430.
Proof. vm_refl. Qed.
Lemma D_19430 : decode_any W_19430 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19434 : bv 32 := 0x0084b583.
Lemma F_19434 : fetch_word Ubsan.M.loaded_segments (0x19434 : word) = Some W_19434.
Proof. vm_refl. Qed.
Lemma D_19434 : decode_any W_19434 = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19438 : bv 32 := 0x000580e7.
Lemma F_19438 : fetch_word Ubsan.M.loaded_segments (0x19438 : word) = Some W_19438.
Proof. vm_refl. Qed.
Lemma D_19438 : decode_any W_19438 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1943c : bv 32 := 0x02843503.
Lemma F_1943c : fetch_word Ubsan.M.loaded_segments (0x1943c : word) = Some W_1943c.
Proof. vm_refl. Qed.
Lemma D_1943c : decode_any W_1943c = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19440 : bv 32 := 0x00050463.
Lemma F_19440 : fetch_word Ubsan.M.loaded_segments (0x19440 : word) = Some W_19440.
Proof. vm_refl. Qed.
Lemma D_19440 : decode_any W_19440 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19444 : bv 32 := 0x5ed220ef.
Lemma F_19444 : fetch_word Ubsan.M.loaded_segments (0x19444 : word) = Some W_19444.
Proof. vm_refl. Qed.
Lemma D_19444 : decode_any W_19444 = Some (Jal 1 142828, 4%Z).
Proof. vm_refl. Qed.

Definition W_19448 : bv 32 := 0x03043503.
Lemma F_19448 : fetch_word Ubsan.M.loaded_segments (0x19448 : word) = Some W_19448.
Proof. vm_refl. Qed.
Lemma D_19448 : decode_any W_19448 = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1944c : bv 32 := 0x00a13023.
Lemma F_1944c : fetch_word Ubsan.M.loaded_segments (0x1944c : word) = Some W_1944c.
Proof. vm_refl. Qed.
Lemma D_1944c : decode_any W_1944c = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19450 : bv 32 := 0x00050863.
Lemma F_19450 : fetch_word Ubsan.M.loaded_segments (0x19450 : word) = Some W_19450.
Proof. vm_refl. Qed.
Lemma D_19450 : decode_any W_19450 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19454 : bv 32 := 0x00010513.
Lemma F_19454 : fetch_word Ubsan.M.loaded_segments (0x19454 : word) = Some W_19454.
Proof. vm_refl. Qed.
Lemma D_19454 : decode_any W_19454 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19458 : bv 32 := 0x5f4040ef.
Lemma F_19458 : fetch_word Ubsan.M.loaded_segments (0x19458 : word) = Some W_19458.
Proof. vm_refl. Qed.
Lemma D_19458 : decode_any W_19458 = Some (Jal 1 17908, 4%Z).
Proof. vm_refl. Qed.

Definition W_1945c : bv 32 := 0x02043823.
Lemma F_1945c : fetch_word Ubsan.M.loaded_segments (0x1945c : word) = Some W_1945c.
Proof. vm_refl. Qed.
Lemma D_1945c : decode_any W_1945c = Some (Store SZ8 8 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_19460 : bv 32 := 0x00040513.
Lemma F_19460 : fetch_word Ubsan.M.loaded_segments (0x19460 : word) = Some W_19460.
Proof. vm_refl. Qed.
Lemma D_19460 : decode_any W_19460 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19464 : bv 32 := 0x5cd220ef.
Lemma F_19464 : fetch_word Ubsan.M.loaded_segments (0x19464 : word) = Some W_19464.
Proof. vm_refl. Qed.
Lemma D_19464 : decode_any W_19464 = Some (Jal 1 142796, 4%Z).
Proof. vm_refl. Qed.

Definition W_19468 : bv 32 := 0x0002c517.
Lemma F_19468 : fetch_word Ubsan.M.loaded_segments (0x19468 : word) = Some W_19468.
Proof. vm_refl. Qed.
Lemma D_19468 : decode_any W_19468 = Some (Auipc 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_1946c : bv 32 := 0xa3053503.
Lemma F_1946c : fetch_word Ubsan.M.loaded_segments (0x1946c : word) = Some W_1946c.
Proof. vm_refl. Qed.
Lemma D_1946c : decode_any W_1946c = Some (Load SZ8 true 10 10 2608, 4%Z).
Proof. vm_refl. Qed.

Definition W_19470 : bv 32 := 0x00052503.
Lemma F_19470 : fetch_word Ubsan.M.loaded_segments (0x19470 : word) = Some W_19470.
Proof. vm_refl. Qed.
Lemma D_19470 : decode_any W_19470 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19474 : bv 32 := 0x00500593.
Lemma F_19474 : fetch_word Ubsan.M.loaded_segments (0x19474 : word) = Some W_19474.
Proof. vm_refl. Qed.
Lemma D_19474 : decode_any W_19474 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_19478 : bv 32 := 0x02a5c263.
Lemma F_19478 : fetch_word Ubsan.M.loaded_segments (0x19478 : word) = Some W_19478.
Proof. vm_refl. Qed.
Lemma D_19478 : decode_any W_19478 = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_1947c : bv 32 := 0xffff9517.
Lemma F_1947c : fetch_word Ubsan.M.loaded_segments (0x1947c : word) = Some W_1947c.
Proof. vm_refl. Qed.
Lemma D_1947c : decode_any W_1947c = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_19480 : bv 32 := 0xffff7597.
Lemma F_19480 : fetch_word Ubsan.M.loaded_segments (0x19480 : word) = Some W_19480.
Proof. vm_refl. Qed.
Lemma D_19480 : decode_any W_19480 = Some (Auipc 11 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_19484 : bv 32 := 0x8c450513.
Lemma F_19484 : fetch_word Ubsan.M.loaded_segments (0x19484 : word) = Some W_19484.
Proof. vm_refl. Qed.
Lemma D_19484 : decode_any W_19484 = Some (OpImm ALU_ADD 10 10 2244, 4%Z).
Proof. vm_refl. Qed.

Definition W_19488 : bv 32 := 0x64258593.
Lemma F_19488 : fetch_word Ubsan.M.loaded_segments (0x19488 : word) = Some W_19488.
Proof. vm_refl. Qed.
Lemma D_19488 : decode_any W_19488 = Some (OpImm ALU_ADD 11 11 1602, 4%Z).
Proof. vm_refl. Qed.

Definition W_1948c : bv 32 := 0x00000613.
Lemma F_1948c : fetch_word Ubsan.M.loaded_segments (0x1948c : word) = Some W_1948c.
Proof. vm_refl. Qed.
Lemma D_1948c : decode_any W_1948c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19490 : bv 32 := 0xa35fe0ef.
Lemma F_19490 : fetch_word Ubsan.M.loaded_segments (0x19490 : word) = Some W_19490.
Proof. vm_refl. Qed.
Lemma D_19490 : decode_any W_19490 = Some (Jal 1 2091572, 4%Z).
Proof. vm_refl. Qed.

Definition W_19494 : bv 32 := 0x00050413.
Lemma F_19494 : fetch_word Ubsan.M.loaded_segments (0x19494 : word) = Some W_19494.
Proof. vm_refl. Qed.
Lemma D_19494 : decode_any W_19494 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19498 : bv 32 := 0x0080006f.
Lemma F_19498 : fetch_word Ubsan.M.loaded_segments (0x19498 : word) = Some W_19498.
Proof. vm_refl. Qed.
Lemma D_19498 : decode_any W_19498 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1949c : bv 32 := 0x00000413.
Lemma F_1949c : fetch_word Ubsan.M.loaded_segments (0x1949c : word) = Some W_1949c.
Proof. vm_refl. Qed.
Lemma D_1949c : decode_any W_1949c = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_194a0 : bv 32 := 0x00040513.
Lemma F_194a0 : fetch_word Ubsan.M.loaded_segments (0x194a0 : word) = Some W_194a0.
Proof. vm_refl. Qed.
Lemma D_194a0 : decode_any W_194a0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_194a4 : bv 32 := 0x01813083.
Lemma F_194a4 : fetch_word Ubsan.M.loaded_segments (0x194a4 : word) = Some W_194a4.
Proof. vm_refl. Qed.
Lemma D_194a4 : decode_any W_194a4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_194a8 : bv 32 := 0x01013403.
Lemma F_194a8 : fetch_word Ubsan.M.loaded_segments (0x194a8 : word) = Some W_194a8.
Proof. vm_refl. Qed.
Lemma D_194a8 : decode_any W_194a8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_194ac : bv 32 := 0x00813483.
Lemma F_194ac : fetch_word Ubsan.M.loaded_segments (0x194ac : word) = Some W_194ac.
Proof. vm_refl. Qed.
Lemma D_194ac : decode_any W_194ac = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_194b0 : bv 32 := 0x02010113.
Lemma F_194b0 : fetch_word Ubsan.M.loaded_segments (0x194b0 : word) = Some W_194b0.
Proof. vm_refl. Qed.
Lemma D_194b0 : decode_any W_194b0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_194b4 : bv 32 := 0x00008067.
Lemma F_194b4 : fetch_word Ubsan.M.loaded_segments (0x194b4 : word) = Some W_194b4.
Proof. vm_refl. Qed.
Lemma D_194b4 : decode_any W_194b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_194b8 : bv 32 := 0xc0001073.
Lemma F_194b8 : fetch_word Ubsan.M.loaded_segments (0x194b8 : word) = Some W_194b8.
Proof. vm_refl. Qed.
Lemma D_194b8 : decode_any W_194b8 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
