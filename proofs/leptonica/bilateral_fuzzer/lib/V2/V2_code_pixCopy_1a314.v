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

Definition W_1a314 : bv 32 := 0xfd010113.
Lemma F_1a314 : fetch_word Ubsan.M.loaded_segments (0x1a314 : word) = Some W_1a314.
Proof. vm_refl. Qed.
Lemma D_1a314 : decode_any W_1a314 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a318 : bv 32 := 0x02113423.
Lemma F_1a318 : fetch_word Ubsan.M.loaded_segments (0x1a318 : word) = Some W_1a318.
Proof. vm_refl. Qed.
Lemma D_1a318 : decode_any W_1a318 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a31c : bv 32 := 0x02813023.
Lemma F_1a31c : fetch_word Ubsan.M.loaded_segments (0x1a31c : word) = Some W_1a31c.
Proof. vm_refl. Qed.
Lemma D_1a31c : decode_any W_1a31c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a320 : bv 32 := 0x00913c23.
Lemma F_1a320 : fetch_word Ubsan.M.loaded_segments (0x1a320 : word) = Some W_1a320.
Proof. vm_refl. Qed.
Lemma D_1a320 : decode_any W_1a320 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a324 : bv 32 := 0x01213823.
Lemma F_1a324 : fetch_word Ubsan.M.loaded_segments (0x1a324 : word) = Some W_1a324.
Proof. vm_refl. Qed.
Lemma D_1a324 : decode_any W_1a324 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a328 : bv 32 := 0x01313423.
Lemma F_1a328 : fetch_word Ubsan.M.loaded_segments (0x1a328 : word) = Some W_1a328.
Proof. vm_refl. Qed.
Lemma D_1a328 : decode_any W_1a328 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a32c : bv 32 := 0x00050413.
Lemma F_1a32c : fetch_word Ubsan.M.loaded_segments (0x1a32c : word) = Some W_1a32c.
Proof. vm_refl. Qed.
Lemma D_1a32c : decode_any W_1a32c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a330 : bv 32 := 0x08058063.
Lemma F_1a330 : fetch_word Ubsan.M.loaded_segments (0x1a330 : word) = Some W_1a330.
Proof. vm_refl. Qed.
Lemma D_1a330 : decode_any W_1a330 = Some (Branch BC_EQ 11 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a334 : bv 32 := 0x00058493.
Lemma F_1a334 : fetch_word Ubsan.M.loaded_segments (0x1a334 : word) = Some W_1a334.
Proof. vm_refl. Qed.
Lemma D_1a334 : decode_any W_1a334 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a338 : bv 32 := 0x1e858e63.
Lemma F_1a338 : fetch_word Ubsan.M.loaded_segments (0x1a338 : word) = Some W_1a338.
Proof. vm_refl. Qed.
Lemma D_1a338 : decode_any W_1a338 = Some (Branch BC_EQ 11 8 508, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a33c : bv 32 := 0x0074f513.
Lemma F_1a33c : fetch_word Ubsan.M.loaded_segments (0x1a33c : word) = Some W_1a33c.
Proof. vm_refl. Qed.
Lemma D_1a33c : decode_any W_1a33c = Some (OpImm ALU_AND 10 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a340 : bv 32 := 0x20051a63.
Lemma F_1a340 : fetch_word Ubsan.M.loaded_segments (0x1a340 : word) = Some W_1a340.
Proof. vm_refl. Qed.
Lemma D_1a340 : decode_any W_1a340 = Some (Branch BC_NE 10 0 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a344 : bv 32 := 0x0104a503.
Lemma F_1a344 : fetch_word Ubsan.M.loaded_segments (0x1a344 : word) = Some W_1a344.
Proof. vm_refl. Qed.
Lemma D_1a344 : decode_any W_1a344 = Some (Load SZ4 true 10 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a348 : bv 32 := 0x200005b7.
Lemma F_1a348 : fetch_word Ubsan.M.loaded_segments (0x1a348 : word) = Some W_1a348.
Proof. vm_refl. Qed.
Lemma D_1a348 : decode_any W_1a348 = Some (Lui 11 131072, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a34c : bv 32 := 0x00b505b3.
Lemma F_1a34c : fetch_word Ubsan.M.loaded_segments (0x1a34c : word) = Some W_1a34c.
Proof. vm_refl. Qed.
Lemma D_1a34c : decode_any W_1a34c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a350 : bv 32 := 0x01e5d59b.
Lemma F_1a350 : fetch_word Ubsan.M.loaded_segments (0x1a350 : word) = Some W_1a350.
Proof. vm_refl. Qed.
Lemma D_1a350 : decode_any W_1a350 = Some (ShiftImm32 ALU_SRL 11 11 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a354 : bv 32 := 0x20059063.
Lemma F_1a354 : fetch_word Ubsan.M.loaded_segments (0x1a354 : word) = Some W_1a354.
Proof. vm_refl. Qed.
Lemma D_1a354 : decode_any W_1a354 = Some (Branch BC_NE 11 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a358 : bv 32 := 0x0044a583.
Lemma F_1a358 : fetch_word Ubsan.M.loaded_segments (0x1a358 : word) = Some W_1a358.
Proof. vm_refl. Qed.
Lemma D_1a358 : decode_any W_1a358 = Some (Load SZ4 true 11 9 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a35c : bv 32 := 0x0025151b.
Lemma F_1a35c : fetch_word Ubsan.M.loaded_segments (0x1a35c : word) = Some W_1a35c.
Proof. vm_refl. Qed.
Lemma D_1a35c : decode_any W_1a35c = Some (ShiftImm32 ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a360 : bv 32 := 0x02b50933.
Lemma F_1a360 : fetch_word Ubsan.M.loaded_segments (0x1a360 : word) = Some W_1a360.
Proof. vm_refl. Qed.
Lemma D_1a360 : decode_any W_1a360 = Some (Mul M_MUL 18 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a364 : bv 32 := 0x02b5053b.
Lemma F_1a364 : fetch_word Ubsan.M.loaded_segments (0x1a364 : word) = Some W_1a364.
Proof. vm_refl. Qed.
Lemma D_1a364 : decode_any W_1a364 = Some (Mul32 M_MUL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a368 : bv 32 := 0x1f251663.
Lemma F_1a368 : fetch_word Ubsan.M.loaded_segments (0x1a368 : word) = Some W_1a368.
Proof. vm_refl. Qed.
Lemma D_1a368 : decode_any W_1a368 = Some (Branch BC_NE 10 18 492, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a36c : bv 32 := 0x08040463.
Lemma F_1a36c : fetch_word Ubsan.M.loaded_segments (0x1a36c : word) = Some W_1a36c.
Proof. vm_refl. Qed.
Lemma D_1a36c : decode_any W_1a36c = Some (Branch BC_EQ 8 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a370 : bv 32 := 0x00040513.
Lemma F_1a370 : fetch_word Ubsan.M.loaded_segments (0x1a370 : word) = Some W_1a370.
Proof. vm_refl. Qed.
Lemma D_1a370 : decode_any W_1a370 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a374 : bv 32 := 0x00048593.
Lemma F_1a374 : fetch_word Ubsan.M.loaded_segments (0x1a374 : word) = Some W_1a374.
Proof. vm_refl. Qed.
Lemma D_1a374 : decode_any W_1a374 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a378 : bv 32 := 0x22c000ef.
Lemma F_1a378 : fetch_word Ubsan.M.loaded_segments (0x1a378 : word) = Some W_1a378.
Proof. vm_refl. Qed.
Lemma D_1a378 : decode_any W_1a378 = Some (Jal 1 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a37c : bv 32 := 0x00100593.
Lemma F_1a37c : fetch_word Ubsan.M.loaded_segments (0x1a37c : word) = Some W_1a37c.
Proof. vm_refl. Qed.
Lemma D_1a37c : decode_any W_1a37c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a380 : bv 32 := 0x0cb51063.
Lemma F_1a380 : fetch_word Ubsan.M.loaded_segments (0x1a380 : word) = Some W_1a380.
Proof. vm_refl. Qed.
Lemma D_1a380 : decode_any W_1a380 = Some (Branch BC_NE 10 11 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a384 : bv 32 := 0x0002b517.
Lemma F_1a384 : fetch_word Ubsan.M.loaded_segments (0x1a384 : word) = Some W_1a384.
Proof. vm_refl. Qed.
Lemma D_1a384 : decode_any W_1a384 = Some (Auipc 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a388 : bv 32 := 0xb1453503.
Lemma F_1a388 : fetch_word Ubsan.M.loaded_segments (0x1a388 : word) = Some W_1a388.
Proof. vm_refl. Qed.
Lemma D_1a388 : decode_any W_1a388 = Some (Load SZ8 true 10 10 2836, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a38c : bv 32 := 0x00052503.
Lemma F_1a38c : fetch_word Ubsan.M.loaded_segments (0x1a38c : word) = Some W_1a38c.
Proof. vm_refl. Qed.
Lemma D_1a38c : decode_any W_1a38c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a390 : bv 32 := 0x00500593.
Lemma F_1a390 : fetch_word Ubsan.M.loaded_segments (0x1a390 : word) = Some W_1a390.
Proof. vm_refl. Qed.
Lemma D_1a390 : decode_any W_1a390 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a394 : bv 32 := 0x18a5ce63.
Lemma F_1a394 : fetch_word Ubsan.M.loaded_segments (0x1a394 : word) = Some W_1a394.
Proof. vm_refl. Qed.
Lemma D_1a394 : decode_any W_1a394 = Some (Branch BC_LT 11 10 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a398 : bv 32 := 0xffff7517.
Lemma F_1a398 : fetch_word Ubsan.M.loaded_segments (0x1a398 : word) = Some W_1a398.
Proof. vm_refl. Qed.
Lemma D_1a398 : decode_any W_1a398 = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a39c : bv 32 := 0xffff7597.
Lemma F_1a39c : fetch_word Ubsan.M.loaded_segments (0x1a39c : word) = Some W_1a39c.
Proof. vm_refl. Qed.
Lemma D_1a39c : decode_any W_1a39c = Some (Auipc 11 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3a0 : bv 32 := 0xec150513.
Lemma F_1a3a0 : fetch_word Ubsan.M.loaded_segments (0x1a3a0 : word) = Some W_1a3a0.
Proof. vm_refl. Qed.
Lemma D_1a3a0 : decode_any W_1a3a0 = Some (OpImm ALU_ADD 10 10 3777, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3a4 : bv 32 := 0x39f58593.
Lemma F_1a3a4 : fetch_word Ubsan.M.loaded_segments (0x1a3a4 : word) = Some W_1a3a4.
Proof. vm_refl. Qed.
Lemma D_1a3a4 : decode_any W_1a3a4 = Some (OpImm ALU_ADD 11 11 927, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3a8 : bv 32 := 0x00000613.
Lemma F_1a3a8 : fetch_word Ubsan.M.loaded_segments (0x1a3a8 : word) = Some W_1a3a8.
Proof. vm_refl. Qed.
Lemma D_1a3a8 : decode_any W_1a3a8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3ac : bv 32 := 0x02c0006f.
Lemma F_1a3ac : fetch_word Ubsan.M.loaded_segments (0x1a3ac : word) = Some W_1a3ac.
Proof. vm_refl. Qed.
Lemma D_1a3ac : decode_any W_1a3ac = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3b0 : bv 32 := 0x0002b517.
Lemma F_1a3b0 : fetch_word Ubsan.M.loaded_segments (0x1a3b0 : word) = Some W_1a3b0.
Proof. vm_refl. Qed.
Lemma D_1a3b0 : decode_any W_1a3b0 = Some (Auipc 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3b4 : bv 32 := 0xae853503.
Lemma F_1a3b4 : fetch_word Ubsan.M.loaded_segments (0x1a3b4 : word) = Some W_1a3b4.
Proof. vm_refl. Qed.
Lemma D_1a3b4 : decode_any W_1a3b4 = Some (Load SZ8 true 10 10 2792, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3b8 : bv 32 := 0x00052503.
Lemma F_1a3b8 : fetch_word Ubsan.M.loaded_segments (0x1a3b8 : word) = Some W_1a3b8.
Proof. vm_refl. Qed.
Lemma D_1a3b8 : decode_any W_1a3b8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3bc : bv 32 := 0x00500593.
Lemma F_1a3bc : fetch_word Ubsan.M.loaded_segments (0x1a3bc : word) = Some W_1a3bc.
Proof. vm_refl. Qed.
Lemma D_1a3bc : decode_any W_1a3bc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3c0 : bv 32 := 0x16a5ca63.
Lemma F_1a3c0 : fetch_word Ubsan.M.loaded_segments (0x1a3c0 : word) = Some W_1a3c0.
Proof. vm_refl. Qed.
Lemma D_1a3c0 : decode_any W_1a3c0 = Some (Branch BC_LT 11 10 372, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3c4 : bv 32 := 0xffff6517.
Lemma F_1a3c4 : fetch_word Ubsan.M.loaded_segments (0x1a3c4 : word) = Some W_1a3c4.
Proof. vm_refl. Qed.
Lemma D_1a3c4 : decode_any W_1a3c4 = Some (Auipc 10 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3c8 : bv 32 := 0xffff7597.
Lemma F_1a3c8 : fetch_word Ubsan.M.loaded_segments (0x1a3c8 : word) = Some W_1a3c8.
Proof. vm_refl. Qed.
Lemma D_1a3c8 : decode_any W_1a3c8 = Some (Auipc 11 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3cc : bv 32 := 0xef050513.
Lemma F_1a3cc : fetch_word Ubsan.M.loaded_segments (0x1a3cc : word) = Some W_1a3cc.
Proof. vm_refl. Qed.
Lemma D_1a3cc : decode_any W_1a3cc = Some (OpImm ALU_ADD 10 10 3824, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3d0 : bv 32 := 0x37358593.
Lemma F_1a3d0 : fetch_word Ubsan.M.loaded_segments (0x1a3d0 : word) = Some W_1a3d0.
Proof. vm_refl. Qed.
Lemma D_1a3d0 : decode_any W_1a3d0 = Some (OpImm ALU_ADD 11 11 883, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3d4 : bv 32 := 0x00040613.
Lemma F_1a3d4 : fetch_word Ubsan.M.loaded_segments (0x1a3d4 : word) = Some W_1a3d4.
Proof. vm_refl. Qed.
Lemma D_1a3d4 : decode_any W_1a3d4 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3d8 : bv 32 := 0x02813083.
Lemma F_1a3d8 : fetch_word Ubsan.M.loaded_segments (0x1a3d8 : word) = Some W_1a3d8.
Proof. vm_refl. Qed.
Lemma D_1a3d8 : decode_any W_1a3d8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3dc : bv 32 := 0x02013403.
Lemma F_1a3dc : fetch_word Ubsan.M.loaded_segments (0x1a3dc : word) = Some W_1a3dc.
Proof. vm_refl. Qed.
Lemma D_1a3dc : decode_any W_1a3dc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3e0 : bv 32 := 0x01813483.
Lemma F_1a3e0 : fetch_word Ubsan.M.loaded_segments (0x1a3e0 : word) = Some W_1a3e0.
Proof. vm_refl. Qed.
Lemma D_1a3e0 : decode_any W_1a3e0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3e4 : bv 32 := 0x01013903.
Lemma F_1a3e4 : fetch_word Ubsan.M.loaded_segments (0x1a3e4 : word) = Some W_1a3e4.
Proof. vm_refl. Qed.
Lemma D_1a3e4 : decode_any W_1a3e4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3e8 : bv 32 := 0x00813983.
Lemma F_1a3e8 : fetch_word Ubsan.M.loaded_segments (0x1a3e8 : word) = Some W_1a3e8.
Proof. vm_refl. Qed.
Lemma D_1a3e8 : decode_any W_1a3e8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3ec : bv 32 := 0x03010113.
Lemma F_1a3ec : fetch_word Ubsan.M.loaded_segments (0x1a3ec : word) = Some W_1a3ec.
Proof. vm_refl. Qed.
Lemma D_1a3ec : decode_any W_1a3ec = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3f0 : bv 32 := 0xad5fd06f.
Lemma F_1a3f0 : fetch_word Ubsan.M.loaded_segments (0x1a3f0 : word) = Some W_1a3f0.
Proof. vm_refl. Qed.
Lemma D_1a3f0 : decode_any W_1a3f0 = Some (Jal 0 2087636, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3f4 : bv 32 := 0x00048513.
Lemma F_1a3f4 : fetch_word Ubsan.M.loaded_segments (0x1a3f4 : word) = Some W_1a3f4.
Proof. vm_refl. Qed.
Lemma D_1a3f4 : decode_any W_1a3f4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3f8 : bv 32 := 0xde4ff0ef.
Lemma F_1a3f8 : fetch_word Ubsan.M.loaded_segments (0x1a3f8 : word) = Some W_1a3f8.
Proof. vm_refl. Qed.
Lemma D_1a3f8 : decode_any W_1a3f8 = Some (Jal 1 2094564, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a3fc : bv 32 := 0x06050463.
Lemma F_1a3fc : fetch_word Ubsan.M.loaded_segments (0x1a3fc : word) = Some W_1a3fc.
Proof. vm_refl. Qed.
Lemma D_1a3fc : decode_any W_1a3fc = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a400 : bv 32 := 0x00050413.
Lemma F_1a400 : fetch_word Ubsan.M.loaded_segments (0x1a400 : word) = Some W_1a400.
Proof. vm_refl. Qed.
Lemma D_1a400 : decode_any W_1a400 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a404 : bv 32 := 0x00757513.
Lemma F_1a404 : fetch_word Ubsan.M.loaded_segments (0x1a404 : word) = Some W_1a404.
Proof. vm_refl. Qed.
Lemma D_1a404 : decode_any W_1a404 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a408 : bv 32 := 0x14051663.
Lemma F_1a408 : fetch_word Ubsan.M.loaded_segments (0x1a408 : word) = Some W_1a408.
Proof. vm_refl. Qed.
Lemma D_1a408 : decode_any W_1a408 = Some (Branch BC_NE 10 0 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a40c : bv 32 := 0x01046503.
Lemma F_1a40c : fetch_word Ubsan.M.loaded_segments (0x1a40c : word) = Some W_1a40c.
Proof. vm_refl. Qed.
Lemma D_1a40c : decode_any W_1a40c = Some (Load SZ4 false 10 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a410 : bv 32 := 0x00446583.
Lemma F_1a410 : fetch_word Ubsan.M.loaded_segments (0x1a410 : word) = Some W_1a410.
Proof. vm_refl. Qed.
Lemma D_1a410 : decode_any W_1a410 = Some (Load SZ4 false 11 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a414 : bv 32 := 0x00251513.
Lemma F_1a414 : fetch_word Ubsan.M.loaded_segments (0x1a414 : word) = Some W_1a414.
Proof. vm_refl. Qed.
Lemma D_1a414 : decode_any W_1a414 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a418 : bv 32 := 0x02b516b3.
Lemma F_1a418 : fetch_word Ubsan.M.loaded_segments (0x1a418 : word) = Some W_1a418.
Proof. vm_refl. Qed.
Lemma D_1a418 : decode_any W_1a418 = Some (Mul M_MULH 13 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a41c : bv 32 := 0x02b50633.
Lemma F_1a41c : fetch_word Ubsan.M.loaded_segments (0x1a41c : word) = Some W_1a41c.
Proof. vm_refl. Qed.
Lemma D_1a41c : decode_any W_1a41c = Some (Mul M_MUL 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a420 : bv 32 := 0x43f65513.
Lemma F_1a420 : fetch_word Ubsan.M.loaded_segments (0x1a420 : word) = Some W_1a420.
Proof. vm_refl. Qed.
Lemma D_1a420 : decode_any W_1a420 = Some (ShiftImm ALU_SRA 10 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a424 : bv 32 := 0x12a69863.
Lemma F_1a424 : fetch_word Ubsan.M.loaded_segments (0x1a424 : word) = Some W_1a424.
Proof. vm_refl. Qed.
Lemma D_1a424 : decode_any W_1a424 = Some (Branch BC_NE 13 10 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a428 : bv 32 := 0x03843503.
Lemma F_1a428 : fetch_word Ubsan.M.loaded_segments (0x1a428 : word) = Some W_1a428.
Proof. vm_refl. Qed.
Lemma D_1a428 : decode_any W_1a428 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a42c : bv 32 := 0x00000593.
Lemma F_1a42c : fetch_word Ubsan.M.loaded_segments (0x1a42c : word) = Some W_1a42c.
Proof. vm_refl. Qed.
Lemma D_1a42c : decode_any W_1a42c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a430 : bv 32 := 0x450290ef.
Lemma F_1a430 : fetch_word Ubsan.M.loaded_segments (0x1a430 : word) = Some W_1a430.
Proof. vm_refl. Qed.
Lemma D_1a430 : decode_any W_1a430 = Some (Jal 1 169040, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a434 : bv 32 := 0x00747513.
Lemma F_1a434 : fetch_word Ubsan.M.loaded_segments (0x1a434 : word) = Some W_1a434.
Proof. vm_refl. Qed.
Lemma D_1a434 : decode_any W_1a434 = Some (OpImm ALU_AND 10 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a438 : bv 32 := 0x0a050c63.
Lemma F_1a438 : fetch_word Ubsan.M.loaded_segments (0x1a438 : word) = Some W_1a438.
Proof. vm_refl. Qed.
Lemma D_1a438 : decode_any W_1a438 = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a43c : bv 32 := 0x1180006f.
Lemma F_1a43c : fetch_word Ubsan.M.loaded_segments (0x1a43c : word) = Some W_1a43c.
Proof. vm_refl. Qed.
Lemma D_1a43c : decode_any W_1a43c = Some (Jal 0 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a440 : bv 32 := 0x00040513.
Lemma F_1a440 : fetch_word Ubsan.M.loaded_segments (0x1a440 : word) = Some W_1a440.
Proof. vm_refl. Qed.
Lemma D_1a440 : decode_any W_1a440 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a444 : bv 32 := 0x00048593.
Lemma F_1a444 : fetch_word Ubsan.M.loaded_segments (0x1a444 : word) = Some W_1a444.
Proof. vm_refl. Qed.
Lemma D_1a444 : decode_any W_1a444 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a448 : bv 32 := 0x83dff0ef.
Lemma F_1a448 : fetch_word Ubsan.M.loaded_segments (0x1a448 : word) = Some W_1a448.
Proof. vm_refl. Qed.
Lemma D_1a448 : decode_any W_1a448 = Some (Jal 1 2095164, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a44c : bv 32 := 0x00c4a503.
Lemma F_1a44c : fetch_word Ubsan.M.loaded_segments (0x1a44c : word) = Some W_1a44c.
Proof. vm_refl. Qed.
Lemma D_1a44c : decode_any W_1a44c = Some (Load SZ4 true 10 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a450 : bv 32 := 0x00747993.
Lemma F_1a450 : fetch_word Ubsan.M.loaded_segments (0x1a450 : word) = Some W_1a450.
Proof. vm_refl. Qed.
Lemma D_1a450 : decode_any W_1a450 = Some (OpImm ALU_AND 19 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a454 : bv 32 := 0x04a05863.
Lemma F_1a454 : fetch_word Ubsan.M.loaded_segments (0x1a454 : word) = Some W_1a454.
Proof. vm_refl. Qed.
Lemma D_1a454 : decode_any W_1a454 = Some (Branch BC_GE 0 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a458 : bv 32 := 0x0e099e63.
Lemma F_1a458 : fetch_word Ubsan.M.loaded_segments (0x1a458 : word) = Some W_1a458.
Proof. vm_refl. Qed.
Lemma D_1a458 : decode_any W_1a458 = Some (Branch BC_NE 19 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a45c : bv 32 := 0x00a42623.
Lemma F_1a45c : fetch_word Ubsan.M.loaded_segments (0x1a45c : word) = Some W_1a45c.
Proof. vm_refl. Qed.
Lemma D_1a45c : decode_any W_1a45c = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a460 : bv 32 := 0x0700006f.
Lemma F_1a460 : fetch_word Ubsan.M.loaded_segments (0x1a460 : word) = Some W_1a460.
Proof. vm_refl. Qed.
Lemma D_1a460 : decode_any W_1a460 = Some (Jal 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a464 : bv 32 := 0x0002b517.
Lemma F_1a464 : fetch_word Ubsan.M.loaded_segments (0x1a464 : word) = Some W_1a464.
Proof. vm_refl. Qed.
Lemma D_1a464 : decode_any W_1a464 = Some (Auipc 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a468 : bv 32 := 0xa3453983.
Lemma F_1a468 : fetch_word Ubsan.M.loaded_segments (0x1a468 : word) = Some W_1a468.
Proof. vm_refl. Qed.
Lemma D_1a468 : decode_any W_1a468 = Some (Load SZ8 true 19 10 2612, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a46c : bv 32 := 0x0009a503.
Lemma F_1a46c : fetch_word Ubsan.M.loaded_segments (0x1a46c : word) = Some W_1a46c.
Proof. vm_refl. Qed.
Lemma D_1a46c : decode_any W_1a46c = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a470 : bv 32 := 0x00600593.
Lemma F_1a470 : fetch_word Ubsan.M.loaded_segments (0x1a470 : word) = Some W_1a470.
Proof. vm_refl. Qed.
Lemma D_1a470 : decode_any W_1a470 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a474 : bv 32 := 0x0ab55e63.
Lemma F_1a474 : fetch_word Ubsan.M.loaded_segments (0x1a474 : word) = Some W_1a474.
Proof. vm_refl. Qed.
Lemma D_1a474 : decode_any W_1a474 = Some (Branch BC_GE 10 11 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a478 : bv 32 := 0xffff6517.
Lemma F_1a478 : fetch_word Ubsan.M.loaded_segments (0x1a478 : word) = Some W_1a478.
Proof. vm_refl. Qed.
Lemma D_1a478 : decode_any W_1a478 = Some (Auipc 10 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a47c : bv 32 := 0xffff7597.
Lemma F_1a47c : fetch_word Ubsan.M.loaded_segments (0x1a47c : word) = Some W_1a47c.
Proof. vm_refl. Qed.
Lemma D_1a47c : decode_any W_1a47c = Some (Auipc 11 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a480 : bv 32 := 0x2ed50513.
Lemma F_1a480 : fetch_word Ubsan.M.loaded_segments (0x1a480 : word) = Some W_1a480.
Proof. vm_refl. Qed.
Lemma D_1a480 : decode_any W_1a480 = Some (OpImm ALU_ADD 10 10 749, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a484 : bv 32 := 0x36c58593.
Lemma F_1a484 : fetch_word Ubsan.M.loaded_segments (0x1a484 : word) = Some W_1a484.
Proof. vm_refl. Qed.
Lemma D_1a484 : decode_any W_1a484 = Some (OpImm ALU_ADD 11 11 876, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a488 : bv 32 := 0x00000613.
Lemma F_1a488 : fetch_word Ubsan.M.loaded_segments (0x1a488 : word) = Some W_1a488.
Proof. vm_refl. Qed.
Lemma D_1a488 : decode_any W_1a488 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a48c : bv 32 := 0xa39fd0ef.
Lemma F_1a48c : fetch_word Ubsan.M.loaded_segments (0x1a48c : word) = Some W_1a48c.
Proof. vm_refl. Qed.
Lemma D_1a48c : decode_any W_1a48c = Some (Jal 1 2087480, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a490 : bv 32 := 0x08050063.
Lemma F_1a490 : fetch_word Ubsan.M.loaded_segments (0x1a490 : word) = Some W_1a490.
Proof. vm_refl. Qed.
Lemma D_1a490 : decode_any W_1a490 = Some (Branch BC_EQ 10 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a494 : bv 32 := 0x00050413.
Lemma F_1a494 : fetch_word Ubsan.M.loaded_segments (0x1a494 : word) = Some W_1a494.
Proof. vm_refl. Qed.
Lemma D_1a494 : decode_any W_1a494 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a498 : bv 32 := 0x00757513.
Lemma F_1a498 : fetch_word Ubsan.M.loaded_segments (0x1a498 : word) = Some W_1a498.
Proof. vm_refl. Qed.
Lemma D_1a498 : decode_any W_1a498 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a49c : bv 32 := 0x04050a63.
Lemma F_1a49c : fetch_word Ubsan.M.loaded_segments (0x1a49c : word) = Some W_1a49c.
Proof. vm_refl. Qed.
Lemma D_1a49c : decode_any W_1a49c = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4a0 : bv 32 := 0x0b40006f.
Lemma F_1a4a0 : fetch_word Ubsan.M.loaded_segments (0x1a4a0 : word) = Some W_1a4a0.
Proof. vm_refl. Qed.
Lemma D_1a4a0 : decode_any W_1a4a0 = Some (Jal 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4a4 : bv 32 := 0x0002b517.
Lemma F_1a4a4 : fetch_word Ubsan.M.loaded_segments (0x1a4a4 : word) = Some W_1a4a4.
Proof. vm_refl. Qed.
Lemma D_1a4a4 : decode_any W_1a4a4 = Some (Auipc 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4a8 : bv 32 := 0x9f453503.
Lemma F_1a4a8 : fetch_word Ubsan.M.loaded_segments (0x1a4a8 : word) = Some W_1a4a8.
Proof. vm_refl. Qed.
Lemma D_1a4a8 : decode_any W_1a4a8 = Some (Load SZ8 true 10 10 2548, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4ac : bv 32 := 0x00052503.
Lemma F_1a4ac : fetch_word Ubsan.M.loaded_segments (0x1a4ac : word) = Some W_1a4ac.
Proof. vm_refl. Qed.
Lemma D_1a4ac : decode_any W_1a4ac = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4b0 : bv 32 := 0x00500593.
Lemma F_1a4b0 : fetch_word Ubsan.M.loaded_segments (0x1a4b0 : word) = Some W_1a4b0.
Proof. vm_refl. Qed.
Lemma D_1a4b0 : decode_any W_1a4b0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4b4 : bv 32 := 0x00a5ce63.
Lemma F_1a4b4 : fetch_word Ubsan.M.loaded_segments (0x1a4b4 : word) = Some W_1a4b4.
Proof. vm_refl. Qed.
Lemma D_1a4b4 : decode_any W_1a4b4 = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4b8 : bv 32 := 0xffff6517.
Lemma F_1a4b8 : fetch_word Ubsan.M.loaded_segments (0x1a4b8 : word) = Some W_1a4b8.
Proof. vm_refl. Qed.
Lemma D_1a4b8 : decode_any W_1a4b8 = Some (Auipc 10 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4bc : bv 32 := 0xffff8597.
Lemma F_1a4bc : fetch_word Ubsan.M.loaded_segments (0x1a4bc : word) = Some W_1a4bc.
Proof. vm_refl. Qed.
Lemma D_1a4bc : decode_any W_1a4bc = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4c0 : bv 32 := 0x5ad50513.
Lemma F_1a4c0 : fetch_word Ubsan.M.loaded_segments (0x1a4c0 : word) = Some W_1a4c0.
Proof. vm_refl. Qed.
Lemma D_1a4c0 : decode_any W_1a4c0 = Some (OpImm ALU_ADD 10 10 1453, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4c4 : bv 32 := 0xe6b58593.
Lemma F_1a4c4 : fetch_word Ubsan.M.loaded_segments (0x1a4c4 : word) = Some W_1a4c4.
Proof. vm_refl. Qed.
Lemma D_1a4c4 : decode_any W_1a4c4 = Some (OpImm ALU_ADD 11 11 3691, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4c8 : bv 32 := 0x00100613.
Lemma F_1a4c8 : fetch_word Ubsan.M.loaded_segments (0x1a4c8 : word) = Some W_1a4c8.
Proof. vm_refl. Qed.
Lemma D_1a4c8 : decode_any W_1a4c8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4cc : bv 32 := 0x929fd0ef.
Lemma F_1a4cc : fetch_word Ubsan.M.loaded_segments (0x1a4cc : word) = Some W_1a4cc.
Proof. vm_refl. Qed.
Lemma D_1a4cc : decode_any W_1a4cc = Some (Jal 1 2087208, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4d0 : bv 32 := 0x08099263.
Lemma F_1a4d0 : fetch_word Ubsan.M.loaded_segments (0x1a4d0 : word) = Some W_1a4d0.
Proof. vm_refl. Qed.
Lemma D_1a4d0 : decode_any W_1a4d0 = Some (Branch BC_NE 19 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4d4 : bv 32 := 0x0184b503.
Lemma F_1a4d4 : fetch_word Ubsan.M.loaded_segments (0x1a4d4 : word) = Some W_1a4d4.
Proof. vm_refl. Qed.
Lemma D_1a4d4 : decode_any W_1a4d4 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4d8 : bv 32 := 0x00a43c23.
Lemma F_1a4d8 : fetch_word Ubsan.M.loaded_segments (0x1a4d8 : word) = Some W_1a4d8.
Proof. vm_refl. Qed.
Lemma D_1a4d8 : decode_any W_1a4d8 = Some (Store SZ8 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4dc : bv 32 := 0x0204a503.
Lemma F_1a4dc : fetch_word Ubsan.M.loaded_segments (0x1a4dc : word) = Some W_1a4dc.
Proof. vm_refl. Qed.
Lemma D_1a4dc : decode_any W_1a4dc = Some (Load SZ4 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4e0 : bv 32 := 0x0284b583.
Lemma F_1a4e0 : fetch_word Ubsan.M.loaded_segments (0x1a4e0 : word) = Some W_1a4e0.
Proof. vm_refl. Qed.
Lemma D_1a4e0 : decode_any W_1a4e0 = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4e4 : bv 32 := 0x02a42023.
Lemma F_1a4e4 : fetch_word Ubsan.M.loaded_segments (0x1a4e4 : word) = Some W_1a4e4.
Proof. vm_refl. Qed.
Lemma D_1a4e4 : decode_any W_1a4e4 = Some (Store SZ4 8 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4e8 : bv 32 := 0x02840513.
Lemma F_1a4e8 : fetch_word Ubsan.M.loaded_segments (0x1a4e8 : word) = Some W_1a4e8.
Proof. vm_refl. Qed.
Lemma D_1a4e8 : decode_any W_1a4e8 = Some (OpImm ALU_ADD 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4ec : bv 32 := 0xb79fd0ef.
Lemma F_1a4ec : fetch_word Ubsan.M.loaded_segments (0x1a4ec : word) = Some W_1a4ec.
Proof. vm_refl. Qed.
Lemma D_1a4ec : decode_any W_1a4ec = Some (Jal 1 2087800, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4f0 : bv 32 := 0x03843503.
Lemma F_1a4f0 : fetch_word Ubsan.M.loaded_segments (0x1a4f0 : word) = Some W_1a4f0.
Proof. vm_refl. Qed.
Lemma D_1a4f0 : decode_any W_1a4f0 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4f4 : bv 32 := 0x0384b583.
Lemma F_1a4f4 : fetch_word Ubsan.M.loaded_segments (0x1a4f4 : word) = Some W_1a4f4.
Proof. vm_refl. Qed.
Lemma D_1a4f4 : decode_any W_1a4f4 = Some (Load SZ8 true 11 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4f8 : bv 32 := 0x00b56633.
Lemma F_1a4f8 : fetch_word Ubsan.M.loaded_segments (0x1a4f8 : word) = Some W_1a4f8.
Proof. vm_refl. Qed.
Lemma D_1a4f8 : decode_any W_1a4f8 = Some (Op ALU_OR 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a4fc : bv 32 := 0x00367613.
Lemma F_1a4fc : fetch_word Ubsan.M.loaded_segments (0x1a4fc : word) = Some W_1a4fc.
Proof. vm_refl. Qed.
Lemma D_1a4fc : decode_any W_1a4fc = Some (OpImm ALU_AND 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a500 : bv 32 := 0x04061a63.
Lemma F_1a500 : fetch_word Ubsan.M.loaded_segments (0x1a500 : word) = Some W_1a500.
Proof. vm_refl. Qed.
Lemma D_1a500 : decode_any W_1a500 = Some (Branch BC_NE 12 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a504 : bv 32 := 0x0009061b.
Lemma F_1a504 : fetch_word Ubsan.M.loaded_segments (0x1a504 : word) = Some W_1a504.
Proof. vm_refl. Qed.
Lemma D_1a504 : decode_any W_1a504 = Some (OpImm32 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a508 : bv 32 := 0x775280ef.
Lemma F_1a508 : fetch_word Ubsan.M.loaded_segments (0x1a508 : word) = Some W_1a508.
Proof. vm_refl. Qed.
Lemma D_1a508 : decode_any W_1a508 = Some (Jal 1 167796, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a50c : bv 32 := 0x0280006f.
Lemma F_1a50c : fetch_word Ubsan.M.loaded_segments (0x1a50c : word) = Some W_1a50c.
Proof. vm_refl. Qed.
Lemma D_1a50c : decode_any W_1a50c = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a510 : bv 32 := 0x0009a503.
Lemma F_1a510 : fetch_word Ubsan.M.loaded_segments (0x1a510 : word) = Some W_1a510.
Proof. vm_refl. Qed.
Lemma D_1a510 : decode_any W_1a510 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a514 : bv 32 := 0x00500593.
Lemma F_1a514 : fetch_word Ubsan.M.loaded_segments (0x1a514 : word) = Some W_1a514.
Proof. vm_refl. Qed.
Lemma D_1a514 : decode_any W_1a514 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a518 : bv 32 := 0x00a5cc63.
Lemma F_1a518 : fetch_word Ubsan.M.loaded_segments (0x1a518 : word) = Some W_1a518.
Proof. vm_refl. Qed.
Lemma D_1a518 : decode_any W_1a518 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a51c : bv 32 := 0xffff6517.
Lemma F_1a51c : fetch_word Ubsan.M.loaded_segments (0x1a51c : word) = Some W_1a51c.
Proof. vm_refl. Qed.
Lemma D_1a51c : decode_any W_1a51c = Some (Auipc 10 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a520 : bv 32 := 0xffff7597.
Lemma F_1a520 : fetch_word Ubsan.M.loaded_segments (0x1a520 : word) = Some W_1a520.
Proof. vm_refl. Qed.
Lemma D_1a520 : decode_any W_1a520 = Some (Auipc 11 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a524 : bv 32 := 0x24950513.
Lemma F_1a524 : fetch_word Ubsan.M.loaded_segments (0x1a524 : word) = Some W_1a524.
Proof. vm_refl. Qed.
Lemma D_1a524 : decode_any W_1a524 = Some (OpImm ALU_ADD 10 10 585, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a528 : bv 32 := 0x21b58593.
Lemma F_1a528 : fetch_word Ubsan.M.loaded_segments (0x1a528 : word) = Some W_1a528.
Proof. vm_refl. Qed.
Lemma D_1a528 : decode_any W_1a528 = Some (OpImm ALU_ADD 11 11 539, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a52c : bv 32 := 0xe7dff06f.
Lemma F_1a52c : fetch_word Ubsan.M.loaded_segments (0x1a52c : word) = Some W_1a52c.
Proof. vm_refl. Qed.
Lemma D_1a52c : decode_any W_1a52c = Some (Jal 0 2096764, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a530 : bv 32 := 0x00000413.
Lemma F_1a530 : fetch_word Ubsan.M.loaded_segments (0x1a530 : word) = Some W_1a530.
Proof. vm_refl. Qed.
Lemma D_1a530 : decode_any W_1a530 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a534 : bv 32 := 0x00040513.
Lemma F_1a534 : fetch_word Ubsan.M.loaded_segments (0x1a534 : word) = Some W_1a534.
Proof. vm_refl. Qed.
Lemma D_1a534 : decode_any W_1a534 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a538 : bv 32 := 0x02813083.
Lemma F_1a538 : fetch_word Ubsan.M.loaded_segments (0x1a538 : word) = Some W_1a538.
Proof. vm_refl. Qed.
Lemma D_1a538 : decode_any W_1a538 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a53c : bv 32 := 0x02013403.
Lemma F_1a53c : fetch_word Ubsan.M.loaded_segments (0x1a53c : word) = Some W_1a53c.
Proof. vm_refl. Qed.
Lemma D_1a53c : decode_any W_1a53c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a540 : bv 32 := 0x01813483.
Lemma F_1a540 : fetch_word Ubsan.M.loaded_segments (0x1a540 : word) = Some W_1a540.
Proof. vm_refl. Qed.
Lemma D_1a540 : decode_any W_1a540 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a544 : bv 32 := 0x01013903.
Lemma F_1a544 : fetch_word Ubsan.M.loaded_segments (0x1a544 : word) = Some W_1a544.
Proof. vm_refl. Qed.
Lemma D_1a544 : decode_any W_1a544 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a548 : bv 32 := 0x00813983.
Lemma F_1a548 : fetch_word Ubsan.M.loaded_segments (0x1a548 : word) = Some W_1a548.
Proof. vm_refl. Qed.
Lemma D_1a548 : decode_any W_1a548 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a54c : bv 32 := 0x03010113.
Lemma F_1a54c : fetch_word Ubsan.M.loaded_segments (0x1a54c : word) = Some W_1a54c.
Proof. vm_refl. Qed.
Lemma D_1a54c : decode_any W_1a54c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a550 : bv 32 := 0x00008067.
Lemma F_1a550 : fetch_word Ubsan.M.loaded_segments (0x1a550 : word) = Some W_1a550.
Proof. vm_refl. Qed.
Lemma D_1a550 : decode_any W_1a550 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a554 : bv 32 := 0xc0001073.
Lemma F_1a554 : fetch_word Ubsan.M.loaded_segments (0x1a554 : word) = Some W_1a554.
Proof. vm_refl. Qed.
Lemma D_1a554 : decode_any W_1a554 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
