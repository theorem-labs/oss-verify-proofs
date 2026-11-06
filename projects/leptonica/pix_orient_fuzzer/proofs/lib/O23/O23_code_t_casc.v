(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6d928 : bv 32 := 0x00050663.
Lemma F_6d928 : fetch_word Plain.M.loaded_segments (0x6d980 : word) = Some W_6d928.
Proof. vm_refl. Qed.
Lemma D_6d928 : decode_any W_6d928 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d92c : bv 32 := 0x00852503.
Lemma F_6d92c : fetch_word Plain.M.loaded_segments (0x6d984 : word) = Some W_6d92c.
Proof. vm_refl. Qed.
Lemma D_6d92c : decode_any W_6d92c = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d930 : bv 32 := 0x00008067.
Lemma F_6d930 : fetch_word Plain.M.loaded_segments (0x6d988 : word) = Some W_6d930.
Proof. vm_refl. Qed.
Lemma D_6d930 : decode_any W_6d930 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93df4 : bv 32 := 0xfb010113.
Lemma F_93df4 : fetch_word Plain.M.loaded_segments (0x93e4c : word) = Some W_93df4.
Proof. vm_refl. Qed.
Lemma D_93df4 : decode_any W_93df4 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93df8 : bv 32 := 0x04113423.
Lemma F_93df8 : fetch_word Plain.M.loaded_segments (0x93e50 : word) = Some W_93df8.
Proof. vm_refl. Qed.
Lemma D_93df8 : decode_any W_93df8 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93dfc : bv 32 := 0x04813023.
Lemma F_93dfc : fetch_word Plain.M.loaded_segments (0x93e54 : word) = Some W_93dfc.
Proof. vm_refl. Qed.
Lemma D_93dfc : decode_any W_93dfc = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e00 : bv 32 := 0x02913c23.
Lemma F_93e00 : fetch_word Plain.M.loaded_segments (0x93e58 : word) = Some W_93e00.
Proof. vm_refl. Qed.
Lemma D_93e00 : decode_any W_93e00 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e04 : bv 32 := 0x03213823.
Lemma F_93e04 : fetch_word Plain.M.loaded_segments (0x93e5c : word) = Some W_93e04.
Proof. vm_refl. Qed.
Lemma D_93e04 : decode_any W_93e04 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e08 : bv 32 := 0x03313423.
Lemma F_93e08 : fetch_word Plain.M.loaded_segments (0x93e60 : word) = Some W_93e08.
Proof. vm_refl. Qed.
Lemma D_93e08 : decode_any W_93e08 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e0c : bv 32 := 0x03413023.
Lemma F_93e0c : fetch_word Plain.M.loaded_segments (0x93e64 : word) = Some W_93e0c.
Proof. vm_refl. Qed.
Lemma D_93e0c : decode_any W_93e0c = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e10 : bv 32 := 0x01513c23.
Lemma F_93e10 : fetch_word Plain.M.loaded_segments (0x93e68 : word) = Some W_93e10.
Proof. vm_refl. Qed.
Lemma D_93e10 : decode_any W_93e10 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e14 : bv 32 := 0x14050263.
Lemma F_93e14 : fetch_word Plain.M.loaded_segments (0x93e6c : word) = Some W_93e14.
Proof. vm_refl. Qed.
Lemma D_93e14 : decode_any W_93e14 = Some (Branch BC_EQ 10 0 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e18 : bv 32 := 0x00070413.
Lemma F_93e18 : fetch_word Plain.M.loaded_segments (0x93e70 : word) = Some W_93e18.
Proof. vm_refl. Qed.
Lemma D_93e18 : decode_any W_93e18 = Some (OpImm ALU_ADD 8 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e1c : bv 32 := 0x00068493.
Lemma F_93e1c : fetch_word Plain.M.loaded_segments (0x93e74 : word) = Some W_93e1c.
Proof. vm_refl. Qed.
Lemma D_93e1c : decode_any W_93e1c = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e20 : bv 32 := 0x00060a13.
Lemma F_93e20 : fetch_word Plain.M.loaded_segments (0x93e78 : word) = Some W_93e20.
Proof. vm_refl. Qed.
Lemma D_93e20 : decode_any W_93e20 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e24 : bv 32 := 0x00058a93.
Lemma F_93e24 : fetch_word Plain.M.loaded_segments (0x93e7c : word) = Some W_93e24.
Proof. vm_refl. Qed.
Lemma D_93e24 : decode_any W_93e24 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e28 : bv 32 := 0x00050993.
Lemma F_93e28 : fetch_word Plain.M.loaded_segments (0x93e80 : word) = Some W_93e28.
Proof. vm_refl. Qed.
Lemma D_93e28 : decode_any W_93e28 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e2c : bv 32 := 0xafdd90ef.
Lemma F_93e2c : fetch_word Plain.M.loaded_segments (0x93e84 : word) = Some W_93e2c.
Proof. vm_refl. Qed.
Lemma D_93e2c : decode_any W_93e2c = Some (Jal 1 1940220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e30 : bv 32 := 0x00100593.
Lemma F_93e30 : fetch_word Plain.M.loaded_segments (0x93e88 : word) = Some W_93e30.
Proof. vm_refl. Qed.
Lemma D_93e30 : decode_any W_93e30 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e34 : bv 32 := 0x14b51663.
Lemma F_93e34 : fetch_word Plain.M.loaded_segments (0x93e8c : word) = Some W_93e34.
Proof. vm_refl. Qed.
Lemma D_93e34 : decode_any W_93e34 = Some (Branch BC_NE 10 11 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e38 : bv 32 := 0x00400513.
Lemma F_93e38 : fetch_word Plain.M.loaded_segments (0x93e90 : word) = Some W_93e38.
Proof. vm_refl. Qed.
Lemma D_93e38 : decode_any W_93e38 = Some (OpImm ALU_ADD 10 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e3c : bv 32 := 0x17554663.
Lemma F_93e3c : fetch_word Plain.M.loaded_segments (0x93e94 : word) = Some W_93e3c.
Proof. vm_refl. Qed.
Lemma D_93e3c : decode_any W_93e3c = Some (Branch BC_LT 10 21 364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e40 : bv 32 := 0x17454463.
Lemma F_93e40 : fetch_word Plain.M.loaded_segments (0x93e98 : word) = Some W_93e40.
Proof. vm_refl. Qed.
Lemma D_93e40 : decode_any W_93e40 = Some (Branch BC_LT 10 20 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e44 : bv 32 := 0x00400513.
Lemma F_93e44 : fetch_word Plain.M.loaded_segments (0x93e9c : word) = Some W_93e44.
Proof. vm_refl. Qed.
Lemma D_93e44 : decode_any W_93e44 = Some (OpImm ALU_ADD 10 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e48 : bv 32 := 0x16954063.
Lemma F_93e48 : fetch_word Plain.M.loaded_segments (0x93ea0 : word) = Some W_93e48.
Proof. vm_refl. Qed.
Lemma D_93e48 : decode_any W_93e48 = Some (Branch BC_LT 10 9 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e4c : bv 32 := 0x00500513.
Lemma F_93e4c : fetch_word Plain.M.loaded_segments (0x93ea4 : word) = Some W_93e4c.
Proof. vm_refl. Qed.
Lemma D_93e4c : decode_any W_93e4c = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e50 : bv 32 := 0x14a45c63.
Lemma F_93e50 : fetch_word Plain.M.loaded_segments (0x93ea8 : word) = Some W_93e50.
Proof. vm_refl. Qed.
Lemma D_93e50 : decode_any W_93e50 = Some (Branch BC_GE 8 10 344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e54 : bv 32 := 0x1d505463.
Lemma F_93e54 : fetch_word Plain.M.loaded_segments (0x93eac : word) = Some W_93e54.
Proof. vm_refl. Qed.
Lemma D_93e54 : decode_any W_93e54 = Some (Branch BC_GE 0 21 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e58 : bv 32 := 0x10000513.
Lemma F_93e58 : fetch_word Plain.M.loaded_segments (0x93eb0 : word) = Some W_93e58.
Proof. vm_refl. Qed.
Lemma D_93e58 : decode_any W_93e58 = Some (OpImm ALU_ADD 10 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e5c : bv 32 := 0x00100593.
Lemma F_93e5c : fetch_word Plain.M.loaded_segments (0x93eb4 : word) = Some W_93e5c.
Proof. vm_refl. Qed.
Lemma D_93e5c : decode_any W_93e5c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e60 : bv 32 := 0x384660ef.
Lemma F_93e60 : fetch_word Plain.M.loaded_segments (0x93eb8 : word) = Some W_93e60.
Proof. vm_refl. Qed.
Lemma D_93e60 : decode_any W_93e60 = Some (Jal 1 418692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e64 : bv 32 := 0x00050913.
Lemma F_93e64 : fetch_word Plain.M.loaded_segments (0x93ebc : word) = Some W_93e64.
Proof. vm_refl. Qed.
Lemma D_93e64 : decode_any W_93e64 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e68 : bv 32 := 0x00000513.
Lemma F_93e68 : fetch_word Plain.M.loaded_segments (0x93ec0 : word) = Some W_93e68.
Proof. vm_refl. Qed.
Lemma D_93e68 : decode_any W_93e68 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e6c : bv 32 := 0x00000593.
Lemma F_93e6c : fetch_word Plain.M.loaded_segments (0x93ec4 : word) = Some W_93e6c.
Proof. vm_refl. Qed.
Lemma D_93e6c : decode_any W_93e6c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e70 : bv 32 := 0x00000613.
Lemma F_93e70 : fetch_word Plain.M.loaded_segments (0x93ec8 : word) = Some W_93e70.
Proof. vm_refl. Qed.
Lemma D_93e70 : decode_any W_93e70 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e74 : bv 32 := 0x00000693.
Lemma F_93e74 : fetch_word Plain.M.loaded_segments (0x93ecc : word) = Some W_93e74.
Proof. vm_refl. Qed.
Lemma D_93e74 : decode_any W_93e74 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e78 : bv 32 := 0x10090713.
Lemma F_93e78 : fetch_word Plain.M.loaded_segments (0x93ed0 : word) = Some W_93e78.
Proof. vm_refl. Qed.
Lemma D_93e78 : decode_any W_93e78 = Some (OpImm ALU_ADD 14 18 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e7c : bv 32 := 0x00090793.
Lemma F_93e7c : fetch_word Plain.M.loaded_segments (0x93ed4 : word) = Some W_93e7c.
Proof. vm_refl. Qed.
Lemma D_93e7c : decode_any W_93e7c = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e80 : bv 32 := 0x00155813.
Lemma F_93e80 : fetch_word Plain.M.loaded_segments (0x93ed8 : word) = Some W_93e80.
Proof. vm_refl. Qed.
Lemma D_93e80 : decode_any W_93e80 = Some (ShiftImm ALU_SRL 16 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e84 : bv 32 := 0x00255893.
Lemma F_93e84 : fetch_word Plain.M.loaded_segments (0x93edc : word) = Some W_93e84.
Proof. vm_refl. Qed.
Lemma D_93e84 : decode_any W_93e84 = Some (ShiftImm ALU_SRL 17 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e88 : bv 32 := 0x00355293.
Lemma F_93e88 : fetch_word Plain.M.loaded_segments (0x93ee0 : word) = Some W_93e88.
Proof. vm_refl. Qed.
Lemma D_93e88 : decode_any W_93e88 = Some (ShiftImm ALU_SRL 5 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e8c : bv 32 := 0x0105f313.
Lemma F_93e8c : fetch_word Plain.M.loaded_segments (0x93ee4 : word) = Some W_93e8c.
Proof. vm_refl. Qed.
Lemma D_93e8c : decode_any W_93e8c = Some (OpImm ALU_AND 6 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e90 : bv 32 := 0x02067393.
Lemma F_93e90 : fetch_word Plain.M.loaded_segments (0x93ee8 : word) = Some W_93e90.
Proof. vm_refl. Qed.
Lemma D_93e90 : decode_any W_93e90 = Some (OpImm ALU_AND 7 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e94 : bv 32 := 0x0406fe13.
Lemma F_93e94 : fetch_word Plain.M.loaded_segments (0x93eec : word) = Some W_93e94.
Proof. vm_refl. Qed.
Lemma D_93e94 : decode_any W_93e94 = Some (OpImm ALU_AND 28 13 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e98 : bv 32 := 0x08157e93.
Lemma F_93e98 : fetch_word Plain.M.loaded_segments (0x93ef0 : word) = Some W_93e98.
Proof. vm_refl. Qed.
Lemma D_93e98 : decode_any W_93e98 = Some (OpImm ALU_AND 29 10 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93e9c : bv 32 := 0x00268693.
Lemma F_93e9c : fetch_word Plain.M.loaded_segments (0x93ef4 : word) = Some W_93e9c.
Proof. vm_refl. Qed.
Lemma D_93e9c : decode_any W_93e9c = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ea0 : bv 32 := 0x00460613.
Lemma F_93ea0 : fetch_word Plain.M.loaded_segments (0x93ef8 : word) = Some W_93ea0.
Proof. vm_refl. Qed.
Lemma D_93ea0 : decode_any W_93ea0 = Some (OpImm ALU_ADD 12 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ea4 : bv 32 := 0x00287813.
Lemma F_93ea4 : fetch_word Plain.M.loaded_segments (0x93efc : word) = Some W_93ea4.
Proof. vm_refl. Qed.
Lemma D_93ea4 : decode_any W_93ea4 = Some (OpImm ALU_AND 16 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ea8 : bv 32 := 0x0048f893.
Lemma F_93ea8 : fetch_word Plain.M.loaded_segments (0x93f00 : word) = Some W_93ea8.
Proof. vm_refl. Qed.
Lemma D_93ea8 : decode_any W_93ea8 = Some (OpImm ALU_AND 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93eac : bv 32 := 0x0082f293.
Lemma F_93eac : fetch_word Plain.M.loaded_segments (0x93f04 : word) = Some W_93eac.
Proof. vm_refl. Qed.
Lemma D_93eac : decode_any W_93eac = Some (OpImm ALU_AND 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93eb0 : bv 32 := 0x00736333.
Lemma F_93eb0 : fetch_word Plain.M.loaded_segments (0x93f08 : word) = Some W_93eb0.
Proof. vm_refl. Qed.
Lemma D_93eb0 : decode_any W_93eb0 = Some (Op ALU_OR 6 6 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93eb4 : bv 32 := 0x01d86833.
Lemma F_93eb4 : fetch_word Plain.M.loaded_segments (0x93f0c : word) = Some W_93eb4.
Proof. vm_refl. Qed.
Lemma D_93eb4 : decode_any W_93eb4 = Some (Op ALU_OR 16 16 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93eb8 : bv 32 := 0x0058e8b3.
Lemma F_93eb8 : fetch_word Plain.M.loaded_segments (0x93f10 : word) = Some W_93eb8.
Proof. vm_refl. Qed.
Lemma D_93eb8 : decode_any W_93eb8 = Some (Op ALU_OR 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ebc : bv 32 := 0x01c362b3.
Lemma F_93ebc : fetch_word Plain.M.loaded_segments (0x93f14 : word) = Some W_93ebc.
Proof. vm_refl. Qed.
Lemma D_93ebc : decode_any W_93ebc = Some (Op ALU_OR 5 6 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ec0 : bv 32 := 0x01186833.
Lemma F_93ec0 : fetch_word Plain.M.loaded_segments (0x93f18 : word) = Some W_93ec0.
Proof. vm_refl. Qed.
Lemma D_93ec0 : decode_any W_93ec0 = Some (Op ALU_OR 16 16 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ec4 : bv 32 := 0x00586833.
Lemma F_93ec4 : fetch_word Plain.M.loaded_segments (0x93f1c : word) = Some W_93ec4.
Proof. vm_refl. Qed.
Lemma D_93ec4 : decode_any W_93ec4 = Some (Op ALU_OR 16 16 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ec8 : bv 32 := 0x01078023.
Lemma F_93ec8 : fetch_word Plain.M.loaded_segments (0x93f20 : word) = Some W_93ec8.
Proof. vm_refl. Qed.
Lemma D_93ec8 : decode_any W_93ec8 = Some (Store SZ1 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ecc : bv 32 := 0x00178793.
Lemma F_93ecc : fetch_word Plain.M.loaded_segments (0x93f24 : word) = Some W_93ecc.
Proof. vm_refl. Qed.
Lemma D_93ecc : decode_any W_93ecc = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ed0 : bv 32 := 0x00858593.
Lemma F_93ed0 : fetch_word Plain.M.loaded_segments (0x93f28 : word) = Some W_93ed0.
Proof. vm_refl. Qed.
Lemma D_93ed0 : decode_any W_93ed0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ed4 : bv 32 := 0x00150513.
Lemma F_93ed4 : fetch_word Plain.M.loaded_segments (0x93f2c : word) = Some W_93ed4.
Proof. vm_refl. Qed.
Lemma D_93ed4 : decode_any W_93ed4 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ed8 : bv 32 := 0xfae794e3.
Lemma F_93ed8 : fetch_word Plain.M.loaded_segments (0x93f30 : word) = Some W_93ed8.
Proof. vm_refl. Qed.
Lemma D_93ed8 : decode_any W_93ed8 = Some (Branch BC_NE 15 14 8104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93edc : bv 32 := 0x00098513.
Lemma F_93edc : fetch_word Plain.M.loaded_segments (0x93f34 : word) = Some W_93edc.
Proof. vm_refl. Qed.
Lemma D_93edc : decode_any W_93edc = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ee0 : bv 32 := 0x000a8593.
Lemma F_93ee0 : fetch_word Plain.M.loaded_segments (0x93f38 : word) = Some W_93ee0.
Proof. vm_refl. Qed.
Lemma D_93ee0 : decode_any W_93ee0 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ee4 : bv 32 := 0x00090613.
Lemma F_93ee4 : fetch_word Plain.M.loaded_segments (0x93f3c : word) = Some W_93ee4.
Proof. vm_refl. Qed.
Lemma D_93ee4 : decode_any W_93ee4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ee8 : bv 32 := 0x1bc000ef.
Lemma F_93ee8 : fetch_word Plain.M.loaded_segments (0x93f40 : word) = Some W_93ee8.
Proof. vm_refl. Qed.
Lemma D_93ee8 : decode_any W_93ee8 = Some (Jal 1 444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93eec : bv 32 := 0x00a13823.
Lemma F_93eec : fetch_word Plain.M.loaded_segments (0x93f44 : word) = Some W_93eec.
Proof. vm_refl. Qed.
Lemma D_93eec : decode_any W_93eec = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ef0 : bv 32 := 0x19405063.
Lemma F_93ef0 : fetch_word Plain.M.loaded_segments (0x93f48 : word) = Some W_93ef0.
Proof. vm_refl. Qed.
Lemma D_93ef0 : decode_any W_93ef0 = Some (Branch BC_GE 0 20 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ef4 : bv 32 := 0x000a0593.
Lemma F_93ef4 : fetch_word Plain.M.loaded_segments (0x93f4c : word) = Some W_93ef4.
Proof. vm_refl. Qed.
Lemma D_93ef4 : decode_any W_93ef4 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ef8 : bv 32 := 0x00090613.
Lemma F_93ef8 : fetch_word Plain.M.loaded_segments (0x93f50 : word) = Some W_93ef8.
Proof. vm_refl. Qed.
Lemma D_93ef8 : decode_any W_93ef8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93efc : bv 32 := 0x1a8000ef.
Lemma F_93efc : fetch_word Plain.M.loaded_segments (0x93f54 : word) = Some W_93efc.
Proof. vm_refl. Qed.
Lemma D_93efc : decode_any W_93efc = Some (Jal 1 424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f00 : bv 32 := 0x00050993.
Lemma F_93f00 : fetch_word Plain.M.loaded_segments (0x93f58 : word) = Some W_93f00.
Proof. vm_refl. Qed.
Lemma D_93f00 : decode_any W_93f00 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f04 : bv 32 := 0x00a13423.
Lemma F_93f04 : fetch_word Plain.M.loaded_segments (0x93f5c : word) = Some W_93f04.
Proof. vm_refl. Qed.
Lemma D_93f04 : decode_any W_93f04 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f08 : bv 32 := 0x01010513.
Lemma F_93f08 : fetch_word Plain.M.loaded_segments (0x93f60 : word) = Some W_93f08.
Proof. vm_refl. Qed.
Lemma D_93f08 : decode_any W_93f08 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f0c : bv 32 := 0xbd9d80ef.
Lemma F_93f0c : fetch_word Plain.M.loaded_segments (0x93f64 : word) = Some W_93f0c.
Proof. vm_refl. Qed.
Lemma D_93f0c : decode_any W_93f0c = Some (Jal 1 1936344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f10 : bv 32 := 0x16905a63.
Lemma F_93f10 : fetch_word Plain.M.loaded_segments (0x93f68 : word) = Some W_93f10.
Proof. vm_refl. Qed.
Lemma D_93f10 : decode_any W_93f10 = Some (Branch BC_GE 0 9 372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f58 : bv 32 := 0x0007e517.
Lemma F_93f58 : fetch_word Plain.M.loaded_segments (0x93fb0 : word) = Some W_93f58.
Proof. vm_refl. Qed.
Lemma D_93f58 : decode_any W_93f58 = Some (Auipc 10 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f5c : bv 32 := 0x61853503.
Lemma F_93f5c : fetch_word Plain.M.loaded_segments (0x93fb4 : word) = Some W_93f5c.
Proof. vm_refl. Qed.
Lemma D_93f5c : decode_any W_93f5c = Some (Load SZ8 true 10 10 1560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f60 : bv 32 := 0x00052503.
Lemma F_93f60 : fetch_word Plain.M.loaded_segments (0x93fb8 : word) = Some W_93f60.
Proof. vm_refl. Qed.
Lemma D_93f60 : decode_any W_93f60 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f64 : bv 32 := 0x00500593.
Lemma F_93f64 : fetch_word Plain.M.loaded_segments (0x93fbc : word) = Some W_93f64.
Proof. vm_refl. Qed.
Lemma D_93f64 : decode_any W_93f64 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f68 : bv 32 := 0x08a5c663.
Lemma F_93f68 : fetch_word Plain.M.loaded_segments (0x93fc0 : word) = Some W_93f68.
Proof. vm_refl. Qed.
Lemma D_93f68 : decode_any W_93f68 = Some (Branch BC_LT 11 10 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f6c : bv 32 := 0xfff7c517.
Lemma F_93f6c : fetch_word Plain.M.loaded_segments (0x93fc4 : word) = Some W_93f6c.
Proof. vm_refl. Qed.
Lemma D_93f6c : decode_any W_93f6c = Some (Auipc 10 1048444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f70 : bv 32 := 0xfff82597.
Lemma F_93f70 : fetch_word Plain.M.loaded_segments (0x93fc8 : word) = Some W_93f70.
Proof. vm_refl. Qed.
Lemma D_93f70 : decode_any W_93f70 = Some (Auipc 11 1048450, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f74 : bv 32 := 0x39150513.
Lemma F_93f74 : fetch_word Plain.M.loaded_segments (0x93fcc : word) = Some W_93f74.
Proof. vm_refl. Qed.
Lemma D_93f74 : decode_any W_93f74 = Some (OpImm ALU_ADD 10 10 913, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f78 : bv 32 := 0xcac58593.
Lemma F_93f78 : fetch_word Plain.M.loaded_segments (0x93fd0 : word) = Some W_93f78.
Proof. vm_refl. Qed.
Lemma D_93f78 : decode_any W_93f78 = Some (OpImm ALU_ADD 11 11 3244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f7c : bv 32 := 0x0500006f.
Lemma F_93f7c : fetch_word Plain.M.loaded_segments (0x93fd4 : word) = Some W_93f7c.
Proof. vm_refl. Qed.
Lemma D_93f7c : decode_any W_93f7c = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93fcc : bv 32 := 0x00000613.
Lemma F_93fcc : fetch_word Plain.M.loaded_segments (0x94024 : word) = Some W_93fcc.
Proof. vm_refl. Qed.
Lemma D_93fcc : decode_any W_93fcc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93fd0 : bv 32 := 0x04813083.
Lemma F_93fd0 : fetch_word Plain.M.loaded_segments (0x94028 : word) = Some W_93fd0.
Proof. vm_refl. Qed.
Lemma D_93fd0 : decode_any W_93fd0 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93fd4 : bv 32 := 0x04013403.
Lemma F_93fd4 : fetch_word Plain.M.loaded_segments (0x9402c : word) = Some W_93fd4.
Proof. vm_refl. Qed.
Lemma D_93fd4 : decode_any W_93fd4 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93fd8 : bv 32 := 0x03813483.
Lemma F_93fd8 : fetch_word Plain.M.loaded_segments (0x94030 : word) = Some W_93fd8.
Proof. vm_refl. Qed.
Lemma D_93fd8 : decode_any W_93fd8 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93fdc : bv 32 := 0x03013903.
Lemma F_93fdc : fetch_word Plain.M.loaded_segments (0x94034 : word) = Some W_93fdc.
Proof. vm_refl. Qed.
Lemma D_93fdc : decode_any W_93fdc = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93fe0 : bv 32 := 0x02813983.
Lemma F_93fe0 : fetch_word Plain.M.loaded_segments (0x94038 : word) = Some W_93fe0.
Proof. vm_refl. Qed.
Lemma D_93fe0 : decode_any W_93fe0 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93fe4 : bv 32 := 0x02013a03.
Lemma F_93fe4 : fetch_word Plain.M.loaded_segments (0x9403c : word) = Some W_93fe4.
Proof. vm_refl. Qed.
Lemma D_93fe4 : decode_any W_93fe4 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93fe8 : bv 32 := 0x01813a83.
Lemma F_93fe8 : fetch_word Plain.M.loaded_segments (0x94040 : word) = Some W_93fe8.
Proof. vm_refl. Qed.
Lemma D_93fe8 : decode_any W_93fe8 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93fec : bv 32 := 0x05010113.
Lemma F_93fec : fetch_word Plain.M.loaded_segments (0x94044 : word) = Some W_93fec.
Proof. vm_refl. Qed.
Lemma D_93fec : decode_any W_93fec = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ff0 : bv 32 := 0x8d4cf06f.
Lemma F_93ff0 : fetch_word Plain.M.loaded_segments (0x94048 : word) = Some W_93ff0.
Proof. vm_refl. Qed.
Lemma D_93ff0 : decode_any W_93ff0 = Some (Jal 0 1896660, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ff8 : bv 32 := 0x04813083.
Lemma F_93ff8 : fetch_word Plain.M.loaded_segments (0x94050 : word) = Some W_93ff8.
Proof. vm_refl. Qed.
Lemma D_93ff8 : decode_any W_93ff8 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ffc : bv 32 := 0x04013403.
Lemma F_93ffc : fetch_word Plain.M.loaded_segments (0x94054 : word) = Some W_93ffc.
Proof. vm_refl. Qed.
Lemma D_93ffc : decode_any W_93ffc = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94000 : bv 32 := 0x03813483.
Lemma F_94000 : fetch_word Plain.M.loaded_segments (0x94058 : word) = Some W_94000.
Proof. vm_refl. Qed.
Lemma D_94000 : decode_any W_94000 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94004 : bv 32 := 0x03013903.
Lemma F_94004 : fetch_word Plain.M.loaded_segments (0x9405c : word) = Some W_94004.
Proof. vm_refl. Qed.
Lemma D_94004 : decode_any W_94004 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94008 : bv 32 := 0x02813983.
Lemma F_94008 : fetch_word Plain.M.loaded_segments (0x94060 : word) = Some W_94008.
Proof. vm_refl. Qed.
Lemma D_94008 : decode_any W_94008 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9400c : bv 32 := 0x02013a03.
Lemma F_9400c : fetch_word Plain.M.loaded_segments (0x94064 : word) = Some W_9400c.
Proof. vm_refl. Qed.
Lemma D_9400c : decode_any W_9400c = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94010 : bv 32 := 0x01813a83.
Lemma F_94010 : fetch_word Plain.M.loaded_segments (0x94068 : word) = Some W_94010.
Proof. vm_refl. Qed.
Lemma D_94010 : decode_any W_94010 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94014 : bv 32 := 0x05010113.
Lemma F_94014 : fetch_word Plain.M.loaded_segments (0x9406c : word) = Some W_94014.
Proof. vm_refl. Qed.
Lemma D_94014 : decode_any W_94014 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94018 : bv 32 := 0x00008067.
Lemma F_94018 : fetch_word Plain.M.loaded_segments (0x94070 : word) = Some W_94018.
Proof. vm_refl. Qed.
Lemma D_94018 : decode_any W_94018 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94084 : bv 32 := 0x00090513.
Lemma F_94084 : fetch_word Plain.M.loaded_segments (0x940dc : word) = Some W_94084.
Proof. vm_refl. Qed.
Lemma D_94084 : decode_any W_94084 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94088 : bv 32 := 0x294660ef.
Lemma F_94088 : fetch_word Plain.M.loaded_segments (0x940e0 : word) = Some W_94088.
Proof. vm_refl. Qed.
Lemma D_94088 : decode_any W_94088 = Some (Jal 1 418452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9408c : bv 32 := 0x00098513.
Lemma F_9408c : fetch_word Plain.M.loaded_segments (0x940e4 : word) = Some W_9408c.
Proof. vm_refl. Qed.
Lemma D_9408c : decode_any W_9408c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94090 : bv 32 := 0xf69ff06f.
Lemma F_94090 : fetch_word Plain.M.loaded_segments (0x940e8 : word) = Some W_94090.
Proof. vm_refl. Qed.
Lemma D_94090 : decode_any W_94090 = Some (Jal 0 2097000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940a4 : bv 32 := 0xfa010113.
Lemma F_940a4 : fetch_word Plain.M.loaded_segments (0x940fc : word) = Some W_940a4.
Proof. vm_refl. Qed.
Lemma D_940a4 : decode_any W_940a4 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940a8 : bv 32 := 0x04113c23.
Lemma F_940a8 : fetch_word Plain.M.loaded_segments (0x94100 : word) = Some W_940a8.
Proof. vm_refl. Qed.
Lemma D_940a8 : decode_any W_940a8 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940ac : bv 32 := 0x04813823.
Lemma F_940ac : fetch_word Plain.M.loaded_segments (0x94104 : word) = Some W_940ac.
Proof. vm_refl. Qed.
Lemma D_940ac : decode_any W_940ac = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940b0 : bv 32 := 0x04913423.
Lemma F_940b0 : fetch_word Plain.M.loaded_segments (0x94108 : word) = Some W_940b0.
Proof. vm_refl. Qed.
Lemma D_940b0 : decode_any W_940b0 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940b4 : bv 32 := 0x05213023.
Lemma F_940b4 : fetch_word Plain.M.loaded_segments (0x9410c : word) = Some W_940b4.
Proof. vm_refl. Qed.
Lemma D_940b4 : decode_any W_940b4 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940b8 : bv 32 := 0x03313c23.
Lemma F_940b8 : fetch_word Plain.M.loaded_segments (0x94110 : word) = Some W_940b8.
Proof. vm_refl. Qed.
Lemma D_940b8 : decode_any W_940b8 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940bc : bv 32 := 0x03413823.
Lemma F_940bc : fetch_word Plain.M.loaded_segments (0x94114 : word) = Some W_940bc.
Proof. vm_refl. Qed.
Lemma D_940bc : decode_any W_940bc = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940c0 : bv 32 := 0x03513423.
Lemma F_940c0 : fetch_word Plain.M.loaded_segments (0x94118 : word) = Some W_940c0.
Proof. vm_refl. Qed.
Lemma D_940c0 : decode_any W_940c0 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940c4 : bv 32 := 0x03613023.
Lemma F_940c4 : fetch_word Plain.M.loaded_segments (0x9411c : word) = Some W_940c4.
Proof. vm_refl. Qed.
Lemma D_940c4 : decode_any W_940c4 = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940c8 : bv 32 := 0x01713c23.
Lemma F_940c8 : fetch_word Plain.M.loaded_segments (0x94120 : word) = Some W_940c8.
Proof. vm_refl. Qed.
Lemma D_940c8 : decode_any W_940c8 = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940cc : bv 32 := 0x04050863.
Lemma F_940cc : fetch_word Plain.M.loaded_segments (0x94124 : word) = Some W_940cc.
Proof. vm_refl. Qed.
Lemma D_940cc : decode_any W_940cc = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9411c : bv 32 := 0x0007e517.
Lemma F_9411c : fetch_word Plain.M.loaded_segments (0x94174 : word) = Some W_9411c.
Proof. vm_refl. Qed.
Lemma D_9411c : decode_any W_9411c = Some (Auipc 10 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94120 : bv 32 := 0x45453503.
Lemma F_94120 : fetch_word Plain.M.loaded_segments (0x94178 : word) = Some W_94120.
Proof. vm_refl. Qed.
Lemma D_94120 : decode_any W_94120 = Some (Load SZ8 true 10 10 1108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94124 : bv 32 := 0x00052503.
Lemma F_94124 : fetch_word Plain.M.loaded_segments (0x9417c : word) = Some W_94124.
Proof. vm_refl. Qed.
Lemma D_94124 : decode_any W_94124 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94128 : bv 32 := 0x00500593.
Lemma F_94128 : fetch_word Plain.M.loaded_segments (0x94180 : word) = Some W_94128.
Proof. vm_refl. Qed.
Lemma D_94128 : decode_any W_94128 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9412c : bv 32 := 0x54a5ca63.
Lemma F_9412c : fetch_word Plain.M.loaded_segments (0x94184 : word) = Some W_9412c.
Proof. vm_refl. Qed.
Lemma D_9412c : decode_any W_9412c = Some (Branch BC_LT 11 10 1364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94130 : bv 32 := 0xfff7c517.
Lemma F_94130 : fetch_word Plain.M.loaded_segments (0x94188 : word) = Some W_94130.
Proof. vm_refl. Qed.
Lemma D_94130 : decode_any W_94130 = Some (Auipc 10 1048444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94134 : bv 32 := 0xfff82597.
Lemma F_94134 : fetch_word Plain.M.loaded_segments (0x9418c : word) = Some W_94134.
Proof. vm_refl. Qed.
Lemma D_94134 : decode_any W_94134 = Some (Auipc 11 1048450, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94138 : bv 32 := 0x1cd50513.
Lemma F_94138 : fetch_word Plain.M.loaded_segments (0x94190 : word) = Some W_94138.
Proof. vm_refl. Qed.
Lemma D_94138 : decode_any W_94138 = Some (OpImm ALU_ADD 10 10 461, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9413c : bv 32 := 0x1de58593.
Lemma F_9413c : fetch_word Plain.M.loaded_segments (0x94194 : word) = Some W_9413c.
Proof. vm_refl. Qed.
Lemma D_9413c : decode_any W_9413c = Some (OpImm ALU_ADD 11 11 478, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94140 : bv 32 := 0x0280006f.
Lemma F_94140 : fetch_word Plain.M.loaded_segments (0x94198 : word) = Some W_94140.
Proof. vm_refl. Qed.
Lemma D_94140 : decode_any W_94140 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94168 : bv 32 := 0x00000613.
Lemma F_94168 : fetch_word Plain.M.loaded_segments (0x941c0 : word) = Some W_94168.
Proof. vm_refl. Qed.
Lemma D_94168 : decode_any W_94168 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9416c : bv 32 := 0x05813083.
Lemma F_9416c : fetch_word Plain.M.loaded_segments (0x941c4 : word) = Some W_9416c.
Proof. vm_refl. Qed.
Lemma D_9416c : decode_any W_9416c = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94170 : bv 32 := 0x05013403.
Lemma F_94170 : fetch_word Plain.M.loaded_segments (0x941c8 : word) = Some W_94170.
Proof. vm_refl. Qed.
Lemma D_94170 : decode_any W_94170 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94174 : bv 32 := 0x04813483.
Lemma F_94174 : fetch_word Plain.M.loaded_segments (0x941cc : word) = Some W_94174.
Proof. vm_refl. Qed.
Lemma D_94174 : decode_any W_94174 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94178 : bv 32 := 0x04013903.
Lemma F_94178 : fetch_word Plain.M.loaded_segments (0x941d0 : word) = Some W_94178.
Proof. vm_refl. Qed.
Lemma D_94178 : decode_any W_94178 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9417c : bv 32 := 0x03813983.
Lemma F_9417c : fetch_word Plain.M.loaded_segments (0x941d4 : word) = Some W_9417c.
Proof. vm_refl. Qed.
Lemma D_9417c : decode_any W_9417c = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94180 : bv 32 := 0x03013a03.
Lemma F_94180 : fetch_word Plain.M.loaded_segments (0x941d8 : word) = Some W_94180.
Proof. vm_refl. Qed.
Lemma D_94180 : decode_any W_94180 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94184 : bv 32 := 0x02813a83.
Lemma F_94184 : fetch_word Plain.M.loaded_segments (0x941dc : word) = Some W_94184.
Proof. vm_refl. Qed.
Lemma D_94184 : decode_any W_94184 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94188 : bv 32 := 0x02013b03.
Lemma F_94188 : fetch_word Plain.M.loaded_segments (0x941e0 : word) = Some W_94188.
Proof. vm_refl. Qed.
Lemma D_94188 : decode_any W_94188 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9418c : bv 32 := 0x01813b83.
Lemma F_9418c : fetch_word Plain.M.loaded_segments (0x941e4 : word) = Some W_9418c.
Proof. vm_refl. Qed.
Lemma D_9418c : decode_any W_9418c = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94190 : bv 32 := 0x06010113.
Lemma F_94190 : fetch_word Plain.M.loaded_segments (0x941e8 : word) = Some W_94190.
Proof. vm_refl. Qed.
Lemma D_94190 : decode_any W_94190 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94194 : bv 32 := 0xf31ce06f.
Lemma F_94194 : fetch_word Plain.M.loaded_segments (0x941ec : word) = Some W_94194.
Proof. vm_refl. Qed.
Lemma D_94194 : decode_any W_94194 = Some (Jal 0 1896240, 4%Z).
Proof. vm_refl. Qed.

