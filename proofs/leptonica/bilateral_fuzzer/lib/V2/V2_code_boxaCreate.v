(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_18ecc : bv 32 := 0xfe010113.
Lemma F_18ecc : fetch_word Ubsan.M.loaded_segments (0x18ecc : word) = Some W_18ecc.
Proof. vm_refl. Qed.
Lemma D_18ecc : decode_any W_18ecc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ed0 : bv 32 := 0x00113c23.
Lemma F_18ed0 : fetch_word Ubsan.M.loaded_segments (0x18ed0 : word) = Some W_18ed0.
Proof. vm_refl. Qed.
Lemma D_18ed0 : decode_any W_18ed0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ed4 : bv 32 := 0x00813823.
Lemma F_18ed4 : fetch_word Ubsan.M.loaded_segments (0x18ed4 : word) = Some W_18ed4.
Proof. vm_refl. Qed.
Lemma D_18ed4 : decode_any W_18ed4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ed8 : bv 32 := 0x00913423.
Lemma F_18ed8 : fetch_word Ubsan.M.loaded_segments (0x18ed8 : word) = Some W_18ed8.
Proof. vm_refl. Qed.
Lemma D_18ed8 : decode_any W_18ed8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18edc : bv 32 := 0x00050493.
Lemma F_18edc : fetch_word Ubsan.M.loaded_segments (0x18edc : word) = Some W_18edc.
Proof. vm_refl. Qed.
Lemma D_18edc : decode_any W_18edc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ee0 : bv 32 := 0x00100513.
Lemma F_18ee0 : fetch_word Ubsan.M.loaded_segments (0x18ee0 : word) = Some W_18ee0.
Proof. vm_refl. Qed.
Lemma D_18ee0 : decode_any W_18ee0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ee4 : bv 32 := 0x01800593.
Lemma F_18ee4 : fetch_word Ubsan.M.loaded_segments (0x18ee4 : word) = Some W_18ee4.
Proof. vm_refl. Qed.
Lemma D_18ee4 : decode_any W_18ee4 = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ee8 : bv 32 := 0x210230ef.
Lemma F_18ee8 : fetch_word Ubsan.M.loaded_segments (0x18ee8 : word) = Some W_18ee8.
Proof. vm_refl. Qed.
Lemma D_18ee8 : decode_any W_18ee8 = Some (Jal 1 143888, 4%Z).
Proof. vm_refl. Qed.

Definition W_18eec : bv 32 := 0x00a13023.
Lemma F_18eec : fetch_word Ubsan.M.loaded_segments (0x18eec : word) = Some W_18eec.
Proof. vm_refl. Qed.
Lemma D_18eec : decode_any W_18eec = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ef0 : bv 32 := 0x0a050663.
Lemma F_18ef0 : fetch_word Ubsan.M.loaded_segments (0x18ef0 : word) = Some W_18ef0.
Proof. vm_refl. Qed.
Lemma D_18ef0 : decode_any W_18ef0 = Some (Branch BC_EQ 10 0 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ef4 : bv 32 := 0x00050413.
Lemma F_18ef4 : fetch_word Ubsan.M.loaded_segments (0x18ef4 : word) = Some W_18ef4.
Proof. vm_refl. Qed.
Lemma D_18ef4 : decode_any W_18ef4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ef8 : bv 32 := 0x00757513.
Lemma F_18ef8 : fetch_word Ubsan.M.loaded_segments (0x18ef8 : word) = Some W_18ef8.
Proof. vm_refl. Qed.
Lemma D_18ef8 : decode_any W_18ef8 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_18efc : bv 32 := 0x0a051063.
Lemma F_18efc : fetch_word Ubsan.M.loaded_segments (0x18efc : word) = Some W_18efc.
Proof. vm_refl. Qed.
Lemma D_18efc : decode_any W_18efc = Some (Branch BC_NE 10 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f00 : bv 32 := 0xff677537.
Lemma F_18f00 : fetch_word Ubsan.M.loaded_segments (0x18f00 : word) = Some W_18f00.
Proof. vm_refl. Qed.
Lemma D_18f00 : decode_any W_18f00 = Some (Lui 10 1046135, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f04 : bv 32 := 0x97f50593.
Lemma F_18f04 : fetch_word Ubsan.M.loaded_segments (0x18f04 : word) = Some W_18f04.
Proof. vm_refl. Qed.
Lemma D_18f04 : decode_any W_18f04 = Some (OpImm ALU_ADD 11 10 2431, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f08 : bv 32 := 0x00b485bb.
Lemma F_18f08 : fetch_word Ubsan.M.loaded_segments (0x18f08 : word) = Some W_18f08.
Proof. vm_refl. Qed.
Lemma D_18f08 : decode_any W_18f08 = Some (Op32 ALU_ADD 11 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f0c : bv 32 := 0x9805051b.
Lemma F_18f0c : fetch_word Ubsan.M.loaded_segments (0x18f0c : word) = Some W_18f0c.
Proof. vm_refl. Qed.
Lemma D_18f0c : decode_any W_18f0c = Some (OpImm32 10 10 2432, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f10 : bv 32 := 0x00a5f463.
Lemma F_18f10 : fetch_word Ubsan.M.loaded_segments (0x18f10 : word) = Some W_18f10.
Proof. vm_refl. Qed.
Lemma D_18f10 : decode_any W_18f10 = Some (Branch BC_GEU 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f14 : bv 32 := 0x01400493.
Lemma F_18f14 : fetch_word Ubsan.M.loaded_segments (0x18f14 : word) = Some W_18f14.
Proof. vm_refl. Qed.
Lemma D_18f14 : decode_any W_18f14 = Some (OpImm ALU_ADD 9 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f18 : bv 32 := 0x00042023.
Lemma F_18f18 : fetch_word Ubsan.M.loaded_segments (0x18f18 : word) = Some W_18f18.
Proof. vm_refl. Qed.
Lemma D_18f18 : decode_any W_18f18 = Some (Store SZ4 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f1c : bv 32 := 0x00942223.
Lemma F_18f1c : fetch_word Ubsan.M.loaded_segments (0x18f1c : word) = Some W_18f1c.
Proof. vm_refl. Qed.
Lemma D_18f1c : decode_any W_18f1c = Some (Store SZ4 8 9 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f20 : bv 32 := 0x0310000f.
Lemma F_18f20 : fetch_word Ubsan.M.loaded_segments (0x18f20 : word) = Some W_18f20.
Proof. vm_refl. Qed.
Lemma D_18f20 : decode_any W_18f20 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f24 : bv 32 := 0x00100513.
Lemma F_18f24 : fetch_word Ubsan.M.loaded_segments (0x18f24 : word) = Some W_18f24.
Proof. vm_refl. Qed.
Lemma D_18f24 : decode_any W_18f24 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f28 : bv 32 := 0x00a42423.
Lemma F_18f28 : fetch_word Ubsan.M.loaded_segments (0x18f28 : word) = Some W_18f28.
Proof. vm_refl. Qed.
Lemma D_18f28 : decode_any W_18f28 = Some (Store SZ4 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f2c : bv 32 := 0x0330000f.
Lemma F_18f2c : fetch_word Ubsan.M.loaded_segments (0x18f2c : word) = Some W_18f2c.
Proof. vm_refl. Qed.
Lemma D_18f2c : decode_any W_18f2c = Some (Fence 0 3 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f30 : bv 32 := 0x00800593.
Lemma F_18f30 : fetch_word Ubsan.M.loaded_segments (0x18f30 : word) = Some W_18f30.
Proof. vm_refl. Qed.
Lemma D_18f30 : decode_any W_18f30 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f34 : bv 32 := 0x00048513.
Lemma F_18f34 : fetch_word Ubsan.M.loaded_segments (0x18f34 : word) = Some W_18f34.
Proof. vm_refl. Qed.
Lemma D_18f34 : decode_any W_18f34 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f38 : bv 32 := 0x1c0230ef.
Lemma F_18f38 : fetch_word Ubsan.M.loaded_segments (0x18f38 : word) = Some W_18f38.
Proof. vm_refl. Qed.
Lemma D_18f38 : decode_any W_18f38 = Some (Jal 1 143808, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f3c : bv 32 := 0x00a43823.
Lemma F_18f3c : fetch_word Ubsan.M.loaded_segments (0x18f3c : word) = Some W_18f3c.
Proof. vm_refl. Qed.
Lemma D_18f3c : decode_any W_18f3c = Some (Store SZ8 8 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f40 : bv 32 := 0x04051263.
Lemma F_18f40 : fetch_word Ubsan.M.loaded_segments (0x18f40 : word) = Some W_18f40.
Proof. vm_refl. Qed.
Lemma D_18f40 : decode_any W_18f40 = Some (Branch BC_NE 10 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f44 : bv 32 := 0x00010513.
Lemma F_18f44 : fetch_word Ubsan.M.loaded_segments (0x18f44 : word) = Some W_18f44.
Proof. vm_refl. Qed.
Lemma D_18f44 : decode_any W_18f44 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f48 : bv 32 := 0x058000ef.
Lemma F_18f48 : fetch_word Ubsan.M.loaded_segments (0x18f48 : word) = Some W_18f48.
Proof. vm_refl. Qed.
Lemma D_18f48 : decode_any W_18f48 = Some (Jal 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f4c : bv 32 := 0x0002c517.
Lemma F_18f4c : fetch_word Ubsan.M.loaded_segments (0x18f4c : word) = Some W_18f4c.
Proof. vm_refl. Qed.
Lemma D_18f4c : decode_any W_18f4c = Some (Auipc 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f50 : bv 32 := 0xf4c53503.
Lemma F_18f50 : fetch_word Ubsan.M.loaded_segments (0x18f50 : word) = Some W_18f50.
Proof. vm_refl. Qed.
Lemma D_18f50 : decode_any W_18f50 = Some (Load SZ8 true 10 10 3916, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f54 : bv 32 := 0x00052503.
Lemma F_18f54 : fetch_word Ubsan.M.loaded_segments (0x18f54 : word) = Some W_18f54.
Proof. vm_refl. Qed.
Lemma D_18f54 : decode_any W_18f54 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f58 : bv 32 := 0x00500593.
Lemma F_18f58 : fetch_word Ubsan.M.loaded_segments (0x18f58 : word) = Some W_18f58.
Proof. vm_refl. Qed.
Lemma D_18f58 : decode_any W_18f58 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f5c : bv 32 := 0x02a5c263.
Lemma F_18f5c : fetch_word Ubsan.M.loaded_segments (0x18f5c : word) = Some W_18f5c.
Proof. vm_refl. Qed.
Lemma D_18f5c : decode_any W_18f5c = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f60 : bv 32 := 0xffff8517.
Lemma F_18f60 : fetch_word Ubsan.M.loaded_segments (0x18f60 : word) = Some W_18f60.
Proof. vm_refl. Qed.
Lemma D_18f60 : decode_any W_18f60 = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f64 : bv 32 := 0xffff7597.
Lemma F_18f64 : fetch_word Ubsan.M.loaded_segments (0x18f64 : word) = Some W_18f64.
Proof. vm_refl. Qed.
Lemma D_18f64 : decode_any W_18f64 = Some (Auipc 11 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f68 : bv 32 := 0x57350513.
Lemma F_18f68 : fetch_word Ubsan.M.loaded_segments (0x18f68 : word) = Some W_18f68.
Proof. vm_refl. Qed.
Lemma D_18f68 : decode_any W_18f68 = Some (OpImm ALU_ADD 10 10 1395, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f6c : bv 32 := 0x34558593.
Lemma F_18f6c : fetch_word Ubsan.M.loaded_segments (0x18f6c : word) = Some W_18f6c.
Proof. vm_refl. Qed.
Lemma D_18f6c : decode_any W_18f6c = Some (OpImm ALU_ADD 11 11 837, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f70 : bv 32 := 0x00000613.
Lemma F_18f70 : fetch_word Ubsan.M.loaded_segments (0x18f70 : word) = Some W_18f70.
Proof. vm_refl. Qed.
Lemma D_18f70 : decode_any W_18f70 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f74 : bv 32 := 0xf51fe0ef.
Lemma F_18f74 : fetch_word Ubsan.M.loaded_segments (0x18f74 : word) = Some W_18f74.
Proof. vm_refl. Qed.
Lemma D_18f74 : decode_any W_18f74 = Some (Jal 1 2092880, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f78 : bv 32 := 0x00050413.
Lemma F_18f78 : fetch_word Ubsan.M.loaded_segments (0x18f78 : word) = Some W_18f78.
Proof. vm_refl. Qed.
Lemma D_18f78 : decode_any W_18f78 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f7c : bv 32 := 0x0080006f.
Lemma F_18f7c : fetch_word Ubsan.M.loaded_segments (0x18f7c : word) = Some W_18f7c.
Proof. vm_refl. Qed.
Lemma D_18f7c : decode_any W_18f7c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f80 : bv 32 := 0x00000413.
Lemma F_18f80 : fetch_word Ubsan.M.loaded_segments (0x18f80 : word) = Some W_18f80.
Proof. vm_refl. Qed.
Lemma D_18f80 : decode_any W_18f80 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f84 : bv 32 := 0x00040513.
Lemma F_18f84 : fetch_word Ubsan.M.loaded_segments (0x18f84 : word) = Some W_18f84.
Proof. vm_refl. Qed.
Lemma D_18f84 : decode_any W_18f84 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f88 : bv 32 := 0x01813083.
Lemma F_18f88 : fetch_word Ubsan.M.loaded_segments (0x18f88 : word) = Some W_18f88.
Proof. vm_refl. Qed.
Lemma D_18f88 : decode_any W_18f88 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f8c : bv 32 := 0x01013403.
Lemma F_18f8c : fetch_word Ubsan.M.loaded_segments (0x18f8c : word) = Some W_18f8c.
Proof. vm_refl. Qed.
Lemma D_18f8c : decode_any W_18f8c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f90 : bv 32 := 0x00813483.
Lemma F_18f90 : fetch_word Ubsan.M.loaded_segments (0x18f90 : word) = Some W_18f90.
Proof. vm_refl. Qed.
Lemma D_18f90 : decode_any W_18f90 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f94 : bv 32 := 0x02010113.
Lemma F_18f94 : fetch_word Ubsan.M.loaded_segments (0x18f94 : word) = Some W_18f94.
Proof. vm_refl. Qed.
Lemma D_18f94 : decode_any W_18f94 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f98 : bv 32 := 0x00008067.
Lemma F_18f98 : fetch_word Ubsan.M.loaded_segments (0x18f98 : word) = Some W_18f98.
Proof. vm_refl. Qed.
Lemma D_18f98 : decode_any W_18f98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
