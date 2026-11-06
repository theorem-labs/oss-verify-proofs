(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_18ecc : bv 32 := 0xff010113.
Lemma F_18ecc : fetch_word Plain.M.loaded_segments (0x18f24 : word) = Some W_18ecc.
Proof. vm_refl. Qed.
Lemma D_18ecc : decode_any W_18ecc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18ed0 : bv 32 := 0x00113423.
Lemma F_18ed0 : fetch_word Plain.M.loaded_segments (0x18f28 : word) = Some W_18ed0.
Proof. vm_refl. Qed.
Lemma D_18ed0 : decode_any W_18ed0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18ed4 : bv 32 := 0x00813023.
Lemma F_18ed4 : fetch_word Plain.M.loaded_segments (0x18f2c : word) = Some W_18ed4.
Proof. vm_refl. Qed.
Lemma D_18ed4 : decode_any W_18ed4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18ed8 : bv 32 := 0x080000ef.
Lemma F_18ed8 : fetch_word Plain.M.loaded_segments (0x18f30 : word) = Some W_18ed8.
Proof. vm_refl. Qed.
Lemma D_18ed8 : decode_any W_18ed8 = Some (Jal 1 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18edc : bv 32 := 0x02050863.
Lemma F_18edc : fetch_word Plain.M.loaded_segments (0x18f34 : word) = Some W_18edc.
Proof. vm_refl. Qed.
Lemma D_18edc : decode_any W_18edc = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18ee0 : bv 32 := 0x00456603.
Lemma F_18ee0 : fetch_word Plain.M.loaded_segments (0x18f38 : word) = Some W_18ee0.
Proof. vm_refl. Qed.
Lemma D_18ee0 : decode_any W_18ee0 = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18ee4 : bv 32 := 0x01056683.
Lemma F_18ee4 : fetch_word Plain.M.loaded_segments (0x18f3c : word) = Some W_18ee4.
Proof. vm_refl. Qed.
Lemma D_18ee4 : decode_any W_18ee4 = Some (Load SZ4 false 13 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18ee8 : bv 32 := 0x03853583.
Lemma F_18ee8 : fetch_word Plain.M.loaded_segments (0x18f40 : word) = Some W_18ee8.
Proof. vm_refl. Qed.
Lemma D_18ee8 : decode_any W_18ee8 = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18eec : bv 32 := 0x02c68633.
Lemma F_18eec : fetch_word Plain.M.loaded_segments (0x18f44 : word) = Some W_18eec.
Proof. vm_refl. Qed.
Lemma D_18eec : decode_any W_18eec = Some (Mul M_MUL 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18ef0 : bv 32 := 0x00261613.
Lemma F_18ef0 : fetch_word Plain.M.loaded_segments (0x18f48 : word) = Some W_18ef0.
Proof. vm_refl. Qed.
Lemma D_18ef0 : decode_any W_18ef0 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18ef4 : bv 32 := 0x00050413.
Lemma F_18ef4 : fetch_word Plain.M.loaded_segments (0x18f4c : word) = Some W_18ef4.
Proof. vm_refl. Qed.
Lemma D_18ef4 : decode_any W_18ef4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18ef8 : bv 32 := 0x00058513.
Lemma F_18ef8 : fetch_word Plain.M.loaded_segments (0x18f50 : word) = Some W_18ef8.
Proof. vm_refl. Qed.
Lemma D_18ef8 : decode_any W_18ef8 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18efc : bv 32 := 0x00000593.
Lemma F_18efc : fetch_word Plain.M.loaded_segments (0x18f54 : word) = Some W_18efc.
Proof. vm_refl. Qed.
Lemma D_18efc : decode_any W_18efc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f00 : bv 32 := 0x7051d0ef.
Lemma F_18f00 : fetch_word Plain.M.loaded_segments (0x18f58 : word) = Some W_18f00.
Proof. vm_refl. Qed.
Lemma D_18f00 : decode_any W_18f00 = Some (Jal 1 122628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f04 : bv 32 := 0x00040513.
Lemma F_18f04 : fetch_word Plain.M.loaded_segments (0x18f5c : word) = Some W_18f04.
Proof. vm_refl. Qed.
Lemma D_18f04 : decode_any W_18f04 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f08 : bv 32 := 0x0400006f.
Lemma F_18f08 : fetch_word Plain.M.loaded_segments (0x18f60 : word) = Some W_18f08.
Proof. vm_refl. Qed.
Lemma D_18f08 : decode_any W_18f08 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f0c : bv 32 := 0x0001f517.
Lemma F_18f0c : fetch_word Plain.M.loaded_segments (0x18f64 : word) = Some W_18f0c.
Proof. vm_refl. Qed.
Lemma D_18f0c : decode_any W_18f0c = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f10 : bv 32 := 0x50c53503.
Lemma F_18f10 : fetch_word Plain.M.loaded_segments (0x18f68 : word) = Some W_18f10.
Proof. vm_refl. Qed.
Lemma D_18f10 : decode_any W_18f10 = Some (Load SZ8 true 10 10 1292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f14 : bv 32 := 0x00052503.
Lemma F_18f14 : fetch_word Plain.M.loaded_segments (0x18f6c : word) = Some W_18f14.
Proof. vm_refl. Qed.
Lemma D_18f14 : decode_any W_18f14 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f18 : bv 32 := 0x00500593.
Lemma F_18f18 : fetch_word Plain.M.loaded_segments (0x18f70 : word) = Some W_18f18.
Proof. vm_refl. Qed.
Lemma D_18f18 : decode_any W_18f18 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f1c : bv 32 := 0x02a5c463.
Lemma F_18f1c : fetch_word Plain.M.loaded_segments (0x18f74 : word) = Some W_18f1c.
Proof. vm_refl. Qed.
Lemma D_18f1c : decode_any W_18f1c = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f20 : bv 32 := 0xffff7517.
Lemma F_18f20 : fetch_word Plain.M.loaded_segments (0x18f78 : word) = Some W_18f20.
Proof. vm_refl. Qed.
Lemma D_18f20 : decode_any W_18f20 = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f24 : bv 32 := 0xffff8597.
Lemma F_18f24 : fetch_word Plain.M.loaded_segments (0x18f7c : word) = Some W_18f24.
Proof. vm_refl. Qed.
Lemma D_18f24 : decode_any W_18f24 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f28 : bv 32 := 0x7e050513.
Lemma F_18f28 : fetch_word Plain.M.loaded_segments (0x18f80 : word) = Some W_18f28.
Proof. vm_refl. Qed.
Lemma D_18f28 : decode_any W_18f28 = Some (OpImm ALU_ADD 10 10 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f2c : bv 32 := 0xe5258593.
Lemma F_18f2c : fetch_word Plain.M.loaded_segments (0x18f84 : word) = Some W_18f2c.
Proof. vm_refl. Qed.
Lemma D_18f2c : decode_any W_18f2c = Some (OpImm ALU_ADD 11 11 3666, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f30 : bv 32 := 0x00000613.
Lemma F_18f30 : fetch_word Plain.M.loaded_segments (0x18f88 : word) = Some W_18f30.
Proof. vm_refl. Qed.
Lemma D_18f30 : decode_any W_18f30 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f34 : bv 32 := 0x00813083.
Lemma F_18f34 : fetch_word Plain.M.loaded_segments (0x18f8c : word) = Some W_18f34.
Proof. vm_refl. Qed.
Lemma D_18f34 : decode_any W_18f34 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f38 : bv 32 := 0x00013403.
Lemma F_18f38 : fetch_word Plain.M.loaded_segments (0x18f90 : word) = Some W_18f38.
Proof. vm_refl. Qed.
Lemma D_18f38 : decode_any W_18f38 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f3c : bv 32 := 0x01010113.
Lemma F_18f3c : fetch_word Plain.M.loaded_segments (0x18f94 : word) = Some W_18f3c.
Proof. vm_refl. Qed.
Lemma D_18f3c : decode_any W_18f3c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f40 : bv 32 := 0xcddfe06f.
Lemma F_18f40 : fetch_word Plain.M.loaded_segments (0x18f98 : word) = Some W_18f40.
Proof. vm_refl. Qed.
Lemma D_18f40 : decode_any W_18f40 = Some (Jal 0 2092252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f48 : bv 32 := 0x00813083.
Lemma F_18f48 : fetch_word Plain.M.loaded_segments (0x18fa0 : word) = Some W_18f48.
Proof. vm_refl. Qed.
Lemma D_18f48 : decode_any W_18f48 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f4c : bv 32 := 0x00013403.
Lemma F_18f4c : fetch_word Plain.M.loaded_segments (0x18fa4 : word) = Some W_18f4c.
Proof. vm_refl. Qed.
Lemma D_18f4c : decode_any W_18f4c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f50 : bv 32 := 0x01010113.
Lemma F_18f50 : fetch_word Plain.M.loaded_segments (0x18fa8 : word) = Some W_18f50.
Proof. vm_refl. Qed.
Lemma D_18f50 : decode_any W_18f50 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f54 : bv 32 := 0x00008067.
Lemma F_18f54 : fetch_word Plain.M.loaded_segments (0x18fac : word) = Some W_18f54.
Proof. vm_refl. Qed.
Lemma D_18f54 : decode_any W_18f54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f58 : bv 32 := 0xfd010113.
Lemma F_18f58 : fetch_word Plain.M.loaded_segments (0x18fb0 : word) = Some W_18f58.
Proof. vm_refl. Qed.
Lemma D_18f58 : decode_any W_18f58 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f5c : bv 32 := 0x02113423.
Lemma F_18f5c : fetch_word Plain.M.loaded_segments (0x18fb4 : word) = Some W_18f5c.
Proof. vm_refl. Qed.
Lemma D_18f5c : decode_any W_18f5c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f60 : bv 32 := 0x02813023.
Lemma F_18f60 : fetch_word Plain.M.loaded_segments (0x18fb8 : word) = Some W_18f60.
Proof. vm_refl. Qed.
Lemma D_18f60 : decode_any W_18f60 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f64 : bv 32 := 0x00913c23.
Lemma F_18f64 : fetch_word Plain.M.loaded_segments (0x18fbc : word) = Some W_18f64.
Proof. vm_refl. Qed.
Lemma D_18f64 : decode_any W_18f64 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f68 : bv 32 := 0x01213823.
Lemma F_18f68 : fetch_word Plain.M.loaded_segments (0x18fc0 : word) = Some W_18f68.
Proof. vm_refl. Qed.
Lemma D_18f68 : decode_any W_18f68 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f6c : bv 32 := 0x00058493.
Lemma F_18f6c : fetch_word Plain.M.loaded_segments (0x18fc4 : word) = Some W_18f6c.
Proof. vm_refl. Qed.
Lemma D_18f6c : decode_any W_18f6c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f70 : bv 32 := 0x124000ef.
Lemma F_18f70 : fetch_word Plain.M.loaded_segments (0x18fc8 : word) = Some W_18f70.
Proof. vm_refl. Qed.
Lemma D_18f70 : decode_any W_18f70 = Some (Jal 1 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f74 : bv 32 := 0x02050e63.
Lemma F_18f74 : fetch_word Plain.M.loaded_segments (0x18fcc : word) = Some W_18f74.
Proof. vm_refl. Qed.
Lemma D_18f74 : decode_any W_18f74 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f78 : bv 32 := 0x00050413.
Lemma F_18f78 : fetch_word Plain.M.loaded_segments (0x18fd0 : word) = Some W_18f78.
Proof. vm_refl. Qed.
Lemma D_18f78 : decode_any W_18f78 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f7c : bv 32 := 0x01052503.
Lemma F_18f7c : fetch_word Plain.M.loaded_segments (0x18fd4 : word) = Some W_18f7c.
Proof. vm_refl. Qed.
Lemma D_18f7c : decode_any W_18f7c = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f80 : bv 32 := 0x00020597.
Lemma F_18f80 : fetch_word Plain.M.loaded_segments (0x18fd8 : word) = Some W_18f80.
Proof. vm_refl. Qed.
Lemma D_18f80 : decode_any W_18f80 = Some (Auipc 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f84 : bv 32 := 0x51858913.
Lemma F_18f84 : fetch_word Plain.M.loaded_segments (0x18fdc : word) = Some W_18f84.
Proof. vm_refl. Qed.
Lemma D_18f84 : decode_any W_18f84 = Some (OpImm ALU_ADD 18 11 1304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f88 : bv 32 := 0x00093583.
Lemma F_18f88 : fetch_word Plain.M.loaded_segments (0x18fe0 : word) = Some W_18f88.
Proof. vm_refl. Qed.
Lemma D_18f88 : decode_any W_18f88 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f8c : bv 32 := 0x02a48533.
Lemma F_18f8c : fetch_word Plain.M.loaded_segments (0x18fe4 : word) = Some W_18f8c.
Proof. vm_refl. Qed.
Lemma D_18f8c : decode_any W_18f8c = Some (Mul M_MUL 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f90 : bv 32 := 0x00251513.
Lemma F_18f90 : fetch_word Plain.M.loaded_segments (0x18fe8 : word) = Some W_18f90.
Proof. vm_refl. Qed.
Lemma D_18f90 : decode_any W_18f90 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f94 : bv 32 := 0x000580e7.
Lemma F_18f94 : fetch_word Plain.M.loaded_segments (0x18fec : word) = Some W_18f94.
Proof. vm_refl. Qed.
Lemma D_18f94 : decode_any W_18f94 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f98 : bv 32 := 0x04050c63.
Lemma F_18f98 : fetch_word Plain.M.loaded_segments (0x18ff0 : word) = Some W_18f98.
Proof. vm_refl. Qed.
Lemma D_18f98 : decode_any W_18f98 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18f9c : bv 32 := 0x02a43c23.
Lemma F_18f9c : fetch_word Plain.M.loaded_segments (0x18ff4 : word) = Some W_18f9c.
Proof. vm_refl. Qed.
Lemma D_18f9c : decode_any W_18f9c = Some (Store SZ8 8 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fa0 : bv 32 := 0x00040513.
Lemma F_18fa0 : fetch_word Plain.M.loaded_segments (0x18ff8 : word) = Some W_18fa0.
Proof. vm_refl. Qed.
Lemma D_18fa0 : decode_any W_18fa0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fa4 : bv 32 := 0x00000593.
Lemma F_18fa4 : fetch_word Plain.M.loaded_segments (0x18ffc : word) = Some W_18fa4.
Proof. vm_refl. Qed.
Lemma D_18fa4 : decode_any W_18fa4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fa8 : bv 32 := 0x0b8020ef.
Lemma F_18fa8 : fetch_word Plain.M.loaded_segments (0x19000 : word) = Some W_18fa8.
Proof. vm_refl. Qed.
Lemma D_18fa8 : decode_any W_18fa8 = Some (Jal 1 8376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fac : bv 32 := 0x0cc0006f.
Lemma F_18fac : fetch_word Plain.M.loaded_segments (0x19004 : word) = Some W_18fac.
Proof. vm_refl. Qed.
Lemma D_18fac : decode_any W_18fac = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fb0 : bv 32 := 0x0001f517.
Lemma F_18fb0 : fetch_word Plain.M.loaded_segments (0x19008 : word) = Some W_18fb0.
Proof. vm_refl. Qed.
Lemma D_18fb0 : decode_any W_18fb0 = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fb4 : bv 32 := 0x46853503.
Lemma F_18fb4 : fetch_word Plain.M.loaded_segments (0x1900c : word) = Some W_18fb4.
Proof. vm_refl. Qed.
Lemma D_18fb4 : decode_any W_18fb4 = Some (Load SZ8 true 10 10 1128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fb8 : bv 32 := 0x00052503.
Lemma F_18fb8 : fetch_word Plain.M.loaded_segments (0x19010 : word) = Some W_18fb8.
Proof. vm_refl. Qed.
Lemma D_18fb8 : decode_any W_18fb8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fbc : bv 32 := 0x00500593.
Lemma F_18fbc : fetch_word Plain.M.loaded_segments (0x19014 : word) = Some W_18fbc.
Proof. vm_refl. Qed.
Lemma D_18fbc : decode_any W_18fbc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fc0 : bv 32 := 0x0aa5ca63.
Lemma F_18fc0 : fetch_word Plain.M.loaded_segments (0x19018 : word) = Some W_18fc0.
Proof. vm_refl. Qed.
Lemma D_18fc0 : decode_any W_18fc0 = Some (Branch BC_LT 11 10 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fc4 : bv 32 := 0xffff7517.
Lemma F_18fc4 : fetch_word Plain.M.loaded_segments (0x1901c : word) = Some W_18fc4.
Proof. vm_refl. Qed.
Lemma D_18fc4 : decode_any W_18fc4 = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fc8 : bv 32 := 0xffff8597.
Lemma F_18fc8 : fetch_word Plain.M.loaded_segments (0x19020 : word) = Some W_18fc8.
Proof. vm_refl. Qed.
Lemma D_18fc8 : decode_any W_18fc8 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fcc : bv 32 := 0x73c50513.
Lemma F_18fcc : fetch_word Plain.M.loaded_segments (0x19024 : word) = Some W_18fcc.
Proof. vm_refl. Qed.
Lemma D_18fcc : decode_any W_18fcc = Some (OpImm ALU_ADD 10 10 1852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fd0 : bv 32 := 0xa9558593.
Lemma F_18fd0 : fetch_word Plain.M.loaded_segments (0x19028 : word) = Some W_18fd0.
Proof. vm_refl. Qed.
Lemma D_18fd0 : decode_any W_18fd0 = Some (OpImm ALU_ADD 11 11 2709, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fd4 : bv 32 := 0x00000613.
Lemma F_18fd4 : fetch_word Plain.M.loaded_segments (0x1902c : word) = Some W_18fd4.
Proof. vm_refl. Qed.
Lemma D_18fd4 : decode_any W_18fd4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fd8 : bv 32 := 0x02813083.
Lemma F_18fd8 : fetch_word Plain.M.loaded_segments (0x19030 : word) = Some W_18fd8.
Proof. vm_refl. Qed.
Lemma D_18fd8 : decode_any W_18fd8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fdc : bv 32 := 0x02013403.
Lemma F_18fdc : fetch_word Plain.M.loaded_segments (0x19034 : word) = Some W_18fdc.
Proof. vm_refl. Qed.
Lemma D_18fdc : decode_any W_18fdc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fe0 : bv 32 := 0x01813483.
Lemma F_18fe0 : fetch_word Plain.M.loaded_segments (0x19038 : word) = Some W_18fe0.
Proof. vm_refl. Qed.
Lemma D_18fe0 : decode_any W_18fe0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fe4 : bv 32 := 0x01013903.
Lemma F_18fe4 : fetch_word Plain.M.loaded_segments (0x1903c : word) = Some W_18fe4.
Proof. vm_refl. Qed.
Lemma D_18fe4 : decode_any W_18fe4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fe8 : bv 32 := 0x03010113.
Lemma F_18fe8 : fetch_word Plain.M.loaded_segments (0x19040 : word) = Some W_18fe8.
Proof. vm_refl. Qed.
Lemma D_18fe8 : decode_any W_18fe8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18fec : bv 32 := 0xc31fe06f.
Lemma F_18fec : fetch_word Plain.M.loaded_segments (0x19044 : word) = Some W_18fec.
Proof. vm_refl. Qed.
Lemma D_18fec : decode_any W_18fec = Some (Jal 0 2092080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18ff0 : bv 32 := 0x01440513.
Lemma F_18ff0 : fetch_word Plain.M.loaded_segments (0x19048 : word) = Some W_18ff0.
Proof. vm_refl. Qed.
Lemma D_18ff0 : decode_any W_18ff0 = Some (OpImm ALU_ADD 10 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18ff4 : bv 32 := 0xfff00593.
Lemma F_18ff4 : fetch_word Plain.M.loaded_segments (0x1904c : word) = Some W_18ff4.
Proof. vm_refl. Qed.
Lemma D_18ff4 : decode_any W_18ff4 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18ff8 : bv 32 := 0x06b5252f.
Lemma F_18ff8 : fetch_word Plain.M.loaded_segments (0x19050 : word) = Some W_18ff8.
Proof. vm_refl. Qed.
Lemma D_18ff8 : decode_any W_18ff8 = Some (Amo AMO_ADD AW true true 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18ffc : bv 32 := 0x00100593.
Lemma F_18ffc : fetch_word Plain.M.loaded_segments (0x19054 : word) = Some W_18ffc.
Proof. vm_refl. Qed.
Lemma D_18ffc : decode_any W_18ffc = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.
