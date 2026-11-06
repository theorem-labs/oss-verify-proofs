(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.H Require GcFlushS14.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_28ef0 : bv 32 := 0x0e060a63.
Lemma F_28ef0 : fetch_word Plain.M.loaded_segments (0x2942c : word) = Some W_28ef0.
Proof. vm_refl. Qed.
Lemma D_28ef0 : decode_any W_28ef0 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28ef4 : bv 32 := 0x00b50023.
Lemma F_28ef4 : fetch_word Plain.M.loaded_segments (0x29430 : word) = Some W_28ef4.
Proof. vm_refl. Qed.
Lemma D_28ef4 : decode_any W_28ef4 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28ef8 : bv 32 := 0x00c506b3.
Lemma F_28ef8 : fetch_word Plain.M.loaded_segments (0x29434 : word) = Some W_28ef8.
Proof. vm_refl. Qed.
Lemma D_28ef8 : decode_any W_28ef8 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28efc : bv 32 := 0x00300713.
Lemma F_28efc : fetch_word Plain.M.loaded_segments (0x29438 : word) = Some W_28efc.
Proof. vm_refl. Qed.
Lemma D_28efc : decode_any W_28efc = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f00 : bv 32 := 0xfeb68fa3.
Lemma F_28f00 : fetch_word Plain.M.loaded_segments (0x2943c : word) = Some W_28f00.
Proof. vm_refl. Qed.
Lemma D_28f00 : decode_any W_28f00 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f04 : bv 32 := 0x0ee66063.
Lemma F_28f04 : fetch_word Plain.M.loaded_segments (0x29440 : word) = Some W_28f04.
Proof. vm_refl. Qed.
Lemma D_28f04 : decode_any W_28f04 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f08 : bv 32 := 0x00b500a3.
Lemma F_28f08 : fetch_word Plain.M.loaded_segments (0x29444 : word) = Some W_28f08.
Proof. vm_refl. Qed.
Lemma D_28f08 : decode_any W_28f08 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f0c : bv 32 := 0x00b50123.
Lemma F_28f0c : fetch_word Plain.M.loaded_segments (0x29448 : word) = Some W_28f0c.
Proof. vm_refl. Qed.
Lemma D_28f0c : decode_any W_28f0c = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f10 : bv 32 := 0x00700713.
Lemma F_28f10 : fetch_word Plain.M.loaded_segments (0x2944c : word) = Some W_28f10.
Proof. vm_refl. Qed.
Lemma D_28f10 : decode_any W_28f10 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f14 : bv 32 := 0xfeb68ea3.
Lemma F_28f14 : fetch_word Plain.M.loaded_segments (0x29450 : word) = Some W_28f14.
Proof. vm_refl. Qed.
Lemma D_28f14 : decode_any W_28f14 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f18 : bv 32 := 0xfeb68f23.
Lemma F_28f18 : fetch_word Plain.M.loaded_segments (0x29454 : word) = Some W_28f18.
Proof. vm_refl. Qed.
Lemma D_28f18 : decode_any W_28f18 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f1c : bv 32 := 0x0ce66463.
Lemma F_28f1c : fetch_word Plain.M.loaded_segments (0x29458 : word) = Some W_28f1c.
Proof. vm_refl. Qed.
Lemma D_28f1c : decode_any W_28f1c = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f20 : bv 32 := 0x00b501a3.
Lemma F_28f20 : fetch_word Plain.M.loaded_segments (0x2945c : word) = Some W_28f20.
Proof. vm_refl. Qed.
Lemma D_28f20 : decode_any W_28f20 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f24 : bv 32 := 0x00900793.
Lemma F_28f24 : fetch_word Plain.M.loaded_segments (0x29460 : word) = Some W_28f24.
Proof. vm_refl. Qed.
Lemma D_28f24 : decode_any W_28f24 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f28 : bv 32 := 0xfeb68e23.
Lemma F_28f28 : fetch_word Plain.M.loaded_segments (0x29464 : word) = Some W_28f28.
Proof. vm_refl. Qed.
Lemma D_28f28 : decode_any W_28f28 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f2c : bv 32 := 0x0af66c63.
Lemma F_28f2c : fetch_word Plain.M.loaded_segments (0x29468 : word) = Some W_28f2c.
Proof. vm_refl. Qed.
Lemma D_28f2c : decode_any W_28f2c = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f30 : bv 32 := 0x40a006bb.
Lemma F_28f30 : fetch_word Plain.M.loaded_segments (0x2946c : word) = Some W_28f30.
Proof. vm_refl. Qed.
Lemma D_28f30 : decode_any W_28f30 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f34 : bv 32 := 0x03859813.
Lemma F_28f34 : fetch_word Plain.M.loaded_segments (0x29470 : word) = Some W_28f34.
Proof. vm_refl. Qed.
Lemma D_28f34 : decode_any W_28f34 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f38 : bv 32 := 0x101015b7.
Lemma F_28f38 : fetch_word Plain.M.loaded_segments (0x29474 : word) = Some W_28f38.
Proof. vm_refl. Qed.
Lemma D_28f38 : decode_any W_28f38 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f3c : bv 32 := 0x0036f693.
Lemma F_28f3c : fetch_word Plain.M.loaded_segments (0x29478 : word) = Some W_28f3c.
Proof. vm_refl. Qed.
Lemma D_28f3c : decode_any W_28f3c = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f40 : bv 32 := 0x00459713.
Lemma F_28f40 : fetch_word Plain.M.loaded_segments (0x2947c : word) = Some W_28f40.
Proof. vm_refl. Qed.
Lemma D_28f40 : decode_any W_28f40 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f44 : bv 32 := 0x40d60633.
Lemma F_28f44 : fetch_word Plain.M.loaded_segments (0x29480 : word) = Some W_28f44.
Proof. vm_refl. Qed.
Lemma D_28f44 : decode_any W_28f44 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f48 : bv 32 := 0x00d505b3.
Lemma F_28f48 : fetch_word Plain.M.loaded_segments (0x29484 : word) = Some W_28f48.
Proof. vm_refl. Qed.
Lemma D_28f48 : decode_any W_28f48 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f4c : bv 32 := 0x10070693.
Lemma F_28f4c : fetch_word Plain.M.loaded_segments (0x29488 : word) = Some W_28f4c.
Proof. vm_refl. Qed.
Lemma D_28f4c : decode_any W_28f4c = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f50 : bv 32 := 0xffc67713.
Lemma F_28f50 : fetch_word Plain.M.loaded_segments (0x2948c : word) = Some W_28f50.
Proof. vm_refl. Qed.
Lemma D_28f50 : decode_any W_28f50 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f54 : bv 32 := 0x02d83633.
Lemma F_28f54 : fetch_word Plain.M.loaded_segments (0x29490 : word) = Some W_28f54.
Proof. vm_refl. Qed.
Lemma D_28f54 : decode_any W_28f54 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f58 : bv 32 := 0x00c5a023.
Lemma F_28f58 : fetch_word Plain.M.loaded_segments (0x29494 : word) = Some W_28f58.
Proof. vm_refl. Qed.
Lemma D_28f58 : decode_any W_28f58 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f5c : bv 32 := 0x00e586b3.
Lemma F_28f5c : fetch_word Plain.M.loaded_segments (0x29498 : word) = Some W_28f5c.
Proof. vm_refl. Qed.
Lemma D_28f5c : decode_any W_28f5c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f60 : bv 32 := 0xfec6ae23.
Lemma F_28f60 : fetch_word Plain.M.loaded_segments (0x2949c : word) = Some W_28f60.
Proof. vm_refl. Qed.
Lemma D_28f60 : decode_any W_28f60 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f64 : bv 32 := 0x08f76063.
Lemma F_28f64 : fetch_word Plain.M.loaded_segments (0x294a0 : word) = Some W_28f64.
Proof. vm_refl. Qed.
Lemma D_28f64 : decode_any W_28f64 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f68 : bv 32 := 0x00c5a223.
Lemma F_28f68 : fetch_word Plain.M.loaded_segments (0x294a4 : word) = Some W_28f68.
Proof. vm_refl. Qed.
Lemma D_28f68 : decode_any W_28f68 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f6c : bv 32 := 0x00c5a423.
Lemma F_28f6c : fetch_word Plain.M.loaded_segments (0x294a8 : word) = Some W_28f6c.
Proof. vm_refl. Qed.
Lemma D_28f6c : decode_any W_28f6c = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f70 : bv 32 := 0x01900793.
Lemma F_28f70 : fetch_word Plain.M.loaded_segments (0x294ac : word) = Some W_28f70.
Proof. vm_refl. Qed.
Lemma D_28f70 : decode_any W_28f70 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f74 : bv 32 := 0xfec6aa23.
Lemma F_28f74 : fetch_word Plain.M.loaded_segments (0x294b0 : word) = Some W_28f74.
Proof. vm_refl. Qed.
Lemma D_28f74 : decode_any W_28f74 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f78 : bv 32 := 0xfec6ac23.
Lemma F_28f78 : fetch_word Plain.M.loaded_segments (0x294b4 : word) = Some W_28f78.
Proof. vm_refl. Qed.
Lemma D_28f78 : decode_any W_28f78 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f7c : bv 32 := 0x06f76463.
Lemma F_28f7c : fetch_word Plain.M.loaded_segments (0x294b8 : word) = Some W_28f7c.
Proof. vm_refl. Qed.
Lemma D_28f7c : decode_any W_28f7c = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f80 : bv 32 := 0x00c5a623.
Lemma F_28f80 : fetch_word Plain.M.loaded_segments (0x294bc : word) = Some W_28f80.
Proof. vm_refl. Qed.
Lemma D_28f80 : decode_any W_28f80 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f84 : bv 32 := 0x00c5a823.
Lemma F_28f84 : fetch_word Plain.M.loaded_segments (0x294c0 : word) = Some W_28f84.
Proof. vm_refl. Qed.
Lemma D_28f84 : decode_any W_28f84 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f88 : bv 32 := 0x00c5aa23.
Lemma F_28f88 : fetch_word Plain.M.loaded_segments (0x294c4 : word) = Some W_28f88.
Proof. vm_refl. Qed.
Lemma D_28f88 : decode_any W_28f88 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f8c : bv 32 := 0x00c5ac23.
Lemma F_28f8c : fetch_word Plain.M.loaded_segments (0x294c8 : word) = Some W_28f8c.
Proof. vm_refl. Qed.
Lemma D_28f8c : decode_any W_28f8c = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f90 : bv 32 := 0x0045f793.
Lemma F_28f90 : fetch_word Plain.M.loaded_segments (0x294cc : word) = Some W_28f90.
Proof. vm_refl. Qed.
Lemma D_28f90 : decode_any W_28f90 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f94 : bv 32 := 0x02000813.
Lemma F_28f94 : fetch_word Plain.M.loaded_segments (0x294d0 : word) = Some W_28f94.
Proof. vm_refl. Qed.
Lemma D_28f94 : decode_any W_28f94 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f98 : bv 32 := 0x01878793.
Lemma F_28f98 : fetch_word Plain.M.loaded_segments (0x294d4 : word) = Some W_28f98.
Proof. vm_refl. Qed.
Lemma D_28f98 : decode_any W_28f98 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28f9c : bv 32 := 0x40f70733.
Lemma F_28f9c : fetch_word Plain.M.loaded_segments (0x294d8 : word) = Some W_28f9c.
Proof. vm_refl. Qed.
Lemma D_28f9c : decode_any W_28f9c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fa0 : bv 32 := 0xfec6a223.
Lemma F_28fa0 : fetch_word Plain.M.loaded_segments (0x294dc : word) = Some W_28fa0.
Proof. vm_refl. Qed.
Lemma D_28fa0 : decode_any W_28fa0 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fa4 : bv 32 := 0xfec6a423.
Lemma F_28fa4 : fetch_word Plain.M.loaded_segments (0x294e0 : word) = Some W_28fa4.
Proof. vm_refl. Qed.
Lemma D_28fa4 : decode_any W_28fa4 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fa8 : bv 32 := 0xfec6a623.
Lemma F_28fa8 : fetch_word Plain.M.loaded_segments (0x294e4 : word) = Some W_28fa8.
Proof. vm_refl. Qed.
Lemma D_28fa8 : decode_any W_28fa8 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fac : bv 32 := 0xfec6a823.
Lemma F_28fac : fetch_word Plain.M.loaded_segments (0x294e8 : word) = Some W_28fac.
Proof. vm_refl. Qed.
Lemma D_28fac : decode_any W_28fac = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fb0 : bv 32 := 0x03076a63.
Lemma F_28fb0 : fetch_word Plain.M.loaded_segments (0x294ec : word) = Some W_28fb0.
Proof. vm_refl. Qed.
Lemma D_28fb0 : decode_any W_28fb0 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fb4 : bv 32 := 0x02061613.
Lemma F_28fb4 : fetch_word Plain.M.loaded_segments (0x294f0 : word) = Some W_28fb4.
Proof. vm_refl. Qed.
Lemma D_28fb4 : decode_any W_28fb4 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fb8 : bv 32 := 0x00f585b3.
Lemma F_28fb8 : fetch_word Plain.M.loaded_segments (0x294f4 : word) = Some W_28fb8.
Proof. vm_refl. Qed.
Lemma D_28fb8 : decode_any W_28fb8 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fbc : bv 32 := 0x02065693.
Lemma F_28fbc : fetch_word Plain.M.loaded_segments (0x294f8 : word) = Some W_28fbc.
Proof. vm_refl. Qed.
Lemma D_28fbc : decode_any W_28fbc = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fc0 : bv 32 := 0x00d66633.
Lemma F_28fc0 : fetch_word Plain.M.loaded_segments (0x294fc : word) = Some W_28fc0.
Proof. vm_refl. Qed.
Lemma D_28fc0 : decode_any W_28fc0 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fc4 : bv 32 := 0x01f00693.
Lemma F_28fc4 : fetch_word Plain.M.loaded_segments (0x29500 : word) = Some W_28fc4.
Proof. vm_refl. Qed.
Lemma D_28fc4 : decode_any W_28fc4 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fc8 : bv 32 := 0x00c5b023.
Lemma F_28fc8 : fetch_word Plain.M.loaded_segments (0x29504 : word) = Some W_28fc8.
Proof. vm_refl. Qed.
Lemma D_28fc8 : decode_any W_28fc8 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fcc : bv 32 := 0x00c5b423.
Lemma F_28fcc : fetch_word Plain.M.loaded_segments (0x29508 : word) = Some W_28fcc.
Proof. vm_refl. Qed.
Lemma D_28fcc : decode_any W_28fcc = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fd0 : bv 32 := 0x00c5b823.
Lemma F_28fd0 : fetch_word Plain.M.loaded_segments (0x2950c : word) = Some W_28fd0.
Proof. vm_refl. Qed.
Lemma D_28fd0 : decode_any W_28fd0 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fd4 : bv 32 := 0x00c5bc23.
Lemma F_28fd4 : fetch_word Plain.M.loaded_segments (0x29510 : word) = Some W_28fd4.
Proof. vm_refl. Qed.
Lemma D_28fd4 : decode_any W_28fd4 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fd8 : bv 32 := 0xfe070713.
Lemma F_28fd8 : fetch_word Plain.M.loaded_segments (0x29514 : word) = Some W_28fd8.
Proof. vm_refl. Qed.
Lemma D_28fd8 : decode_any W_28fd8 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fdc : bv 32 := 0x02058593.
Lemma F_28fdc : fetch_word Plain.M.loaded_segments (0x29518 : word) = Some W_28fdc.
Proof. vm_refl. Qed.
Lemma D_28fdc : decode_any W_28fdc = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fe0 : bv 32 := 0xfee6e4e3.
Lemma F_28fe0 : fetch_word Plain.M.loaded_segments (0x2951c : word) = Some W_28fe0.
Proof. vm_refl. Qed.
Lemma D_28fe0 : decode_any W_28fe0 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_28fe4 : bv 32 := 0x00008067.
Lemma F_28fe4 : fetch_word Plain.M.loaded_segments (0x29520 : word) = Some W_28fe4.
Proof. vm_refl. Qed.
Lemma D_28fe4 : decode_any W_28fe4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
