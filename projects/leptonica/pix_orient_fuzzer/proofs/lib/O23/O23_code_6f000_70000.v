(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)




(* [comment removed for export] *)
Definition W_6f0b8 : bv 32 := 0xf8010113.
Lemma F_6f0b8 : fetch_word Plain.M.loaded_segments (0x6f110 : word) = Some W_6f0b8.
Proof. vm_refl. Qed.
Lemma D_6f0b8 : decode_any W_6f0b8 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f0bc : bv 32 := 0x06113c23.
Lemma F_6f0bc : fetch_word Plain.M.loaded_segments (0x6f114 : word) = Some W_6f0bc.
Proof. vm_refl. Qed.
Lemma D_6f0bc : decode_any W_6f0bc = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f0c0 : bv 32 := 0x06813823.
Lemma F_6f0c0 : fetch_word Plain.M.loaded_segments (0x6f118 : word) = Some W_6f0c0.
Proof. vm_refl. Qed.
Lemma D_6f0c0 : decode_any W_6f0c0 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f0c4 : bv 32 := 0x06913423.
Lemma F_6f0c4 : fetch_word Plain.M.loaded_segments (0x6f11c : word) = Some W_6f0c4.
Proof. vm_refl. Qed.
Lemma D_6f0c4 : decode_any W_6f0c4 = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f0c8 : bv 32 := 0x07213023.
Lemma F_6f0c8 : fetch_word Plain.M.loaded_segments (0x6f120 : word) = Some W_6f0c8.
Proof. vm_refl. Qed.
Lemma D_6f0c8 : decode_any W_6f0c8 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f0cc : bv 32 := 0x05313c23.
Lemma F_6f0cc : fetch_word Plain.M.loaded_segments (0x6f124 : word) = Some W_6f0cc.
Proof. vm_refl. Qed.
Lemma D_6f0cc : decode_any W_6f0cc = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f0d0 : bv 32 := 0x05413823.
Lemma F_6f0d0 : fetch_word Plain.M.loaded_segments (0x6f128 : word) = Some W_6f0d0.
Proof. vm_refl. Qed.
Lemma D_6f0d0 : decode_any W_6f0d0 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f0d4 : bv 32 := 0x05513423.
Lemma F_6f0d4 : fetch_word Plain.M.loaded_segments (0x6f12c : word) = Some W_6f0d4.
Proof. vm_refl. Qed.
Lemma D_6f0d4 : decode_any W_6f0d4 = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f0d8 : bv 32 := 0x05613023.
Lemma F_6f0d8 : fetch_word Plain.M.loaded_segments (0x6f130 : word) = Some W_6f0d8.
Proof. vm_refl. Qed.
Lemma D_6f0d8 : decode_any W_6f0d8 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f0dc : bv 32 := 0x03713c23.
Lemma F_6f0dc : fetch_word Plain.M.loaded_segments (0x6f134 : word) = Some W_6f0dc.
Proof. vm_refl. Qed.
Lemma D_6f0dc : decode_any W_6f0dc = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f0e0 : bv 32 := 0x03813823.
Lemma F_6f0e0 : fetch_word Plain.M.loaded_segments (0x6f138 : word) = Some W_6f0e0.
Proof. vm_refl. Qed.
Lemma D_6f0e0 : decode_any W_6f0e0 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f0e4 : bv 32 := 0x03913423.
Lemma F_6f0e4 : fetch_word Plain.M.loaded_segments (0x6f13c : word) = Some W_6f0e4.
Proof. vm_refl. Qed.
Lemma D_6f0e4 : decode_any W_6f0e4 = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f0e8 : bv 32 := 0x03a13023.
Lemma F_6f0e8 : fetch_word Plain.M.loaded_segments (0x6f140 : word) = Some W_6f0e8.
Proof. vm_refl. Qed.
Lemma D_6f0e8 : decode_any W_6f0e8 = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f0ec : bv 32 := 0x14050463.
Lemma F_6f0ec : fetch_word Plain.M.loaded_segments (0x6f144 : word) = Some W_6f0ec.
Proof. vm_refl. Qed.
Lemma D_6f0ec : decode_any W_6f0ec = Some (Branch BC_EQ 10 0 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f0f0 : bv 32 := 0x00070a13.
Lemma F_6f0f0 : fetch_word Plain.M.loaded_segments (0x6f148 : word) = Some W_6f0f0.
Proof. vm_refl. Qed.
Lemma D_6f0f0 : decode_any W_6f0f0 = Some (OpImm ALU_ADD 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f0f4 : bv 32 := 0x00068493.
Lemma F_6f0f4 : fetch_word Plain.M.loaded_segments (0x6f14c : word) = Some W_6f0f4.
Proof. vm_refl. Qed.
Lemma D_6f0f4 : decode_any W_6f0f4 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f0f8 : bv 32 := 0x00060a93.
Lemma F_6f0f8 : fetch_word Plain.M.loaded_segments (0x6f150 : word) = Some W_6f0f8.
Proof. vm_refl. Qed.
Lemma D_6f0f8 : decode_any W_6f0f8 = Some (OpImm ALU_ADD 21 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f0fc : bv 32 := 0x00058913.
Lemma F_6f0fc : fetch_word Plain.M.loaded_segments (0x6f154 : word) = Some W_6f0fc.
Proof. vm_refl. Qed.
Lemma D_6f0fc : decode_any W_6f0fc = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f100 : bv 32 := 0x00050413.
Lemma F_6f100 : fetch_word Plain.M.loaded_segments (0x6f158 : word) = Some W_6f100.
Proof. vm_refl. Qed.
Lemma D_6f100 : decode_any W_6f100 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f104 : bv 32 := 0x00b66533.
Lemma F_6f104 : fetch_word Plain.M.loaded_segments (0x6f15c : word) = Some W_6f104.
Proof. vm_refl. Qed.
Lemma D_6f104 : decode_any W_6f104 = Some (Op ALU_OR 10 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f108 : bv 32 := 0x00e6e5b3.
Lemma F_6f108 : fetch_word Plain.M.loaded_segments (0x6f160 : word) = Some W_6f108.
Proof. vm_refl. Qed.
Lemma D_6f108 : decode_any W_6f108 = Some (Op ALU_OR 11 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f10c : bv 32 := 0x00b56533.
Lemma F_6f10c : fetch_word Plain.M.loaded_segments (0x6f164 : word) = Some W_6f10c.
Proof. vm_refl. Qed.
Lemma D_6f10c : decode_any W_6f10c = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f110 : bv 32 := 0x14054663.
Lemma F_6f110 : fetch_word Plain.M.loaded_segments (0x6f168 : word) = Some W_6f110.
Proof. vm_refl. Qed.
Lemma D_6f110 : decode_any W_6f110 = Some (Branch BC_LT 10 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f114 : bv 32 := 0x00078d13.
Lemma F_6f114 : fetch_word Plain.M.loaded_segments (0x6f16c : word) = Some W_6f114.
Proof. vm_refl. Qed.
Lemma D_6f114 : decode_any W_6f114 = Some (OpImm ALU_ADD 26 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f118 : bv 32 := 0x01c10593.
Lemma F_6f118 : fetch_word Plain.M.loaded_segments (0x6f170 : word) = Some W_6f118.
Proof. vm_refl. Qed.
Lemma D_6f118 : decode_any W_6f118 = Some (OpImm ALU_ADD 11 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f11c : bv 32 := 0x01810613.
Lemma F_6f11c : fetch_word Plain.M.loaded_segments (0x6f174 : word) = Some W_6f11c.
Proof. vm_refl. Qed.
Lemma D_6f11c : decode_any W_6f11c = Some (OpImm ALU_ADD 12 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f120 : bv 32 := 0x01410693.
Lemma F_6f120 : fetch_word Plain.M.loaded_segments (0x6f178 : word) = Some W_6f120.
Proof. vm_refl. Qed.
Lemma D_6f120 : decode_any W_6f120 = Some (OpImm ALU_ADD 13 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f124 : bv 32 := 0x00040513.
Lemma F_6f124 : fetch_word Plain.M.loaded_segments (0x6f17c : word) = Some W_6f124.
Proof. vm_refl. Qed.
Lemma D_6f124 : decode_any W_6f124 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f128 : bv 32 := 0xc79fd0ef.
Lemma F_6f128 : fetch_word Plain.M.loaded_segments (0x6f180 : word) = Some W_6f128.
Proof. vm_refl. Qed.
Lemma D_6f128 : decode_any W_6f128 = Some (Jal 1 2088056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f12c : bv 32 := 0x01c12503.
Lemma F_6f12c : fetch_word Plain.M.loaded_segments (0x6f184 : word) = Some W_6f12c.
Proof. vm_refl. Qed.
Lemma D_6f12c : decode_any W_6f12c = Some (Load SZ4 true 10 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f130 : bv 32 := 0x01812583.
Lemma F_6f130 : fetch_word Plain.M.loaded_segments (0x6f188 : word) = Some W_6f130.
Proof. vm_refl. Qed.
Lemma D_6f130 : decode_any W_6f130 = Some (Load SZ4 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f134 : bv 32 := 0x01412603.
Lemma F_6f134 : fetch_word Plain.M.loaded_segments (0x6f18c : word) = Some W_6f134.
Proof. vm_refl. Qed.
Lemma D_6f134 : decode_any W_6f134 = Some (Load SZ4 true 12 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f138 : bv 32 := 0x01250c3b.
Lemma F_6f138 : fetch_word Plain.M.loaded_segments (0x6f190 : word) = Some W_6f138.
Proof. vm_refl. Qed.
Lemma D_6f138 : decode_any W_6f138 = Some (Op32 ALU_ADD 24 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f13c : bv 32 := 0x00958bbb.
Lemma F_6f13c : fetch_word Plain.M.loaded_segments (0x6f194 : word) = Some W_6f13c.
Proof. vm_refl. Qed.
Lemma D_6f13c : decode_any W_6f13c = Some (Op32 ALU_ADD 23 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f140 : bv 32 := 0x015c0b3b.
Lemma F_6f140 : fetch_word Plain.M.loaded_segments (0x6f198 : word) = Some W_6f140.
Proof. vm_refl. Qed.
Lemma D_6f140 : decode_any W_6f140 = Some (Op32 ALU_ADD 22 24 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f144 : bv 32 := 0x014b8cbb.
Lemma F_6f144 : fetch_word Plain.M.loaded_segments (0x6f19c : word) = Some W_6f144.
Proof. vm_refl. Qed.
Lemma D_6f144 : decode_any W_6f144 = Some (Op32 ALU_ADD 25 23 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f148 : bv 32 := 0x000b0513.
Lemma F_6f148 : fetch_word Plain.M.loaded_segments (0x6f1a0 : word) = Some W_6f148.
Proof. vm_refl. Qed.
Lemma D_6f148 : decode_any W_6f148 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f14c : bv 32 := 0x000c8593.
Lemma F_6f14c : fetch_word Plain.M.loaded_segments (0x6f1a4 : word) = Some W_6f14c.
Proof. vm_refl. Qed.
Lemma D_6f14c : decode_any W_6f14c = Some (OpImm ALU_ADD 11 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f150 : bv 32 := 0xc90fd0ef.
Lemma F_6f150 : fetch_word Plain.M.loaded_segments (0x6f1a8 : word) = Some W_6f150.
Proof. vm_refl. Qed.
Lemma D_6f150 : decode_any W_6f150 = Some (Jal 1 2086032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f154 : bv 32 := 0x16050463.
Lemma F_6f154 : fetch_word Plain.M.loaded_segments (0x6f1ac : word) = Some W_6f154.
Proof. vm_refl. Qed.
Lemma D_6f154 : decode_any W_6f154 = Some (Branch BC_EQ 10 0 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f158 : bv 32 := 0x00050993.
Lemma F_6f158 : fetch_word Plain.M.loaded_segments (0x6f1b0 : word) = Some W_6f158.
Proof. vm_refl. Qed.
Lemma D_6f158 : decode_any W_6f158 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f15c : bv 32 := 0x00040593.
Lemma F_6f15c : fetch_word Plain.M.loaded_segments (0x6f1b4 : word) = Some W_6f15c.
Proof. vm_refl. Qed.
Lemma D_6f15c : decode_any W_6f15c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f160 : bv 32 := 0xd91fd0ef.
Lemma F_6f160 : fetch_word Plain.M.loaded_segments (0x6f1b8 : word) = Some W_6f160.
Proof. vm_refl. Qed.
Lemma D_6f160 : decode_any W_6f160 = Some (Jal 1 2088336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f164 : bv 32 := 0x00098513.
Lemma F_6f164 : fetch_word Plain.M.loaded_segments (0x6f1bc : word) = Some W_6f164.
Proof. vm_refl. Qed.
Lemma D_6f164 : decode_any W_6f164 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f168 : bv 32 := 0x00040593.
Lemma F_6f168 : fetch_word Plain.M.loaded_segments (0x6f1c0 : word) = Some W_6f168.
Proof. vm_refl. Qed.
Lemma D_6f168 : decode_any W_6f168 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f16c : bv 32 := 0xe0dfd0ef.
Lemma F_6f16c : fetch_word Plain.M.loaded_segments (0x6f1c4 : word) = Some W_6f16c.
Proof. vm_refl. Qed.
Lemma D_6f16c : decode_any W_6f16c = Some (Jal 1 2088460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f170 : bv 32 := 0x020d0063.
Lemma F_6f170 : fetch_word Plain.M.loaded_segments (0x6f1c8 : word) = Some W_6f170.
Proof. vm_refl. Qed.
Lemma D_6f170 : decode_any W_6f170 = Some (Branch BC_EQ 26 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f174 : bv 32 := 0x000d0593.
Lemma F_6f174 : fetch_word Plain.M.loaded_segments (0x6f1cc : word) = Some W_6f174.
Proof. vm_refl. Qed.
Lemma D_6f174 : decode_any W_6f174 = Some (OpImm ALU_ADD 11 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f178 : bv 32 := 0x01416503.
Lemma F_6f178 : fetch_word Plain.M.loaded_segments (0x6f1d0 : word) = Some W_6f178.
Proof. vm_refl. Qed.
Lemma D_6f178 : decode_any W_6f178 = Some (Load SZ4 false 10 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f17c : bv 32 := 0x02000613.
Lemma F_6f17c : fetch_word Plain.M.loaded_segments (0x6f1d4 : word) = Some W_6f17c.
Proof. vm_refl. Qed.
Lemma D_6f17c : decode_any W_6f17c = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f180 : bv 32 := 0x16c51c63.
Lemma F_6f180 : fetch_word Plain.M.loaded_segments (0x6f1d8 : word) = Some W_6f180.
Proof. vm_refl. Qed.
Lemma D_6f180 : decode_any W_6f180 = Some (Branch BC_NE 10 12 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f18c : bv 32 := 0x00f00d13.
Lemma F_6f18c : fetch_word Plain.M.loaded_segments (0x6f1e4 : word) = Some W_6f18c.
Proof. vm_refl. Qed.
Lemma D_6f18c : decode_any W_6f18c = Some (OpImm ALU_ADD 26 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f190 : bv 32 := 0x00013023.
Lemma F_6f190 : fetch_word Plain.M.loaded_segments (0x6f1e8 : word) = Some W_6f190.
Proof. vm_refl. Qed.
Lemma D_6f190 : decode_any W_6f190 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f194 : bv 32 := 0x00098513.
Lemma F_6f194 : fetch_word Plain.M.loaded_segments (0x6f1ec : word) = Some W_6f194.
Proof. vm_refl. Qed.
Lemma D_6f194 : decode_any W_6f194 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f198 : bv 32 := 0x00000593.
Lemma F_6f198 : fetch_word Plain.M.loaded_segments (0x6f1f0 : word) = Some W_6f198.
Proof. vm_refl. Qed.
Lemma D_6f198 : decode_any W_6f198 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f19c : bv 32 := 0x00000613.
Lemma F_6f19c : fetch_word Plain.M.loaded_segments (0x6f1f4 : word) = Some W_6f19c.
Proof. vm_refl. Qed.
Lemma D_6f19c : decode_any W_6f19c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1a0 : bv 32 := 0x00090693.
Lemma F_6f1a0 : fetch_word Plain.M.loaded_segments (0x6f1f8 : word) = Some W_6f1a0.
Proof. vm_refl. Qed.
Lemma D_6f1a0 : decode_any W_6f1a0 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1a4 : bv 32 := 0x000c8713.
Lemma F_6f1a4 : fetch_word Plain.M.loaded_segments (0x6f1fc : word) = Some W_6f1a4.
Proof. vm_refl. Qed.
Lemma D_6f1a4 : decode_any W_6f1a4 = Some (OpImm ALU_ADD 14 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1a8 : bv 32 := 0x000d0793.
Lemma F_6f1a8 : fetch_word Plain.M.loaded_segments (0x6f200 : word) = Some W_6f1a8.
Proof. vm_refl. Qed.
Lemma D_6f1a8 : decode_any W_6f1a8 = Some (OpImm ALU_ADD 15 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1ac : bv 32 := 0x00000813.
Lemma F_6f1ac : fetch_word Plain.M.loaded_segments (0x6f204 : word) = Some W_6f1ac.
Proof. vm_refl. Qed.
Lemma D_6f1ac : decode_any W_6f1ac = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1b0 : bv 32 := 0x00000893.
Lemma F_6f1b0 : fetch_word Plain.M.loaded_segments (0x6f208 : word) = Some W_6f1b0.
Proof. vm_refl. Qed.
Lemma D_6f1b0 : decode_any W_6f1b0 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1b4 : bv 32 := 0x5a00a0ef.
Lemma F_6f1b4 : fetch_word Plain.M.loaded_segments (0x6f20c : word) = Some W_6f1b4.
Proof. vm_refl. Qed.
Lemma D_6f1b4 : decode_any W_6f1b4 = Some (Jal 1 42400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1b8 : bv 32 := 0x00013023.
Lemma F_6f1b8 : fetch_word Plain.M.loaded_segments (0x6f210 : word) = Some W_6f1b8.
Proof. vm_refl. Qed.
Lemma D_6f1b8 : decode_any W_6f1b8 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1bc : bv 32 := 0x00098513.
Lemma F_6f1bc : fetch_word Plain.M.loaded_segments (0x6f214 : word) = Some W_6f1bc.
Proof. vm_refl. Qed.
Lemma D_6f1bc : decode_any W_6f1bc = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1c0 : bv 32 := 0x000c0593.
Lemma F_6f1c0 : fetch_word Plain.M.loaded_segments (0x6f218 : word) = Some W_6f1c0.
Proof. vm_refl. Qed.
Lemma D_6f1c0 : decode_any W_6f1c0 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1c4 : bv 32 := 0x00000613.
Lemma F_6f1c4 : fetch_word Plain.M.loaded_segments (0x6f21c : word) = Some W_6f1c4.
Proof. vm_refl. Qed.
Lemma D_6f1c4 : decode_any W_6f1c4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1c8 : bv 32 := 0x000a8693.
Lemma F_6f1c8 : fetch_word Plain.M.loaded_segments (0x6f220 : word) = Some W_6f1c8.
Proof. vm_refl. Qed.
Lemma D_6f1c8 : decode_any W_6f1c8 = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1cc : bv 32 := 0x000c8713.
Lemma F_6f1cc : fetch_word Plain.M.loaded_segments (0x6f224 : word) = Some W_6f1cc.
Proof. vm_refl. Qed.
Lemma D_6f1cc : decode_any W_6f1cc = Some (OpImm ALU_ADD 14 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1d0 : bv 32 := 0x000d0793.
Lemma F_6f1d0 : fetch_word Plain.M.loaded_segments (0x6f228 : word) = Some W_6f1d0.
Proof. vm_refl. Qed.
Lemma D_6f1d0 : decode_any W_6f1d0 = Some (OpImm ALU_ADD 15 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1d4 : bv 32 := 0x00000813.
Lemma F_6f1d4 : fetch_word Plain.M.loaded_segments (0x6f22c : word) = Some W_6f1d4.
Proof. vm_refl. Qed.
Lemma D_6f1d4 : decode_any W_6f1d4 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1d8 : bv 32 := 0x00000893.
Lemma F_6f1d8 : fetch_word Plain.M.loaded_segments (0x6f230 : word) = Some W_6f1d8.
Proof. vm_refl. Qed.
Lemma D_6f1d8 : decode_any W_6f1d8 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1dc : bv 32 := 0x5780a0ef.
Lemma F_6f1dc : fetch_word Plain.M.loaded_segments (0x6f234 : word) = Some W_6f1dc.
Proof. vm_refl. Qed.
Lemma D_6f1dc : decode_any W_6f1dc = Some (Jal 1 42360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1e0 : bv 32 := 0x00013023.
Lemma F_6f1e0 : fetch_word Plain.M.loaded_segments (0x6f238 : word) = Some W_6f1e0.
Proof. vm_refl. Qed.
Lemma D_6f1e0 : decode_any W_6f1e0 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1e4 : bv 32 := 0x00098513.
Lemma F_6f1e4 : fetch_word Plain.M.loaded_segments (0x6f23c : word) = Some W_6f1e4.
Proof. vm_refl. Qed.
Lemma D_6f1e4 : decode_any W_6f1e4 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1e8 : bv 32 := 0x00000593.
Lemma F_6f1e8 : fetch_word Plain.M.loaded_segments (0x6f240 : word) = Some W_6f1e8.
Proof. vm_refl. Qed.
Lemma D_6f1e8 : decode_any W_6f1e8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1ec : bv 32 := 0x00000613.
Lemma F_6f1ec : fetch_word Plain.M.loaded_segments (0x6f244 : word) = Some W_6f1ec.
Proof. vm_refl. Qed.
Lemma D_6f1ec : decode_any W_6f1ec = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1f0 : bv 32 := 0x000b0693.
Lemma F_6f1f0 : fetch_word Plain.M.loaded_segments (0x6f248 : word) = Some W_6f1f0.
Proof. vm_refl. Qed.
Lemma D_6f1f0 : decode_any W_6f1f0 = Some (OpImm ALU_ADD 13 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1f4 : bv 32 := 0x00048713.
Lemma F_6f1f4 : fetch_word Plain.M.loaded_segments (0x6f24c : word) = Some W_6f1f4.
Proof. vm_refl. Qed.
Lemma D_6f1f4 : decode_any W_6f1f4 = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1f8 : bv 32 := 0x000d0793.
Lemma F_6f1f8 : fetch_word Plain.M.loaded_segments (0x6f250 : word) = Some W_6f1f8.
Proof. vm_refl. Qed.
Lemma D_6f1f8 : decode_any W_6f1f8 = Some (OpImm ALU_ADD 15 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f1fc : bv 32 := 0x00000813.
Lemma F_6f1fc : fetch_word Plain.M.loaded_segments (0x6f254 : word) = Some W_6f1fc.
Proof. vm_refl. Qed.
Lemma D_6f1fc : decode_any W_6f1fc = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f200 : bv 32 := 0x00000893.
Lemma F_6f200 : fetch_word Plain.M.loaded_segments (0x6f258 : word) = Some W_6f200.
Proof. vm_refl. Qed.
Lemma D_6f200 : decode_any W_6f200 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f204 : bv 32 := 0x5500a0ef.
Lemma F_6f204 : fetch_word Plain.M.loaded_segments (0x6f25c : word) = Some W_6f204.
Proof. vm_refl. Qed.
Lemma D_6f204 : decode_any W_6f204 = Some (Jal 1 42320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f208 : bv 32 := 0x00013023.
Lemma F_6f208 : fetch_word Plain.M.loaded_segments (0x6f260 : word) = Some W_6f208.
Proof. vm_refl. Qed.
Lemma D_6f208 : decode_any W_6f208 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f20c : bv 32 := 0x00098513.
Lemma F_6f20c : fetch_word Plain.M.loaded_segments (0x6f264 : word) = Some W_6f20c.
Proof. vm_refl. Qed.
Lemma D_6f20c : decode_any W_6f20c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f210 : bv 32 := 0x00000593.
Lemma F_6f210 : fetch_word Plain.M.loaded_segments (0x6f268 : word) = Some W_6f210.
Proof. vm_refl. Qed.
Lemma D_6f210 : decode_any W_6f210 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f214 : bv 32 := 0x000b8613.
Lemma F_6f214 : fetch_word Plain.M.loaded_segments (0x6f26c : word) = Some W_6f214.
Proof. vm_refl. Qed.
Lemma D_6f214 : decode_any W_6f214 = Some (OpImm ALU_ADD 12 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f218 : bv 32 := 0x000b0693.
Lemma F_6f218 : fetch_word Plain.M.loaded_segments (0x6f270 : word) = Some W_6f218.
Proof. vm_refl. Qed.
Lemma D_6f218 : decode_any W_6f218 = Some (OpImm ALU_ADD 13 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f21c : bv 32 := 0x000a0713.
Lemma F_6f21c : fetch_word Plain.M.loaded_segments (0x6f274 : word) = Some W_6f21c.
Proof. vm_refl. Qed.
Lemma D_6f21c : decode_any W_6f21c = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f220 : bv 32 := 0x000d0793.
Lemma F_6f220 : fetch_word Plain.M.loaded_segments (0x6f278 : word) = Some W_6f220.
Proof. vm_refl. Qed.
Lemma D_6f220 : decode_any W_6f220 = Some (OpImm ALU_ADD 15 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f224 : bv 32 := 0x00000813.
Lemma F_6f224 : fetch_word Plain.M.loaded_segments (0x6f27c : word) = Some W_6f224.
Proof. vm_refl. Qed.
Lemma D_6f224 : decode_any W_6f224 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f228 : bv 32 := 0x00000893.
Lemma F_6f228 : fetch_word Plain.M.loaded_segments (0x6f280 : word) = Some W_6f228.
Proof. vm_refl. Qed.
Lemma D_6f228 : decode_any W_6f228 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f22c : bv 32 := 0x5280a0ef.
Lemma F_6f22c : fetch_word Plain.M.loaded_segments (0x6f284 : word) = Some W_6f22c.
Proof. vm_refl. Qed.
Lemma D_6f22c : decode_any W_6f22c = Some (Jal 1 42280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f230 : bv 32 := 0x0e00006f.
Lemma F_6f230 : fetch_word Plain.M.loaded_segments (0x6f288 : word) = Some W_6f230.
Proof. vm_refl. Qed.
Lemma D_6f230 : decode_any W_6f230 = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f2bc : bv 32 := 0x000a3517.
Lemma F_6f2bc : fetch_word Plain.M.loaded_segments (0x6f314 : word) = Some W_6f2bc.
Proof. vm_refl. Qed.
Lemma D_6f2bc : decode_any W_6f2bc = Some (Auipc 10 163, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f2c0 : bv 32 := 0x2b453503.
Lemma F_6f2c0 : fetch_word Plain.M.loaded_segments (0x6f318 : word) = Some W_6f2c0.
Proof. vm_refl. Qed.
Lemma D_6f2c0 : decode_any W_6f2c0 = Some (Load SZ8 true 10 10 692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f2c4 : bv 32 := 0x00052503.
Lemma F_6f2c4 : fetch_word Plain.M.loaded_segments (0x6f31c : word) = Some W_6f2c4.
Proof. vm_refl. Qed.
Lemma D_6f2c4 : decode_any W_6f2c4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f2c8 : bv 32 := 0x00500593.
Lemma F_6f2c8 : fetch_word Plain.M.loaded_segments (0x6f320 : word) = Some W_6f2c8.
Proof. vm_refl. Qed.
Lemma D_6f2c8 : decode_any W_6f2c8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f2cc : bv 32 := 0x02a5c263.
Lemma F_6f2cc : fetch_word Plain.M.loaded_segments (0x6f324 : word) = Some W_6f2cc.
Proof. vm_refl. Qed.
Lemma D_6f2cc : decode_any W_6f2cc = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f2d0 : bv 32 := 0xfffa3517.
Lemma F_6f2d0 : fetch_word Plain.M.loaded_segments (0x6f328 : word) = Some W_6f2d0.
Proof. vm_refl. Qed.
Lemma D_6f2d0 : decode_any W_6f2d0 = Some (Auipc 10 1048483, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f2d4 : bv 32 := 0xfffa8597.
Lemma F_6f2d4 : fetch_word Plain.M.loaded_segments (0x6f32c : word) = Some W_6f2d4.
Proof. vm_refl. Qed.
Lemma D_6f2d4 : decode_any W_6f2d4 = Some (Auipc 11 1048488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f2d8 : bv 32 := 0x3b250513.
Lemma F_6f2d8 : fetch_word Plain.M.loaded_segments (0x6f330 : word) = Some W_6f2d8.
Proof. vm_refl. Qed.
Lemma D_6f2d8 : decode_any W_6f2d8 = Some (OpImm ALU_ADD 10 10 946, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f2dc : bv 32 := 0xdce58593.
Lemma F_6f2dc : fetch_word Plain.M.loaded_segments (0x6f334 : word) = Some W_6f2dc.
Proof. vm_refl. Qed.
Lemma D_6f2dc : decode_any W_6f2dc = Some (OpImm ALU_ADD 11 11 3534, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f2e0 : bv 32 := 0x00000613.
Lemma F_6f2e0 : fetch_word Plain.M.loaded_segments (0x6f338 : word) = Some W_6f2e0.
Proof. vm_refl. Qed.
Lemma D_6f2e0 : decode_any W_6f2e0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f2e4 : bv 32 := 0xde1f30ef.
Lemma F_6f2e4 : fetch_word Plain.M.loaded_segments (0x6f33c : word) = Some W_6f2e4.
Proof. vm_refl. Qed.
Lemma D_6f2e4 : decode_any W_6f2e4 = Some (Jal 1 2047456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f2e8 : bv 32 := 0x00050993.
Lemma F_6f2e8 : fetch_word Plain.M.loaded_segments (0x6f340 : word) = Some W_6f2e8.
Proof. vm_refl. Qed.
Lemma D_6f2e8 : decode_any W_6f2e8 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f2ec : bv 32 := 0x04c0006f.
Lemma F_6f2ec : fetch_word Plain.M.loaded_segments (0x6f344 : word) = Some W_6f2ec.
Proof. vm_refl. Qed.
Lemma D_6f2ec : decode_any W_6f2ec = Some (Jal 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f2f8 : bv 32 := 0xfff00613.
Lemma F_6f2f8 : fetch_word Plain.M.loaded_segments (0x6f350 : word) = Some W_6f2f8.
Proof. vm_refl. Qed.
Lemma D_6f2f8 : decode_any W_6f2f8 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f2fc : bv 32 := 0x00a6153b.
Lemma F_6f2fc : fetch_word Plain.M.loaded_segments (0x6f354 : word) = Some W_6f2fc.
Proof. vm_refl. Qed.
Lemma D_6f2fc : decode_any W_6f2fc = Some (Op32 ALU_SLL 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f300 : bv 32 := 0xfff54513.
Lemma F_6f300 : fetch_word Plain.M.loaded_segments (0x6f358 : word) = Some W_6f300.
Proof. vm_refl. Qed.
Lemma D_6f300 : decode_any W_6f300 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f304 : bv 32 := 0xe8a5f4e3.
Lemma F_6f304 : fetch_word Plain.M.loaded_segments (0x6f35c : word) = Some W_6f304.
Proof. vm_refl. Qed.
Lemma D_6f304 : decode_any W_6f304 = Some (Branch BC_GEU 11 10 7816, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f310 : bv 32 := 0x01c12683.
Lemma F_6f310 : fetch_word Plain.M.loaded_segments (0x6f368 : word) = Some W_6f310.
Proof. vm_refl. Qed.
Lemma D_6f310 : decode_any W_6f310 = Some (Load SZ4 true 13 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f314 : bv 32 := 0x01812703.
Lemma F_6f314 : fetch_word Plain.M.loaded_segments (0x6f36c : word) = Some W_6f314.
Proof. vm_refl. Qed.
Lemma D_6f314 : decode_any W_6f314 = Some (Load SZ4 true 14 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f318 : bv 32 := 0x00c00793.
Lemma F_6f318 : fetch_word Plain.M.loaded_segments (0x6f370 : word) = Some W_6f318.
Proof. vm_refl. Qed.
Lemma D_6f318 : decode_any W_6f318 = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f31c : bv 32 := 0x00013023.
Lemma F_6f31c : fetch_word Plain.M.loaded_segments (0x6f374 : word) = Some W_6f31c.
Proof. vm_refl. Qed.
Lemma D_6f31c : decode_any W_6f31c = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f320 : bv 32 := 0x00098513.
Lemma F_6f320 : fetch_word Plain.M.loaded_segments (0x6f378 : word) = Some W_6f320.
Proof. vm_refl. Qed.
Lemma D_6f320 : decode_any W_6f320 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f324 : bv 32 := 0x00090593.
Lemma F_6f324 : fetch_word Plain.M.loaded_segments (0x6f37c : word) = Some W_6f324.
Proof. vm_refl. Qed.
Lemma D_6f324 : decode_any W_6f324 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f328 : bv 32 := 0x00048613.
Lemma F_6f328 : fetch_word Plain.M.loaded_segments (0x6f380 : word) = Some W_6f328.
Proof. vm_refl. Qed.
Lemma D_6f328 : decode_any W_6f328 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f32c : bv 32 := 0x00040813.
Lemma F_6f32c : fetch_word Plain.M.loaded_segments (0x6f384 : word) = Some W_6f32c.
Proof. vm_refl. Qed.
Lemma D_6f32c : decode_any W_6f32c = Some (OpImm ALU_ADD 16 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f330 : bv 32 := 0x00000893.
Lemma F_6f330 : fetch_word Plain.M.loaded_segments (0x6f388 : word) = Some W_6f330.
Proof. vm_refl. Qed.
Lemma D_6f330 : decode_any W_6f330 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f334 : bv 32 := 0x4200a0ef.
Lemma F_6f334 : fetch_word Plain.M.loaded_segments (0x6f38c : word) = Some W_6f334.
Proof. vm_refl. Qed.
Lemma D_6f334 : decode_any W_6f334 = Some (Jal 1 42016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f338 : bv 32 := 0x00098513.
Lemma F_6f338 : fetch_word Plain.M.loaded_segments (0x6f390 : word) = Some W_6f338.
Proof. vm_refl. Qed.
Lemma D_6f338 : decode_any W_6f338 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f33c : bv 32 := 0x07813083.
Lemma F_6f33c : fetch_word Plain.M.loaded_segments (0x6f394 : word) = Some W_6f33c.
Proof. vm_refl. Qed.
Lemma D_6f33c : decode_any W_6f33c = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f340 : bv 32 := 0x07013403.
Lemma F_6f340 : fetch_word Plain.M.loaded_segments (0x6f398 : word) = Some W_6f340.
Proof. vm_refl. Qed.
Lemma D_6f340 : decode_any W_6f340 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f344 : bv 32 := 0x06813483.
Lemma F_6f344 : fetch_word Plain.M.loaded_segments (0x6f39c : word) = Some W_6f344.
Proof. vm_refl. Qed.
Lemma D_6f344 : decode_any W_6f344 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f348 : bv 32 := 0x06013903.
Lemma F_6f348 : fetch_word Plain.M.loaded_segments (0x6f3a0 : word) = Some W_6f348.
Proof. vm_refl. Qed.
Lemma D_6f348 : decode_any W_6f348 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f34c : bv 32 := 0x05813983.
Lemma F_6f34c : fetch_word Plain.M.loaded_segments (0x6f3a4 : word) = Some W_6f34c.
Proof. vm_refl. Qed.
Lemma D_6f34c : decode_any W_6f34c = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f350 : bv 32 := 0x05013a03.
Lemma F_6f350 : fetch_word Plain.M.loaded_segments (0x6f3a8 : word) = Some W_6f350.
Proof. vm_refl. Qed.
Lemma D_6f350 : decode_any W_6f350 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f354 : bv 32 := 0x04813a83.
Lemma F_6f354 : fetch_word Plain.M.loaded_segments (0x6f3ac : word) = Some W_6f354.
Proof. vm_refl. Qed.
Lemma D_6f354 : decode_any W_6f354 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f358 : bv 32 := 0x04013b03.
Lemma F_6f358 : fetch_word Plain.M.loaded_segments (0x6f3b0 : word) = Some W_6f358.
Proof. vm_refl. Qed.
Lemma D_6f358 : decode_any W_6f358 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f35c : bv 32 := 0x03813b83.
Lemma F_6f35c : fetch_word Plain.M.loaded_segments (0x6f3b4 : word) = Some W_6f35c.
Proof. vm_refl. Qed.
Lemma D_6f35c : decode_any W_6f35c = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f360 : bv 32 := 0x03013c03.
Lemma F_6f360 : fetch_word Plain.M.loaded_segments (0x6f3b8 : word) = Some W_6f360.
Proof. vm_refl. Qed.
Lemma D_6f360 : decode_any W_6f360 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f364 : bv 32 := 0x02813c83.
Lemma F_6f364 : fetch_word Plain.M.loaded_segments (0x6f3bc : word) = Some W_6f364.
Proof. vm_refl. Qed.
Lemma D_6f364 : decode_any W_6f364 = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f368 : bv 32 := 0x02013d03.
Lemma F_6f368 : fetch_word Plain.M.loaded_segments (0x6f3c0 : word) = Some W_6f368.
Proof. vm_refl. Qed.
Lemma D_6f368 : decode_any W_6f368 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f36c : bv 32 := 0x08010113.
Lemma F_6f36c : fetch_word Plain.M.loaded_segments (0x6f3c4 : word) = Some W_6f36c.
Proof. vm_refl. Qed.
Lemma D_6f36c : decode_any W_6f36c = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f370 : bv 32 := 0x00008067.
Lemma F_6f370 : fetch_word Plain.M.loaded_segments (0x6f3c8 : word) = Some W_6f370.
Proof. vm_refl. Qed.
Lemma D_6f370 : decode_any W_6f370 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
