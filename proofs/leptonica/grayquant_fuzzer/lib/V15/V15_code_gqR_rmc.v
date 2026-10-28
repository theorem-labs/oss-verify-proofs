(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_178cc : bv 32 := 0x06c5a02f.
Lemma F_178cc : fetch_word Ubsan.M.loaded_segments (0x179d0 : word) = Some W_178cc.
Proof. vm_refl. Qed.
Lemma D_178cc : decode_any W_178cc = Some (Amo AMO_ADD AW true true 0 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178d0 : bv 32 := 0x00008067.
Lemma F_178d0 : fetch_word Ubsan.M.loaded_segments (0x179d4 : word) = Some W_178d0.
Proof. vm_refl. Qed.
Lemma D_178d0 : decode_any W_178d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a7cc : bv 32 := 0xf00887d3.
Lemma F_1a7cc : fetch_word Ubsan.M.loaded_segments (0x1a8d0 : word) = Some W_1a7cc.
Proof. vm_refl. Qed.
Lemma D_1a7cc : decode_any W_1a7cc = Some (Fmv FMV_F_X FMT_S 15 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a7d0 : bv 32 := 0xe682a707.
Lemma F_1a7d0 : fetch_word Ubsan.M.loaded_segments (0x1a8d4 : word) = Some W_1a7d0.
Proof. vm_refl. Qed.
Lemma D_1a7d0 : decode_any W_1a7d0 = Some (FLoad FMT_S 14 5 3688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a7d4 : bv 32 := 0xe5832687.
Lemma F_1a7d4 : fetch_word Ubsan.M.loaded_segments (0x1a8d8 : word) = Some W_1a7d4.
Proof. vm_refl. Qed.
Lemma D_1a7d4 : decode_any W_1a7d4 = Some (FLoad FMT_S 13 6 3672, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a7d8 : bv 32 := 0xd783b607.
Lemma F_1a7d8 : fetch_word Ubsan.M.loaded_segments (0x1a8dc : word) = Some W_1a7d8.
Proof. vm_refl. Qed.
Lemma D_1a7d8 : decode_any W_1a7d8 = Some (FLoad FMT_D 12 7 3448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a7dc : bv 32 := 0xd44e3587.
Lemma F_1a7dc : fetch_word Ubsan.M.loaded_segments (0x1a8e0 : word) = Some W_1a7dc.
Proof. vm_refl. Qed.
Lemma D_1a7dc : decode_any W_1a7dc = Some (FLoad FMT_D 11 28 3396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a7e0 : bv 32 := 0xd50eb507.
Lemma F_1a7e0 : fetch_word Ubsan.M.loaded_segments (0x1a8e4 : word) = Some W_1a7e0.
Proof. vm_refl. Qed.
Lemma D_1a7e0 : decode_any W_1a7e0 = Some (FLoad FMT_D 10 29 3408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a870 : bv 32 := 0xd00ff053.
Lemma F_1a870 : fetch_word Ubsan.M.loaded_segments (0x1a974 : word) = Some W_1a870.
Proof. vm_refl. Qed.
Lemma D_1a870 : decode_any W_1a870 = Some (Fcvt FC_S FC_W 0 31 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a874 : bv 32 := 0xd00470d3.
Lemma F_1a874 : fetch_word Ubsan.M.loaded_segments (0x1a978 : word) = Some W_1a874.
Proof. vm_refl. Qed.
Lemma D_1a874 : decode_any W_1a874 = Some (Fcvt FC_S FC_W 1 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a878 : bv 32 := 0x10f0f0d3.
Lemma F_1a878 : fetch_word Ubsan.M.loaded_segments (0x1a97c : word) = Some W_1a878.
Proof. vm_refl. Qed.
Lemma D_1a878 : decode_any W_1a878 = Some (Fari F_MUL FMT_S 1 1 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a87c : bv 32 := 0x08e07043.
Lemma F_1a87c : fetch_word Ubsan.M.loaded_segments (0x1a980 : word) = Some W_1a87c.
Proof. vm_refl. Qed.
Lemma D_1a87c : decode_any W_1a87c = Some (Fma F_MADD FMT_S 0 0 14 1 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a880 : bv 32 := 0xd004f0d3.
Lemma F_1a880 : fetch_word Ubsan.M.loaded_segments (0x1a984 : word) = Some W_1a880.
Proof. vm_refl. Qed.
Lemma D_1a880 : decode_any W_1a880 = Some (Fcvt FC_S FC_W 1 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a884 : bv 32 := 0x00d0f043.
Lemma F_1a884 : fetch_word Ubsan.M.loaded_segments (0x1a988 : word) = Some W_1a884.
Proof. vm_refl. Qed.
Lemma D_1a884 : decode_any W_1a884 = Some (Fma F_MADD FMT_S 0 1 13 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a888 : bv 32 := 0x42000053.
Lemma F_1a888 : fetch_word Ubsan.M.loaded_segments (0x1a98c : word) = Some W_1a888.
Proof. vm_refl. Qed.
Lemma D_1a888 : decode_any W_1a888 = Some (Fcvt FC_D FC_S 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a88c : bv 32 := 0x02c07053.
Lemma F_1a88c : fetch_word Ubsan.M.loaded_segments (0x1a990 : word) = Some W_1a88c.
Proof. vm_refl. Qed.
Lemma D_1a88c : decode_any W_1a88c = Some (Fari F_ADD FMT_D 0 0 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a890 : bv 32 := 0xa2059fd3.
Lemma F_1a890 : fetch_word Ubsan.M.loaded_segments (0x1a994 : word) = Some W_1a890.
Proof. vm_refl. Qed.
Lemma D_1a890 : decode_any W_1a890 = Some (Fcmp F_LT FMT_D 31 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a894 : bv 32 := 0xa40f8ce3.
Lemma F_1a894 : fetch_word Ubsan.M.loaded_segments (0x1a998 : word) = Some W_1a894.
Proof. vm_refl. Qed.
Lemma D_1a894 : decode_any W_1a894 = Some (Branch BC_EQ 31 0 6744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a898 : bv 32 := 0xa2a01fd3.
Lemma F_1a898 : fetch_word Ubsan.M.loaded_segments (0x1a99c : word) = Some W_1a898.
Proof. vm_refl. Qed.
Lemma D_1a898 : decode_any W_1a898 = Some (Fcmp F_LT FMT_D 31 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a89c : bv 32 := 0xa40f88e3.
Lemma F_1a89c : fetch_word Ubsan.M.loaded_segments (0x1a9a0 : word) = Some W_1a89c.
Proof. vm_refl. Qed.
Lemma D_1a89c : decode_any W_1a89c = Some (Branch BC_EQ 31 0 6736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8b8 : bv 32 := 0xc2101453.
Lemma F_1a8b8 : fetch_word Ubsan.M.loaded_segments (0x1a9bc : word) = Some W_1a8b8.
Proof. vm_refl. Qed.
Lemma D_1a8b8 : decode_any W_1a8b8 = Some (Fcvt FC_WU FC_D 8 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8bc : bv 32 := 0x00458593.
Lemma F_1a8bc : fetch_word Ubsan.M.loaded_segments (0x1a9c0 : word) = Some W_1a8bc.
Proof. vm_refl. Qed.
Lemma D_1a8bc : decode_any W_1a8bc = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8c0 : bv 32 := 0x008fa023.
Lemma F_1a8c0 : fetch_word Ubsan.M.loaded_segments (0x1a9c4 : word) = Some W_1a8c0.
Proof. vm_refl. Qed.
Lemma D_1a8c0 : decode_any W_1a8c0 = Some (Store SZ4 31 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8c4 : bv 32 := 0xf4bf1ce3.
Lemma F_1a8c4 : fetch_word Ubsan.M.loaded_segments (0x1a9c8 : word) = Some W_1a8c4.
Proof. vm_refl. Qed.
Lemma D_1a8c4 : decode_any W_1a8c4 = Some (Branch BC_NE 30 11 8024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b438 : bv 32 := 0x00008067.
Lemma F_1b438 : fetch_word Ubsan.M.loaded_segments (0x1b53c : word) = Some W_1b438.
Proof. vm_refl. Qed.
Lemma D_1b438 : decode_any W_1b438 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

