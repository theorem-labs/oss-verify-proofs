(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_83690 : bv 32 := 0x02850583.
Lemma F_83690 : fetch_word AsanUbsan.M.loaded_segments (0x83aa8 : word) = Some W_83690.
Proof. vm_refl. Qed.
Lemma D_83690 : decode_any W_83690 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83694 : bv 32 := 0x0230000f.
Lemma F_83694 : fetch_word AsanUbsan.M.loaded_segments (0x83aac : word) = Some W_83694.
Proof. vm_refl. Qed.
Lemma D_83694 : decode_any W_83694 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83698 : bv 32 := 0x02058c63.
Lemma F_83698 : fetch_word AsanUbsan.M.loaded_segments (0x83ab0 : word) = Some W_83698.
Proof. vm_refl. Qed.
Lemma D_83698 : decode_any W_83698 = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836d0 : bv 32 := 0x00853583.
Lemma F_836d0 : fetch_word AsanUbsan.M.loaded_segments (0x83ae8 : word) = Some W_836d0.
Proof. vm_refl. Qed.
Lemma D_836d0 : decode_any W_836d0 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836d4 : bv 32 := 0x01053503.
Lemma F_836d4 : fetch_word AsanUbsan.M.loaded_segments (0x83aec : word) = Some W_836d4.
Proof. vm_refl. Qed.
Lemma D_836d4 : decode_any W_836d4 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836d8 : bv 32 := 0x00b53533.
Lemma F_836d8 : fetch_word AsanUbsan.M.loaded_segments (0x83af0 : word) = Some W_836d8.
Proof. vm_refl. Qed.
Lemma D_836d8 : decode_any W_836d8 = Some (Op ALU_SLTU 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836dc : bv 32 := 0x40a00533.
Lemma F_836dc : fetch_word AsanUbsan.M.loaded_segments (0x83af4 : word) = Some W_836dc.
Proof. vm_refl. Qed.
Lemma D_836dc : decode_any W_836dc = Some (Op ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836e0 : bv 32 := 0x00b57533.
Lemma F_836e0 : fetch_word AsanUbsan.M.loaded_segments (0x83af8 : word) = Some W_836e0.
Proof. vm_refl. Qed.
Lemma D_836e0 : decode_any W_836e0 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836e4 : bv 32 := 0x00008067.
Lemma F_836e4 : fetch_word AsanUbsan.M.loaded_segments (0x83afc : word) = Some W_836e4.
Proof. vm_refl. Qed.
Lemma D_836e4 : decode_any W_836e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836e8 : bv 32 := 0x02850583.
Lemma F_836e8 : fetch_word AsanUbsan.M.loaded_segments (0x83b00 : word) = Some W_836e8.
Proof. vm_refl. Qed.
Lemma D_836e8 : decode_any W_836e8 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836ec : bv 32 := 0x0230000f.
Lemma F_836ec : fetch_word AsanUbsan.M.loaded_segments (0x83b04 : word) = Some W_836ec.
Proof. vm_refl. Qed.
Lemma D_836ec : decode_any W_836ec = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836f0 : bv 32 := 0x02058c63.
Lemma F_836f0 : fetch_word AsanUbsan.M.loaded_segments (0x83b08 : word) = Some W_836f0.
Proof. vm_refl. Qed.
Lemma D_836f0 : decode_any W_836f0 = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83728 : bv 32 := 0x00853583.
Lemma F_83728 : fetch_word AsanUbsan.M.loaded_segments (0x83b40 : word) = Some W_83728.
Proof. vm_refl. Qed.
Lemma D_83728 : decode_any W_83728 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8372c : bv 32 := 0x01053503.
Lemma F_8372c : fetch_word AsanUbsan.M.loaded_segments (0x83b44 : word) = Some W_8372c.
Proof. vm_refl. Qed.
Lemma D_8372c : decode_any W_8372c = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83730 : bv 32 := 0x00b535b3.
Lemma F_83730 : fetch_word AsanUbsan.M.loaded_segments (0x83b48 : word) = Some W_83730.
Proof. vm_refl. Qed.
Lemma D_83730 : decode_any W_83730 = Some (Op ALU_SLTU 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83734 : bv 32 := 0x40b005b3.
Lemma F_83734 : fetch_word AsanUbsan.M.loaded_segments (0x83b4c : word) = Some W_83734.
Proof. vm_refl. Qed.
Lemma D_83734 : decode_any W_83734 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83738 : bv 32 := 0x00a5f533.
Lemma F_83738 : fetch_word AsanUbsan.M.loaded_segments (0x83b50 : word) = Some W_83738.
Proof. vm_refl. Qed.
Lemma D_83738 : decode_any W_83738 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8373c : bv 32 := 0x00008067.
Lemma F_8373c : fetch_word AsanUbsan.M.loaded_segments (0x83b54 : word) = Some W_8373c.
Proof. vm_refl. Qed.
Lemma D_8373c : decode_any W_8373c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
