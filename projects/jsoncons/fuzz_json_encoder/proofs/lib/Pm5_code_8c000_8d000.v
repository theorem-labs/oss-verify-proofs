(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8c718 : bv 32 := 0xff010113.
Lemma F_8c718 : fetch_word AsanUbsan.M.loaded_segments (0x8c760 : word) = Some W_8c718.
Proof. vm_refl. Qed.
Lemma D_8c718 : decode_any W_8c718 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c71c : bv 32 := 0x00113423.
Lemma F_8c71c : fetch_word AsanUbsan.M.loaded_segments (0x8c764 : word) = Some W_8c71c.
Proof. vm_refl. Qed.
Lemma D_8c71c : decode_any W_8c71c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c720 : bv 32 := 0xe78f80ef.
Lemma F_8c720 : fetch_word AsanUbsan.M.loaded_segments (0x8c768 : word) = Some W_8c720.
Proof. vm_refl. Qed.
Lemma D_8c720 : decode_any W_8c720 = Some (Jal 1 2066040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c724 : bv 32 := 0x00050463.
Lemma F_8c724 : fetch_word AsanUbsan.M.loaded_segments (0x8c76c : word) = Some W_8c724.
Proof. vm_refl. Qed.
Lemma D_8c724 : decode_any W_8c724 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c728 : bv 32 := 0x09853503.
Lemma F_8c728 : fetch_word AsanUbsan.M.loaded_segments (0x8c770 : word) = Some W_8c728.
Proof. vm_refl. Qed.
Lemma D_8c728 : decode_any W_8c728 = Some (Load SZ8 true 10 10 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c72c : bv 32 := 0x00813083.
Lemma F_8c72c : fetch_word AsanUbsan.M.loaded_segments (0x8c774 : word) = Some W_8c72c.
Proof. vm_refl. Qed.
Lemma D_8c72c : decode_any W_8c72c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c730 : bv 32 := 0x01010113.
Lemma F_8c730 : fetch_word AsanUbsan.M.loaded_segments (0x8c778 : word) = Some W_8c730.
Proof. vm_refl. Qed.
Lemma D_8c730 : decode_any W_8c730 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c734 : bv 32 := 0x00008067.
Lemma F_8c734 : fetch_word AsanUbsan.M.loaded_segments (0x8c77c : word) = Some W_8c734.
Proof. vm_refl. Qed.
Lemma D_8c734 : decode_any W_8c734 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c8dc : bv 32 := 0x02850583.
Lemma F_8c8dc : fetch_word AsanUbsan.M.loaded_segments (0x8c924 : word) = Some W_8c8dc.
Proof. vm_refl. Qed.
Lemma D_8c8dc : decode_any W_8c8dc = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c8e0 : bv 32 := 0x0230000f.
Lemma F_8c8e0 : fetch_word AsanUbsan.M.loaded_segments (0x8c928 : word) = Some W_8c8e0.
Proof. vm_refl. Qed.
Lemma D_8c8e0 : decode_any W_8c8e0 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c8e4 : bv 32 := 0x02058c63.
Lemma F_8c8e4 : fetch_word AsanUbsan.M.loaded_segments (0x8c92c : word) = Some W_8c8e4.
Proof. vm_refl. Qed.
Lemma D_8c8e4 : decode_any W_8c8e4 = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c91c : bv 32 := 0x00853583.
Lemma F_8c91c : fetch_word AsanUbsan.M.loaded_segments (0x8c964 : word) = Some W_8c91c.
Proof. vm_refl. Qed.
Lemma D_8c91c : decode_any W_8c91c = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c920 : bv 32 := 0x01053503.
Lemma F_8c920 : fetch_word AsanUbsan.M.loaded_segments (0x8c968 : word) = Some W_8c920.
Proof. vm_refl. Qed.
Lemma D_8c920 : decode_any W_8c920 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c924 : bv 32 := 0x00b53533.
Lemma F_8c924 : fetch_word AsanUbsan.M.loaded_segments (0x8c96c : word) = Some W_8c924.
Proof. vm_refl. Qed.
Lemma D_8c924 : decode_any W_8c924 = Some (Op ALU_SLTU 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c928 : bv 32 := 0x40a00533.
Lemma F_8c928 : fetch_word AsanUbsan.M.loaded_segments (0x8c970 : word) = Some W_8c928.
Proof. vm_refl. Qed.
Lemma D_8c928 : decode_any W_8c928 = Some (Op ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c92c : bv 32 := 0x00b57533.
Lemma F_8c92c : fetch_word AsanUbsan.M.loaded_segments (0x8c974 : word) = Some W_8c92c.
Proof. vm_refl. Qed.
Lemma D_8c92c : decode_any W_8c92c = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c930 : bv 32 := 0x00008067.
Lemma F_8c930 : fetch_word AsanUbsan.M.loaded_segments (0x8c978 : word) = Some W_8c930.
Proof. vm_refl. Qed.
Lemma D_8c930 : decode_any W_8c930 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c934 : bv 32 := 0x02850583.
Lemma F_8c934 : fetch_word AsanUbsan.M.loaded_segments (0x8c97c : word) = Some W_8c934.
Proof. vm_refl. Qed.
Lemma D_8c934 : decode_any W_8c934 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c938 : bv 32 := 0x0230000f.
Lemma F_8c938 : fetch_word AsanUbsan.M.loaded_segments (0x8c980 : word) = Some W_8c938.
Proof. vm_refl. Qed.
Lemma D_8c938 : decode_any W_8c938 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c93c : bv 32 := 0x02058c63.
Lemma F_8c93c : fetch_word AsanUbsan.M.loaded_segments (0x8c984 : word) = Some W_8c93c.
Proof. vm_refl. Qed.
Lemma D_8c93c : decode_any W_8c93c = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c974 : bv 32 := 0x00853583.
Lemma F_8c974 : fetch_word AsanUbsan.M.loaded_segments (0x8c9bc : word) = Some W_8c974.
Proof. vm_refl. Qed.
Lemma D_8c974 : decode_any W_8c974 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c978 : bv 32 := 0x01053503.
Lemma F_8c978 : fetch_word AsanUbsan.M.loaded_segments (0x8c9c0 : word) = Some W_8c978.
Proof. vm_refl. Qed.
Lemma D_8c978 : decode_any W_8c978 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c97c : bv 32 := 0x00b535b3.
Lemma F_8c97c : fetch_word AsanUbsan.M.loaded_segments (0x8c9c4 : word) = Some W_8c97c.
Proof. vm_refl. Qed.
Lemma D_8c97c : decode_any W_8c97c = Some (Op ALU_SLTU 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c980 : bv 32 := 0x40b005b3.
Lemma F_8c980 : fetch_word AsanUbsan.M.loaded_segments (0x8c9c8 : word) = Some W_8c980.
Proof. vm_refl. Qed.
Lemma D_8c980 : decode_any W_8c980 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c984 : bv 32 := 0x00a5f533.
Lemma F_8c984 : fetch_word AsanUbsan.M.loaded_segments (0x8c9cc : word) = Some W_8c984.
Proof. vm_refl. Qed.
Lemma D_8c984 : decode_any W_8c984 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c988 : bv 32 := 0x00008067.
Lemma F_8c988 : fetch_word AsanUbsan.M.loaded_segments (0x8c9d0 : word) = Some W_8c988.
Proof. vm_refl. Qed.
Lemma D_8c988 : decode_any W_8c988 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

