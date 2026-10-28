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
Definition W_834cc : bv 32 := 0xff010113.
Lemma F_834cc : fetch_word AsanUbsan.M.loaded_segments (0x838e4 : word) = Some W_834cc.
Proof. vm_refl. Qed.
Lemma D_834cc : decode_any W_834cc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_834d0 : bv 32 := 0x00113423.
Lemma F_834d0 : fetch_word AsanUbsan.M.loaded_segments (0x838e8 : word) = Some W_834d0.
Proof. vm_refl. Qed.
Lemma D_834d0 : decode_any W_834d0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_834d4 : bv 32 := 0xe78f80ef.
Lemma F_834d4 : fetch_word AsanUbsan.M.loaded_segments (0x838ec : word) = Some W_834d4.
Proof. vm_refl. Qed.
Lemma D_834d4 : decode_any W_834d4 = Some (Jal 1 2066040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_834d8 : bv 32 := 0x00050463.
Lemma F_834d8 : fetch_word AsanUbsan.M.loaded_segments (0x838f0 : word) = Some W_834d8.
Proof. vm_refl. Qed.
Lemma D_834d8 : decode_any W_834d8 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_834dc : bv 32 := 0x09853503.
Lemma F_834dc : fetch_word AsanUbsan.M.loaded_segments (0x838f4 : word) = Some W_834dc.
Proof. vm_refl. Qed.
Lemma D_834dc : decode_any W_834dc = Some (Load SZ8 true 10 10 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_834e0 : bv 32 := 0x00813083.
Lemma F_834e0 : fetch_word AsanUbsan.M.loaded_segments (0x838f8 : word) = Some W_834e0.
Proof. vm_refl. Qed.
Lemma D_834e0 : decode_any W_834e0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_834e4 : bv 32 := 0x01010113.
Lemma F_834e4 : fetch_word AsanUbsan.M.loaded_segments (0x838fc : word) = Some W_834e4.
Proof. vm_refl. Qed.
Lemma D_834e4 : decode_any W_834e4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_834e8 : bv 32 := 0x00008067.
Lemma F_834e8 : fetch_word AsanUbsan.M.loaded_segments (0x83900 : word) = Some W_834e8.
Proof. vm_refl. Qed.
Lemma D_834e8 : decode_any W_834e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
