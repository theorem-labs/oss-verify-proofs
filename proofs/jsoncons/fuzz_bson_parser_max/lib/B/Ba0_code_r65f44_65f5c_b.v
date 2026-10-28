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
Definition W_7fdbc : bv 32 := 0x000c0517.
Lemma F_7fdbc : fetch_word AsanUbsan.M.loaded_segments (0x801d4 : word) = Some W_7fdbc.
Proof. vm_refl. Qed.
Lemma D_7fdbc : decode_any W_7fdbc = Some (Auipc 10 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fdc0 : bv 32 := 0x74450503.
Lemma F_7fdc0 : fetch_word AsanUbsan.M.loaded_segments (0x801d8 : word) = Some W_7fdc0.
Proof. vm_refl. Qed.
Lemma D_7fdc0 : decode_any W_7fdc0 = Some (Load SZ1 true 10 10 1860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fdc4 : bv 32 := 0x0230000f.
Lemma F_7fdc4 : fetch_word AsanUbsan.M.loaded_segments (0x801dc : word) = Some W_7fdc4.
Proof. vm_refl. Qed.
Lemma D_7fdc4 : decode_any W_7fdc4 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fdc8 : bv 32 := 0xfff50513.
Lemma F_7fdc8 : fetch_word AsanUbsan.M.loaded_segments (0x801e0 : word) = Some W_7fdc8.
Proof. vm_refl. Qed.
Lemma D_7fdc8 : decode_any W_7fdc8 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fdcc : bv 32 := 0x00153513.
Lemma F_7fdcc : fetch_word AsanUbsan.M.loaded_segments (0x801e4 : word) = Some W_7fdcc.
Proof. vm_refl. Qed.
Lemma D_7fdcc : decode_any W_7fdcc = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fdd0 : bv 32 := 0x00008067.
Lemma F_7fdd0 : fetch_word AsanUbsan.M.loaded_segments (0x801e8 : word) = Some W_7fdd0.
Proof. vm_refl. Qed.
Lemma D_7fdd0 : decode_any W_7fdd0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
