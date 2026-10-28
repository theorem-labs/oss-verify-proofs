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
Definition W_12dd14 : bv 32 := 0xff010113.
Lemma F_12dd14 : fetch_word AsanUbsan.M.loaded_segments (0x130304 : word) = Some W_12dd14.
Proof. vm_refl. Qed.
Lemma D_12dd14 : decode_any W_12dd14 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12dd18 : bv 32 := 0x00113423.
Lemma F_12dd18 : fetch_word AsanUbsan.M.loaded_segments (0x130308 : word) = Some W_12dd18.
Proof. vm_refl. Qed.
Lemma D_12dd18 : decode_any W_12dd18 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12dd1c : bv 32 := 0x00060693.
Lemma F_12dd1c : fetch_word AsanUbsan.M.loaded_segments (0x13030c : word) = Some W_12dd1c.
Proof. vm_refl. Qed.
Lemma D_12dd1c : decode_any W_12dd1c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12dd20 : bv 32 := 0x00058613.
Lemma F_12dd20 : fetch_word AsanUbsan.M.loaded_segments (0x130310 : word) = Some W_12dd20.
Proof. vm_refl. Qed.
Lemma D_12dd20 : decode_any W_12dd20 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12dd24 : bv 32 := 0x00050593.
Lemma F_12dd24 : fetch_word AsanUbsan.M.loaded_segments (0x130314 : word) = Some W_12dd24.
Proof. vm_refl. Qed.
Lemma D_12dd24 : decode_any W_12dd24 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12dd28 : bv 32 := 0x03f00513.
Lemma F_12dd28 : fetch_word AsanUbsan.M.loaded_segments (0x130318 : word) = Some W_12dd28.
Proof. vm_refl. Qed.
Lemma D_12dd28 : decode_any W_12dd28 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12dd2c : bv 32 := 0x00000713.
Lemma F_12dd2c : fetch_word AsanUbsan.M.loaded_segments (0x13031c : word) = Some W_12dd2c.
Proof. vm_refl. Qed.
Lemma D_12dd2c : decode_any W_12dd2c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12dd30 : bv 32 := 0x00000793.
Lemma F_12dd30 : fetch_word AsanUbsan.M.loaded_segments (0x130320 : word) = Some W_12dd30.
Proof. vm_refl. Qed.
Lemma D_12dd30 : decode_any W_12dd30 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12dd34 : bv 32 := 0x00000813.
Lemma F_12dd34 : fetch_word AsanUbsan.M.loaded_segments (0x130324 : word) = Some W_12dd34.
Proof. vm_refl. Qed.
Lemma D_12dd34 : decode_any W_12dd34 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12dd38 : bv 32 := 0xdb8fa0ef.
Lemma F_12dd38 : fetch_word AsanUbsan.M.loaded_segments (0x130328 : word) = Some W_12dd38.
Proof. vm_refl. Qed.
Lemma D_12dd38 : decode_any W_12dd38 = Some (Jal 1 2074040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12dd3c : bv 32 := 0x00813083.
Lemma F_12dd3c : fetch_word AsanUbsan.M.loaded_segments (0x13032c : word) = Some W_12dd3c.
Proof. vm_refl. Qed.
Lemma D_12dd3c : decode_any W_12dd3c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12dd40 : bv 32 := 0x01010113.
Lemma F_12dd40 : fetch_word AsanUbsan.M.loaded_segments (0x130330 : word) = Some W_12dd40.
Proof. vm_refl. Qed.
Lemma D_12dd40 : decode_any W_12dd40 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12dd44 : bv 32 := 0x89de806f.
Lemma F_12dd44 : fetch_word AsanUbsan.M.loaded_segments (0x130334 : word) = Some W_12dd44.
Proof. vm_refl. Qed.
Lemma D_12dd44 : decode_any W_12dd44 = Some (Jal 0 2001052, 4%Z).
Proof. vm_refl. Qed.
