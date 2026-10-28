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
Definition W_8dc10 : bv 32 := 0xef010113.
Lemma F_8dc10 : fetch_word AsanUbsan.M.loaded_segments (0x8e028 : word) = Some W_8dc10.
Proof. vm_refl. Qed.
Lemma D_8dc10 : decode_any W_8dc10 = Some (OpImm ALU_ADD 2 2 3824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc14 : bv 32 := 0x10113423.
Lemma F_8dc14 : fetch_word AsanUbsan.M.loaded_segments (0x8e02c : word) = Some W_8dc14.
Proof. vm_refl. Qed.
Lemma D_8dc14 : decode_any W_8dc14 = Some (Store SZ8 2 1 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc18 : bv 32 := 0x10813023.
Lemma F_8dc18 : fetch_word AsanUbsan.M.loaded_segments (0x8e030 : word) = Some W_8dc18.
Proof. vm_refl. Qed.
Lemma D_8dc18 : decode_any W_8dc18 = Some (Store SZ8 2 8 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc1c : bv 32 := 0x0e913c23.
Lemma F_8dc1c : fetch_word AsanUbsan.M.loaded_segments (0x8e034 : word) = Some W_8dc1c.
Proof. vm_refl. Qed.
Lemma D_8dc1c : decode_any W_8dc1c = Some (Store SZ8 2 9 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc20 : bv 32 := 0x0f213823.
Lemma F_8dc20 : fetch_word AsanUbsan.M.loaded_segments (0x8e038 : word) = Some W_8dc20.
Proof. vm_refl. Qed.
Lemma D_8dc20 : decode_any W_8dc20 = Some (Store SZ8 2 18 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc24 : bv 32 := 0x0f313423.
Lemma F_8dc24 : fetch_word AsanUbsan.M.loaded_segments (0x8e03c : word) = Some W_8dc24.
Proof. vm_refl. Qed.
Lemma D_8dc24 : decode_any W_8dc24 = Some (Store SZ8 2 19 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc28 : bv 32 := 0x0f413023.
Lemma F_8dc28 : fetch_word AsanUbsan.M.loaded_segments (0x8e040 : word) = Some W_8dc28.
Proof. vm_refl. Qed.
Lemma D_8dc28 : decode_any W_8dc28 = Some (Store SZ8 2 20 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc2c : bv 32 := 0x0d513c23.
Lemma F_8dc2c : fetch_word AsanUbsan.M.loaded_segments (0x8e044 : word) = Some W_8dc2c.
Proof. vm_refl. Qed.
Lemma D_8dc2c : decode_any W_8dc2c = Some (Store SZ8 2 21 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc30 : bv 32 := 0x00050913.
Lemma F_8dc30 : fetch_word AsanUbsan.M.loaded_segments (0x8e048 : word) = Some W_8dc30.
Proof. vm_refl. Qed.
Lemma D_8dc30 : decode_any W_8dc30 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc34 : bv 32 := 0xfff00513.
Lemma F_8dc34 : fetch_word AsanUbsan.M.loaded_segments (0x8e04c : word) = Some W_8dc34.
Proof. vm_refl. Qed.
Lemma D_8dc34 : decode_any W_8dc34 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc38 : bv 32 := 0x12090463.
Lemma F_8dc38 : fetch_word AsanUbsan.M.loaded_segments (0x8e050 : word) = Some W_8dc38.
Proof. vm_refl. Qed.
Lemma D_8dc38 : decode_any W_8dc38 = Some (Branch BC_EQ 18 0 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc3c : bv 32 := 0x00060413.
Lemma F_8dc3c : fetch_word AsanUbsan.M.loaded_segments (0x8e054 : word) = Some W_8dc3c.
Proof. vm_refl. Qed.
Lemma D_8dc3c : decode_any W_8dc3c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc40 : bv 32 := 0x000a9617.
Lemma F_8dc40 : fetch_word AsanUbsan.M.loaded_segments (0x8e058 : word) = Some W_8dc40.
Proof. vm_refl. Qed.
Lemma D_8dc40 : decode_any W_8dc40 = Some (Auipc 12 169, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc44 : bv 32 := 0x45863603.
Lemma F_8dc44 : fetch_word AsanUbsan.M.loaded_segments (0x8e05c : word) = Some W_8dc44.
Proof. vm_refl. Qed.
Lemma D_8dc44 : decode_any W_8dc44 = Some (Load SZ8 true 12 12 1112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc48 : bv 32 := 0x10464603.
Lemma F_8dc48 : fetch_word AsanUbsan.M.loaded_segments (0x8e060 : word) = Some W_8dc48.
Proof. vm_refl. Qed.
Lemma D_8dc48 : decode_any W_8dc48 = Some (Load SZ1 false 12 12 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc4c : bv 32 := 0x00167613.
Lemma F_8dc4c : fetch_word AsanUbsan.M.loaded_segments (0x8e064 : word) = Some W_8dc4c.
Proof. vm_refl. Qed.
Lemma D_8dc4c : decode_any W_8dc4c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc50 : bv 32 := 0x10060863.
Lemma F_8dc50 : fetch_word AsanUbsan.M.loaded_segments (0x8e068 : word) = Some W_8dc50.
Proof. vm_refl. Qed.
Lemma D_8dc50 : decode_any W_8dc50 = Some (Branch BC_EQ 12 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dd60 : bv 32 := 0x0005051b.
Lemma F_8dd60 : fetch_word AsanUbsan.M.loaded_segments (0x8e178 : word) = Some W_8dd60.
Proof. vm_refl. Qed.
Lemma D_8dd60 : decode_any W_8dd60 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dd64 : bv 32 := 0x10813083.
Lemma F_8dd64 : fetch_word AsanUbsan.M.loaded_segments (0x8e17c : word) = Some W_8dd64.
Proof. vm_refl. Qed.
Lemma D_8dd64 : decode_any W_8dd64 = Some (Load SZ8 true 1 2 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dd68 : bv 32 := 0x10013403.
Lemma F_8dd68 : fetch_word AsanUbsan.M.loaded_segments (0x8e180 : word) = Some W_8dd68.
Proof. vm_refl. Qed.
Lemma D_8dd68 : decode_any W_8dd68 = Some (Load SZ8 true 8 2 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dd6c : bv 32 := 0x0f813483.
Lemma F_8dd6c : fetch_word AsanUbsan.M.loaded_segments (0x8e184 : word) = Some W_8dd6c.
Proof. vm_refl. Qed.
Lemma D_8dd6c : decode_any W_8dd6c = Some (Load SZ8 true 9 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dd70 : bv 32 := 0x0f013903.
Lemma F_8dd70 : fetch_word AsanUbsan.M.loaded_segments (0x8e188 : word) = Some W_8dd70.
Proof. vm_refl. Qed.
Lemma D_8dd70 : decode_any W_8dd70 = Some (Load SZ8 true 18 2 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dd74 : bv 32 := 0x0e813983.
Lemma F_8dd74 : fetch_word AsanUbsan.M.loaded_segments (0x8e18c : word) = Some W_8dd74.
Proof. vm_refl. Qed.
Lemma D_8dd74 : decode_any W_8dd74 = Some (Load SZ8 true 19 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dd78 : bv 32 := 0x0e013a03.
Lemma F_8dd78 : fetch_word AsanUbsan.M.loaded_segments (0x8e190 : word) = Some W_8dd78.
Proof. vm_refl. Qed.
Lemma D_8dd78 : decode_any W_8dd78 = Some (Load SZ8 true 20 2 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dd7c : bv 32 := 0x0d813a83.
Lemma F_8dd7c : fetch_word AsanUbsan.M.loaded_segments (0x8e194 : word) = Some W_8dd7c.
Proof. vm_refl. Qed.
Lemma D_8dd7c : decode_any W_8dd7c = Some (Load SZ8 true 21 2 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dd80 : bv 32 := 0x11010113.
Lemma F_8dd80 : fetch_word AsanUbsan.M.loaded_segments (0x8e198 : word) = Some W_8dd80.
Proof. vm_refl. Qed.
Lemma D_8dd80 : decode_any W_8dd80 = Some (OpImm ALU_ADD 2 2 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dd84 : bv 32 := 0x00008067.
Lemma F_8dd84 : fetch_word AsanUbsan.M.loaded_segments (0x8e19c : word) = Some W_8dd84.
Proof. vm_refl. Qed.
Lemma D_8dd84 : decode_any W_8dd84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
