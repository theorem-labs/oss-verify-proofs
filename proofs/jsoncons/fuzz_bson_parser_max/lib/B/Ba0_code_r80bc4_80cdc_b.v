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
Definition W_9ab94 : bv 32 := 0xfc010113.
Lemma F_9ab94 : fetch_word AsanUbsan.M.loaded_segments (0x9afac : word) = Some W_9ab94.
Proof. vm_refl. Qed.
Lemma D_9ab94 : decode_any W_9ab94 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab98 : bv 32 := 0x02113c23.
Lemma F_9ab98 : fetch_word AsanUbsan.M.loaded_segments (0x9afb0 : word) = Some W_9ab98.
Proof. vm_refl. Qed.
Lemma D_9ab98 : decode_any W_9ab98 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab9c : bv 32 := 0x02813823.
Lemma F_9ab9c : fetch_word AsanUbsan.M.loaded_segments (0x9afb4 : word) = Some W_9ab9c.
Proof. vm_refl. Qed.
Lemma D_9ab9c : decode_any W_9ab9c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aba0 : bv 32 := 0x02913423.
Lemma F_9aba0 : fetch_word AsanUbsan.M.loaded_segments (0x9afb8 : word) = Some W_9aba0.
Proof. vm_refl. Qed.
Lemma D_9aba0 : decode_any W_9aba0 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aba4 : bv 32 := 0x03213023.
Lemma F_9aba4 : fetch_word AsanUbsan.M.loaded_segments (0x9afbc : word) = Some W_9aba4.
Proof. vm_refl. Qed.
Lemma D_9aba4 : decode_any W_9aba4 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aba8 : bv 32 := 0x01313c23.
Lemma F_9aba8 : fetch_word AsanUbsan.M.loaded_segments (0x9afc0 : word) = Some W_9aba8.
Proof. vm_refl. Qed.
Lemma D_9aba8 : decode_any W_9aba8 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abac : bv 32 := 0x01413823.
Lemma F_9abac : fetch_word AsanUbsan.M.loaded_segments (0x9afc4 : word) = Some W_9abac.
Proof. vm_refl. Qed.
Lemma D_9abac : decode_any W_9abac = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abb0 : bv 32 := 0x01513423.
Lemma F_9abb0 : fetch_word AsanUbsan.M.loaded_segments (0x9afc8 : word) = Some W_9abb0.
Proof. vm_refl. Qed.
Lemma D_9abb0 : decode_any W_9abb0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abb4 : bv 32 := 0x00058413.
Lemma F_9abb4 : fetch_word AsanUbsan.M.loaded_segments (0x9afcc : word) = Some W_9abb4.
Proof. vm_refl. Qed.
Lemma D_9abb4 : decode_any W_9abb4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abb8 : bv 32 := 0x0015b593.
Lemma F_9abb8 : fetch_word AsanUbsan.M.loaded_segments (0x9afd0 : word) = Some W_9abb8.
Proof. vm_refl. Qed.
Lemma D_9abb8 : decode_any W_9abb8 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abbc : bv 32 := 0x7ff50293.
Lemma F_9abbc : fetch_word AsanUbsan.M.loaded_segments (0x9afd4 : word) = Some W_9abbc.
Proof. vm_refl. Qed.
Lemma D_9abbc : decode_any W_9abbc = Some (OpImm ALU_ADD 5 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abc0 : bv 32 := 0xfff58593.
Lemma F_9abc0 : fetch_word AsanUbsan.M.loaded_segments (0x9afd8 : word) = Some W_9abc0.
Proof. vm_refl. Qed.
Lemma D_9abc0 : decode_any W_9abc0 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abc4 : bv 32 := 0x00d5f333.
Lemma F_9abc4 : fetch_word AsanUbsan.M.loaded_segments (0x9afdc : word) = Some W_9abc4.
Proof. vm_refl. Qed.
Lemma D_9abc4 : decode_any W_9abc4 = Some (Op ALU_AND 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abc8 : bv 32 := 0x00100593.
Lemma F_9abc8 : fetch_word AsanUbsan.M.loaded_segments (0x9afe0 : word) = Some W_9abc8.
Proof. vm_refl. Qed.
Lemma D_9abc8 : decode_any W_9abc8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abcc : bv 32 := 0x0062b4a3.
Lemma F_9abcc : fetch_word AsanUbsan.M.loaded_segments (0x9afe4 : word) = Some W_9abcc.
Proof. vm_refl. Qed.
Lemma D_9abcc : decode_any W_9abcc = Some (Store SZ8 5 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abd0 : bv 32 := 0x00b40863.
Lemma F_9abd0 : fetch_word AsanUbsan.M.loaded_segments (0x9afe8 : word) = Some W_9abd0.
Proof. vm_refl. Qed.
Lemma D_9abd0 : decode_any W_9abd0 = Some (Branch BC_EQ 8 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abd4 : bv 32 := 0x02041c63.
Lemma F_9abd4 : fetch_word AsanUbsan.M.loaded_segments (0x9afec : word) = Some W_9abd4.
Proof. vm_refl. Qed.
Lemma D_9abd4 : decode_any W_9abd4 = Some (Branch BC_NE 8 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac0c : bv 32 := 0x06089463.
Lemma F_9ac0c : fetch_word AsanUbsan.M.loaded_segments (0x9b024 : word) = Some W_9ac0c.
Proof. vm_refl. Qed.
Lemma D_9ac0c : decode_any W_9ac0c = Some (Branch BC_NE 17 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac74 : bv 32 := 0x00060593.
Lemma F_9ac74 : fetch_word AsanUbsan.M.loaded_segments (0x9b08c : word) = Some W_9ac74.
Proof. vm_refl. Qed.
Lemma D_9ac74 : decode_any W_9ac74 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac78 : bv 32 := 0x00068613.
Lemma F_9ac78 : fetch_word AsanUbsan.M.loaded_segments (0x9b090 : word) = Some W_9ac78.
Proof. vm_refl. Qed.
Lemma D_9ac78 : decode_any W_9ac78 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac7c : bv 32 := 0x00078693.
Lemma F_9ac7c : fetch_word AsanUbsan.M.loaded_segments (0x9b094 : word) = Some W_9ac7c.
Proof. vm_refl. Qed.
Lemma D_9ac7c : decode_any W_9ac7c = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac80 : bv 32 := 0x00080713.
Lemma F_9ac80 : fetch_word AsanUbsan.M.loaded_segments (0x9b098 : word) = Some W_9ac80.
Proof. vm_refl. Qed.
Lemma D_9ac80 : decode_any W_9ac80 = Some (OpImm ALU_ADD 14 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac84 : bv 32 := 0x00040793.
Lemma F_9ac84 : fetch_word AsanUbsan.M.loaded_segments (0x9b09c : word) = Some W_9ac84.
Proof. vm_refl. Qed.
Lemma D_9ac84 : decode_any W_9ac84 = Some (OpImm ALU_ADD 15 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac88 : bv 32 := 0x03813083.
Lemma F_9ac88 : fetch_word AsanUbsan.M.loaded_segments (0x9b0a0 : word) = Some W_9ac88.
Proof. vm_refl. Qed.
Lemma D_9ac88 : decode_any W_9ac88 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac8c : bv 32 := 0x03013403.
Lemma F_9ac8c : fetch_word AsanUbsan.M.loaded_segments (0x9b0a4 : word) = Some W_9ac8c.
Proof. vm_refl. Qed.
Lemma D_9ac8c : decode_any W_9ac8c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac90 : bv 32 := 0x02813483.
Lemma F_9ac90 : fetch_word AsanUbsan.M.loaded_segments (0x9b0a8 : word) = Some W_9ac90.
Proof. vm_refl. Qed.
Lemma D_9ac90 : decode_any W_9ac90 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac94 : bv 32 := 0x02013903.
Lemma F_9ac94 : fetch_word AsanUbsan.M.loaded_segments (0x9b0ac : word) = Some W_9ac94.
Proof. vm_refl. Qed.
Lemma D_9ac94 : decode_any W_9ac94 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac98 : bv 32 := 0x01813983.
Lemma F_9ac98 : fetch_word AsanUbsan.M.loaded_segments (0x9b0b0 : word) = Some W_9ac98.
Proof. vm_refl. Qed.
Lemma D_9ac98 : decode_any W_9ac98 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac9c : bv 32 := 0x01013a03.
Lemma F_9ac9c : fetch_word AsanUbsan.M.loaded_segments (0x9b0b4 : word) = Some W_9ac9c.
Proof. vm_refl. Qed.
Lemma D_9ac9c : decode_any W_9ac9c = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aca0 : bv 32 := 0x00813a83.
Lemma F_9aca0 : fetch_word AsanUbsan.M.loaded_segments (0x9b0b8 : word) = Some W_9aca0.
Proof. vm_refl. Qed.
Lemma D_9aca0 : decode_any W_9aca0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aca4 : bv 32 := 0x04010113.
Lemma F_9aca4 : fetch_word AsanUbsan.M.loaded_segments (0x9b0bc : word) = Some W_9aca4.
Proof. vm_refl. Qed.
Lemma D_9aca4 : decode_any W_9aca4 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aca8 : bv 32 := 0x891ff06f.
Lemma F_9aca8 : fetch_word AsanUbsan.M.loaded_segments (0x9b0c0 : word) = Some W_9aca8.
Proof. vm_refl. Qed.
Lemma D_9aca8 : decode_any W_9aca8 = Some (Jal 0 2095248, 4%Z).
Proof. vm_refl. Qed.
