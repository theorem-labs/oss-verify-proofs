(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_7cbe0 : bv 32 := 0x00050213.
Lemma F_7cbe0 : fetch_word Ubsan.M.loaded_segments (0x7cbe0 : word) = Some W_7cbe0.
Proof. vm_refl. Qed.
Lemma D_7cbe0 : decode_any W_7cbe0 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbe4 : bv 32 := 0x00000513.
Lemma F_7cbe4 : fetch_word Ubsan.M.loaded_segments (0x7cbe4 : word) = Some W_7cbe4.
Proof. vm_refl. Qed.
Lemma D_7cbe4 : decode_any W_7cbe4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbe8 : bv 32 := 0x00008067.
Lemma F_7cbe8 : fetch_word Ubsan.M.loaded_segments (0x7cbe8 : word) = Some W_7cbe8.
Proof. vm_refl. Qed.
Lemma D_7cbe8 : decode_any W_7cbe8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbec : bv 32 := 0x0d700893.
Lemma F_7cbec : fetch_word Ubsan.M.loaded_segments (0x7cbec : word) = Some W_7cbec.
Proof. vm_refl. Qed.
Lemma D_7cbec : decode_any W_7cbec = Some (OpImm ALU_ADD 17 0 215, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbf0 : bv 32 := 0x00000073.
Lemma F_7cbf0 : fetch_word Ubsan.M.loaded_segments (0x7cbf0 : word) = Some W_7cbf0.
Proof. vm_refl. Qed.
Lemma D_7cbf0 : decode_any W_7cbf0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_7cbf0 : is_ecall W_7cbf0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_7cbf4 : bv 32 := 0x05d00893.
Lemma F_7cbf4 : fetch_word Ubsan.M.loaded_segments (0x7cbf4 : word) = Some W_7cbf4.
Proof. vm_refl. Qed.
Lemma D_7cbf4 : decode_any W_7cbf4 = Some (OpImm ALU_ADD 17 0 93, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbf8 : bv 32 := 0x00000073.
Lemma F_7cbf8 : fetch_word Ubsan.M.loaded_segments (0x7cbf8 : word) = Some W_7cbf8.
Proof. vm_refl. Qed.
Lemma D_7cbf8 : decode_any W_7cbf8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_7cbf8 : is_ecall W_7cbf8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_7cbfc : bv 32 := 0xff05f593.
Lemma F_7cbfc : fetch_word Ubsan.M.loaded_segments (0x7cbfc : word) = Some W_7cbfc.
Proof. vm_refl. Qed.
Lemma D_7cbfc : decode_any W_7cbfc = Some (OpImm ALU_AND 11 11 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc00 : bv 32 := 0xff058593.
Lemma F_7cc00 : fetch_word Ubsan.M.loaded_segments (0x7cc00 : word) = Some W_7cc00.
Proof. vm_refl. Qed.
Lemma D_7cc00 : decode_any W_7cc00 = Some (OpImm ALU_ADD 11 11 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc04 : bv 32 := 0x00a5b023.
Lemma F_7cc04 : fetch_word Ubsan.M.loaded_segments (0x7cc04 : word) = Some W_7cc04.
Proof. vm_refl. Qed.
Lemma D_7cc04 : decode_any W_7cc04 = Some (Store SZ8 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc08 : bv 32 := 0x00d5b423.
Lemma F_7cc08 : fetch_word Ubsan.M.loaded_segments (0x7cc08 : word) = Some W_7cc08.
Proof. vm_refl. Qed.
Lemma D_7cc08 : decode_any W_7cc08 = Some (Store SZ8 11 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc0c : bv 32 := 0x00060513.
Lemma F_7cc0c : fetch_word Ubsan.M.loaded_segments (0x7cc0c : word) = Some W_7cc0c.
Proof. vm_refl. Qed.
Lemma D_7cc0c : decode_any W_7cc0c = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc10 : bv 32 := 0x00070613.
Lemma F_7cc10 : fetch_word Ubsan.M.loaded_segments (0x7cc10 : word) = Some W_7cc10.
Proof. vm_refl. Qed.
Lemma D_7cc10 : decode_any W_7cc10 = Some (OpImm ALU_ADD 12 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc14 : bv 32 := 0x00078693.
Lemma F_7cc14 : fetch_word Ubsan.M.loaded_segments (0x7cc14 : word) = Some W_7cc14.
Proof. vm_refl. Qed.
Lemma D_7cc14 : decode_any W_7cc14 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc18 : bv 32 := 0x00080713.
Lemma F_7cc18 : fetch_word Ubsan.M.loaded_segments (0x7cc18 : word) = Some W_7cc18.
Proof. vm_refl. Qed.
Lemma D_7cc18 : decode_any W_7cc18 = Some (OpImm ALU_ADD 14 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc1c : bv 32 := 0x0dc00893.
Lemma F_7cc1c : fetch_word Ubsan.M.loaded_segments (0x7cc1c : word) = Some W_7cc1c.
Proof. vm_refl. Qed.
Lemma D_7cc1c : decode_any W_7cc1c = Some (OpImm ALU_ADD 17 0 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc20 : bv 32 := 0x00000073.
Lemma F_7cc20 : fetch_word Ubsan.M.loaded_segments (0x7cc20 : word) = Some W_7cc20.
Proof. vm_refl. Qed.
Lemma D_7cc20 : decode_any W_7cc20 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_7cc20 : is_ecall W_7cc20 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_7cc24 : bv 32 := 0x00050463.
Lemma F_7cc24 : fetch_word Ubsan.M.loaded_segments (0x7cc24 : word) = Some W_7cc24.
Proof. vm_refl. Qed.
Lemma D_7cc24 : decode_any W_7cc24 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc28 : bv 32 := 0x00008067.
Lemma F_7cc28 : fetch_word Ubsan.M.loaded_segments (0x7cc28 : word) = Some W_7cc28.
Proof. vm_refl. Qed.
Lemma D_7cc28 : decode_any W_7cc28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc2c : bv 32 := 0x00013583.
Lemma F_7cc2c : fetch_word Ubsan.M.loaded_segments (0x7cc2c : word) = Some W_7cc2c.
Proof. vm_refl. Qed.
Lemma D_7cc2c : decode_any W_7cc2c = Some (Load SZ8 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc30 : bv 32 := 0x00813503.
Lemma F_7cc30 : fetch_word Ubsan.M.loaded_segments (0x7cc30 : word) = Some W_7cc30.
Proof. vm_refl. Qed.
Lemma D_7cc30 : decode_any W_7cc30 = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc34 : bv 32 := 0x000580e7.
Lemma F_7cc34 : fetch_word Ubsan.M.loaded_segments (0x7cc34 : word) = Some W_7cc34.
Proof. vm_refl. Qed.
Lemma D_7cc34 : decode_any W_7cc34 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc38 : bv 32 := 0x05d00893.
Lemma F_7cc38 : fetch_word Ubsan.M.loaded_segments (0x7cc38 : word) = Some W_7cc38.
Proof. vm_refl. Qed.
Lemma D_7cc38 : decode_any W_7cc38 = Some (OpImm ALU_ADD 17 0 93, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc3c : bv 32 := 0x00000073.
Lemma F_7cc3c : fetch_word Ubsan.M.loaded_segments (0x7cc3c : word) = Some W_7cc3c.
Proof. vm_refl. Qed.
Lemma D_7cc3c : decode_any W_7cc3c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_7cc3c : is_ecall W_7cc3c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_7cc40 : bv 32 := 0xfe010113.
Lemma F_7cc40 : fetch_word Ubsan.M.loaded_segments (0x7cc40 : word) = Some W_7cc40.
Proof. vm_refl. Qed.
Lemma D_7cc40 : decode_any W_7cc40 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc44 : bv 32 := 0x00113c23.
Lemma F_7cc44 : fetch_word Ubsan.M.loaded_segments (0x7cc44 : word) = Some W_7cc44.
Proof. vm_refl. Qed.
Lemma D_7cc44 : decode_any W_7cc44 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc48 : bv 32 := 0x00813823.
Lemma F_7cc48 : fetch_word Ubsan.M.loaded_segments (0x7cc48 : word) = Some W_7cc48.
Proof. vm_refl. Qed.
Lemma D_7cc48 : decode_any W_7cc48 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc4c : bv 32 := 0x00913423.
Lemma F_7cc4c : fetch_word Ubsan.M.loaded_segments (0x7cc4c : word) = Some W_7cc4c.
Proof. vm_refl. Qed.
Lemma D_7cc4c : decode_any W_7cc4c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc50 : bv 32 := 0x0003b517.
Lemma F_7cc50 : fetch_word Ubsan.M.loaded_segments (0x7cc50 : word) = Some W_7cc50.
Proof. vm_refl. Qed.
Lemma D_7cc50 : decode_any W_7cc50 = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc54 : bv 32 := 0x04850413.
Lemma F_7cc54 : fetch_word Ubsan.M.loaded_segments (0x7cc54 : word) = Some W_7cc54.
Proof. vm_refl. Qed.
Lemma D_7cc54 : decode_any W_7cc54 = Some (OpImm ALU_ADD 8 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc58 : bv 32 := 0x00042603.
Lemma F_7cc58 : fetch_word Ubsan.M.loaded_segments (0x7cc58 : word) = Some W_7cc58.
Proof. vm_refl. Qed.
Lemma D_7cc58 : decode_any W_7cc58 = Some (Load SZ4 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc5c : bv 32 := 0x02060063.
Lemma F_7cc5c : fetch_word Ubsan.M.loaded_segments (0x7cc5c : word) = Some W_7cc5c.
Proof. vm_refl. Qed.
Lemma D_7cc5c : decode_any W_7cc5c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc60 : bv 32 := 0x00440493.
Lemma F_7cc60 : fetch_word Ubsan.M.loaded_segments (0x7cc60 : word) = Some W_7cc60.
Proof. vm_refl. Qed.
Lemma D_7cc60 : decode_any W_7cc60 = Some (OpImm ALU_ADD 9 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc64 : bv 32 := 0x00100693.
Lemma F_7cc64 : fetch_word Ubsan.M.loaded_segments (0x7cc64 : word) = Some W_7cc64.
Proof. vm_refl. Qed.
Lemma D_7cc64 : decode_any W_7cc64 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc68 : bv 32 := 0x00040513.
Lemma F_7cc68 : fetch_word Ubsan.M.loaded_segments (0x7cc68 : word) = Some W_7cc68.
Proof. vm_refl. Qed.
Lemma D_7cc68 : decode_any W_7cc68 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc6c : bv 32 := 0x00048593.
Lemma F_7cc6c : fetch_word Ubsan.M.loaded_segments (0x7cc6c : word) = Some W_7cc6c.
Proof. vm_refl. Qed.
Lemma D_7cc6c : decode_any W_7cc6c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc70 : bv 32 := 0xfc0fd0ef.
Lemma F_7cc70 : fetch_word Ubsan.M.loaded_segments (0x7cc70 : word) = Some W_7cc70.
Proof. vm_refl. Qed.
Lemma D_7cc70 : decode_any W_7cc70 = Some (Jal 1 2086848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc74 : bv 32 := 0x00042603.
Lemma F_7cc74 : fetch_word Ubsan.M.loaded_segments (0x7cc74 : word) = Some W_7cc74.
Proof. vm_refl. Qed.
Lemma D_7cc74 : decode_any W_7cc74 = Some (Load SZ4 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc78 : bv 32 := 0xfe0616e3.
Lemma F_7cc78 : fetch_word Ubsan.M.loaded_segments (0x7cc78 : word) = Some W_7cc78.
Proof. vm_refl. Qed.
Lemma D_7cc78 : decode_any W_7cc78 = Some (Branch BC_NE 12 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc7c : bv 32 := 0x01813083.
Lemma F_7cc7c : fetch_word Ubsan.M.loaded_segments (0x7cc7c : word) = Some W_7cc7c.
Proof. vm_refl. Qed.
Lemma D_7cc7c : decode_any W_7cc7c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc80 : bv 32 := 0x01013403.
Lemma F_7cc80 : fetch_word Ubsan.M.loaded_segments (0x7cc80 : word) = Some W_7cc80.
Proof. vm_refl. Qed.
Lemma D_7cc80 : decode_any W_7cc80 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc84 : bv 32 := 0x00813483.
Lemma F_7cc84 : fetch_word Ubsan.M.loaded_segments (0x7cc84 : word) = Some W_7cc84.
Proof. vm_refl. Qed.
Lemma D_7cc84 : decode_any W_7cc84 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc88 : bv 32 := 0x02010113.
Lemma F_7cc88 : fetch_word Ubsan.M.loaded_segments (0x7cc88 : word) = Some W_7cc88.
Proof. vm_refl. Qed.
Lemma D_7cc88 : decode_any W_7cc88 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc8c : bv 32 := 0x00008067.
Lemma F_7cc8c : fetch_word Ubsan.M.loaded_segments (0x7cc8c : word) = Some W_7cc8c.
Proof. vm_refl. Qed.
Lemma D_7cc8c : decode_any W_7cc8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc90 : bv 32 := 0x0003b517.
Lemma F_7cc90 : fetch_word Ubsan.M.loaded_segments (0x7cc90 : word) = Some W_7cc90.
Proof. vm_refl. Qed.
Lemma D_7cc90 : decode_any W_7cc90 = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc94 : bv 32 := 0x00850513.
Lemma F_7cc94 : fetch_word Ubsan.M.loaded_segments (0x7cc94 : word) = Some W_7cc94.
Proof. vm_refl. Qed.
Lemma D_7cc94 : decode_any W_7cc94 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc98 : bv 32 := 0x00052583.
Lemma F_7cc98 : fetch_word Ubsan.M.loaded_segments (0x7cc98 : word) = Some W_7cc98.
Proof. vm_refl. Qed.
Lemma D_7cc98 : decode_any W_7cc98 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc9c : bv 32 := 0x0015861b.
Lemma F_7cc9c : fetch_word Ubsan.M.loaded_segments (0x7cc9c : word) = Some W_7cc9c.
Proof. vm_refl. Qed.
Lemma D_7cc9c : decode_any W_7cc9c = Some (OpImm32 12 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cca0 : bv 32 := 0x160526af.
Lemma F_7cca0 : fetch_word Ubsan.M.loaded_segments (0x7cca0 : word) = Some W_7cca0.
Proof. vm_refl. Qed.
Lemma D_7cca0 : decode_any W_7cca0 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cca4 : bv 32 := 0x00b69663.
Lemma F_7cca4 : fetch_word Ubsan.M.loaded_segments (0x7cca4 : word) = Some W_7cca4.
Proof. vm_refl. Qed.
Lemma D_7cca4 : decode_any W_7cca4 = Some (Branch BC_NE 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cca8 : bv 32 := 0x1ec5272f.
Lemma F_7cca8 : fetch_word Ubsan.M.loaded_segments (0x7cca8 : word) = Some W_7cca8.
Proof. vm_refl. Qed.
Lemma D_7cca8 : decode_any W_7cca8 = Some (Sc AW true true 14 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccac : bv 32 := 0xfe071ae3.
Lemma F_7ccac : fetch_word Ubsan.M.loaded_segments (0x7ccac : word) = Some W_7ccac.
Proof. vm_refl. Qed.
Lemma D_7ccac : decode_any W_7ccac = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccb0 : bv 32 := 0x0006869b.
Lemma F_7ccb0 : fetch_word Ubsan.M.loaded_segments (0x7ccb0 : word) = Some W_7ccb0.
Proof. vm_refl. Qed.
Lemma D_7ccb0 : decode_any W_7ccb0 = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccb4 : bv 32 := 0xfeb692e3.
Lemma F_7ccb4 : fetch_word Ubsan.M.loaded_segments (0x7ccb4 : word) = Some W_7ccb4.
Proof. vm_refl. Qed.
Lemma D_7ccb4 : decode_any W_7ccb4 = Some (Branch BC_NE 13 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccb8 : bv 32 := 0x00008067.
Lemma F_7ccb8 : fetch_word Ubsan.M.loaded_segments (0x7ccb8 : word) = Some W_7ccb8.
Proof. vm_refl. Qed.
Lemma D_7ccb8 : decode_any W_7ccb8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccbc : bv 32 := 0x0003b517.
Lemma F_7ccbc : fetch_word Ubsan.M.loaded_segments (0x7ccbc : word) = Some W_7ccbc.
Proof. vm_refl. Qed.
Lemma D_7ccbc : decode_any W_7ccbc = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccc0 : bv 32 := 0xfdc50513.
Lemma F_7ccc0 : fetch_word Ubsan.M.loaded_segments (0x7ccc0 : word) = Some W_7ccc0.
Proof. vm_refl. Qed.
Lemma D_7ccc0 : decode_any W_7ccc0 = Some (OpImm ALU_ADD 10 10 4060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccc4 : bv 32 := 0x00052583.
Lemma F_7ccc4 : fetch_word Ubsan.M.loaded_segments (0x7ccc4 : word) = Some W_7ccc4.
Proof. vm_refl. Qed.
Lemma D_7ccc4 : decode_any W_7ccc4 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccc8 : bv 32 := 0xfff5861b.
Lemma F_7ccc8 : fetch_word Ubsan.M.loaded_segments (0x7ccc8 : word) = Some W_7ccc8.
Proof. vm_refl. Qed.
Lemma D_7ccc8 : decode_any W_7ccc8 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cccc : bv 32 := 0x160526af.
Lemma F_7cccc : fetch_word Ubsan.M.loaded_segments (0x7cccc : word) = Some W_7cccc.
Proof. vm_refl. Qed.
Lemma D_7cccc : decode_any W_7cccc = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccd0 : bv 32 := 0x00b69663.
Lemma F_7ccd0 : fetch_word Ubsan.M.loaded_segments (0x7ccd0 : word) = Some W_7ccd0.
Proof. vm_refl. Qed.
Lemma D_7ccd0 : decode_any W_7ccd0 = Some (Branch BC_NE 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccd4 : bv 32 := 0x1ec5272f.
Lemma F_7ccd4 : fetch_word Ubsan.M.loaded_segments (0x7ccd4 : word) = Some W_7ccd4.
Proof. vm_refl. Qed.
Lemma D_7ccd4 : decode_any W_7ccd4 = Some (Sc AW true true 14 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccd8 : bv 32 := 0xfe071ae3.
Lemma F_7ccd8 : fetch_word Ubsan.M.loaded_segments (0x7ccd8 : word) = Some W_7ccd8.
Proof. vm_refl. Qed.
Lemma D_7ccd8 : decode_any W_7ccd8 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccdc : bv 32 := 0x0006869b.
Lemma F_7ccdc : fetch_word Ubsan.M.loaded_segments (0x7ccdc : word) = Some W_7ccdc.
Proof. vm_refl. Qed.
Lemma D_7ccdc : decode_any W_7ccdc = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cce0 : bv 32 := 0xfeb692e3.
Lemma F_7cce0 : fetch_word Ubsan.M.loaded_segments (0x7cce0 : word) = Some W_7cce0.
Proof. vm_refl. Qed.
Lemma D_7cce0 : decode_any W_7cce0 = Some (Branch BC_NE 13 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cce4 : bv 32 := 0x00100613.
Lemma F_7cce4 : fetch_word Ubsan.M.loaded_segments (0x7cce4 : word) = Some W_7cce4.
Proof. vm_refl. Qed.
Lemma D_7cce4 : decode_any W_7cce4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cce8 : bv 32 := 0x04c59263.
Lemma F_7cce8 : fetch_word Ubsan.M.loaded_segments (0x7cce8 : word) = Some W_7cce8.
Proof. vm_refl. Qed.
Lemma D_7cce8 : decode_any W_7cce8 = Some (Branch BC_NE 11 12 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccec : bv 32 := 0x00452503.
Lemma F_7ccec : fetch_word Ubsan.M.loaded_segments (0x7ccec : word) = Some W_7ccec.
Proof. vm_refl. Qed.
Lemma D_7ccec : decode_any W_7ccec = Some (Load SZ4 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccf0 : bv 32 := 0x02050e63.
Lemma F_7ccf0 : fetch_word Ubsan.M.loaded_segments (0x7ccf0 : word) = Some W_7ccf0.
Proof. vm_refl. Qed.
Lemma D_7ccf0 : decode_any W_7ccf0 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccf4 : bv 32 := 0x0003b517.
Lemma F_7ccf4 : fetch_word Ubsan.M.loaded_segments (0x7ccf4 : word) = Some W_7ccf4.
Proof. vm_refl. Qed.
Lemma D_7ccf4 : decode_any W_7ccf4 = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccf8 : bv 32 := 0x80000637.
Lemma F_7ccf8 : fetch_word Ubsan.M.loaded_segments (0x7ccf8 : word) = Some W_7ccf8.
Proof. vm_refl. Qed.
Lemma D_7ccf8 : decode_any W_7ccf8 = Some (Lui 12 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccfc : bv 32 := 0x06200893.
Lemma F_7ccfc : fetch_word Ubsan.M.loaded_segments (0x7ccfc : word) = Some W_7ccfc.
Proof. vm_refl. Qed.
Lemma D_7ccfc : decode_any W_7ccfc = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd00 : bv 32 := 0xfa450513.
Lemma F_7cd00 : fetch_word Ubsan.M.loaded_segments (0x7cd00 : word) = Some W_7cd00.
Proof. vm_refl. Qed.
Lemma D_7cd00 : decode_any W_7cd00 = Some (OpImm ALU_ADD 10 10 4004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd04 : bv 32 := 0xfff6061b.
Lemma F_7cd04 : fetch_word Ubsan.M.loaded_segments (0x7cd04 : word) = Some W_7cd04.
Proof. vm_refl. Qed.
Lemma D_7cd04 : decode_any W_7cd04 = Some (OpImm32 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd08 : bv 32 := 0x08100593.
Lemma F_7cd08 : fetch_word Ubsan.M.loaded_segments (0x7cd08 : word) = Some W_7cd08.
Proof. vm_refl. Qed.
Lemma D_7cd08 : decode_any W_7cd08 = Some (OpImm ALU_ADD 11 0 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd0c : bv 32 := 0xfda00693.
Lemma F_7cd0c : fetch_word Ubsan.M.loaded_segments (0x7cd0c : word) = Some W_7cd0c.
Proof. vm_refl. Qed.
Lemma D_7cd0c : decode_any W_7cd0c = Some (OpImm ALU_ADD 13 0 4058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd10 : bv 32 := 0x00000073.
Lemma F_7cd10 : fetch_word Ubsan.M.loaded_segments (0x7cd10 : word) = Some W_7cd10.
Proof. vm_refl. Qed.
Lemma D_7cd10 : decode_any W_7cd10 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_7cd10 : is_ecall W_7cd10 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_7cd14 : bv 32 := 0x00d51c63.
Lemma F_7cd14 : fetch_word Ubsan.M.loaded_segments (0x7cd14 : word) = Some W_7cd14.
Proof. vm_refl. Qed.
Lemma D_7cd14 : decode_any W_7cd14 = Some (Branch BC_NE 10 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd18 : bv 32 := 0x0003b517.
Lemma F_7cd18 : fetch_word Ubsan.M.loaded_segments (0x7cd18 : word) = Some W_7cd18.
Proof. vm_refl. Qed.
Lemma D_7cd18 : decode_any W_7cd18 = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd1c : bv 32 := 0xf8050513.
Lemma F_7cd1c : fetch_word Ubsan.M.loaded_segments (0x7cd1c : word) = Some W_7cd1c.
Proof. vm_refl. Qed.
Lemma D_7cd1c : decode_any W_7cd1c = Some (OpImm ALU_ADD 10 10 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd20 : bv 32 := 0x06200893.
Lemma F_7cd20 : fetch_word Ubsan.M.loaded_segments (0x7cd20 : word) = Some W_7cd20.
Proof. vm_refl. Qed.
Lemma D_7cd20 : decode_any W_7cd20 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd24 : bv 32 := 0x00100593.
Lemma F_7cd24 : fetch_word Ubsan.M.loaded_segments (0x7cd24 : word) = Some W_7cd24.
Proof. vm_refl. Qed.
Lemma D_7cd24 : decode_any W_7cd24 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd28 : bv 32 := 0x00000073.
Lemma F_7cd28 : fetch_word Ubsan.M.loaded_segments (0x7cd28 : word) = Some W_7cd28.
Proof. vm_refl. Qed.
Lemma D_7cd28 : decode_any W_7cd28 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_7cd28 : is_ecall W_7cd28 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_7cd2c : bv 32 := 0x00008067.
Lemma F_7cd2c : fetch_word Ubsan.M.loaded_segments (0x7cd2c : word) = Some W_7cd2c.
Proof. vm_refl. Qed.
Lemma D_7cd2c : decode_any W_7cd2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
