(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1cc20 : bv 32 := 0xffff3197.
Lemma F_1cc20 : fetch_word Ubsan.M.loaded_segments (0x1d100 : word) = Some W_1cc20.
Proof. vm_refl. Qed.
Lemma D_1cc20 : decode_any W_1cc20 = Some (Auipc 3 1048563, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc24 : bv 32 := 0x70018193.
Lemma F_1cc24 : fetch_word Ubsan.M.loaded_segments (0x1d104 : word) = Some W_1cc24.
Proof. vm_refl. Qed.
Lemma D_1cc24 : decode_any W_1cc24 = Some (OpImm ALU_ADD 3 3 1792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc28 : bv 32 := 0x00010513.
Lemma F_1cc28 : fetch_word Ubsan.M.loaded_segments (0x1d108 : word) = Some W_1cc28.
Proof. vm_refl. Qed.
Lemma D_1cc28 : decode_any W_1cc28 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc2c : bv 32 := 0xfffe3597.
Lemma F_1cc2c : fetch_word Ubsan.M.loaded_segments (0x1d10c : word) = Some W_1cc2c.
Proof. vm_refl. Qed.
Lemma D_1cc2c : decode_any W_1cc2c = Some (Auipc 11 1048547, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc30 : bv 32 := 0xef458593.
Lemma F_1cc30 : fetch_word Ubsan.M.loaded_segments (0x1d110 : word) = Some W_1cc30.
Proof. vm_refl. Qed.
Lemma D_1cc30 : decode_any W_1cc30 = Some (OpImm ALU_ADD 11 11 3828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc34 : bv 32 := 0xff017113.
Lemma F_1cc34 : fetch_word Ubsan.M.loaded_segments (0x1d114 : word) = Some W_1cc34.
Proof. vm_refl. Qed.
Lemma D_1cc34 : decode_any W_1cc34 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc38 : bv 32 := 0x0040006f.
Lemma F_1cc38 : fetch_word Ubsan.M.loaded_segments (0x1d118 : word) = Some W_1cc38.
Proof. vm_refl. Qed.
Lemma D_1cc38 : decode_any W_1cc38 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc3c : bv 32 := 0x00052583.
Lemma F_1cc3c : fetch_word Ubsan.M.loaded_segments (0x1d11c : word) = Some W_1cc3c.
Proof. vm_refl. Qed.
Lemma D_1cc3c : decode_any W_1cc3c = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc40 : bv 32 := 0x0002f617.
Lemma F_1cc40 : fetch_word Ubsan.M.loaded_segments (0x1d120 : word) = Some W_1cc40.
Proof. vm_refl. Qed.
Lemma D_1cc40 : decode_any W_1cc40 = Some (Auipc 12 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc44 : bv 32 := 0x0002f697.
Lemma F_1cc44 : fetch_word Ubsan.M.loaded_segments (0x1d124 : word) = Some W_1cc44.
Proof. vm_refl. Qed.
Lemma D_1cc44 : decode_any W_1cc44 = Some (Auipc 13 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc48 : bv 32 := 0x0002f717.
Lemma F_1cc48 : fetch_word Ubsan.M.loaded_segments (0x1d128 : word) = Some W_1cc48.
Proof. vm_refl. Qed.
Lemma D_1cc48 : decode_any W_1cc48 = Some (Auipc 14 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc4c : bv 32 := 0xb4063783.
Lemma F_1cc4c : fetch_word Ubsan.M.loaded_segments (0x1d12c : word) = Some W_1cc4c.
Proof. vm_refl. Qed.
Lemma D_1cc4c : decode_any W_1cc4c = Some (Load SZ8 true 15 12 2880, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc50 : bv 32 := 0xb446b683.
Lemma F_1cc50 : fetch_word Ubsan.M.loaded_segments (0x1d130 : word) = Some W_1cc50.
Proof. vm_refl. Qed.
Lemma D_1cc50 : decode_any W_1cc50 = Some (Load SZ8 true 13 13 2884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc54 : bv 32 := 0xb4873703.
Lemma F_1cc54 : fetch_word Ubsan.M.loaded_segments (0x1d134 : word) = Some W_1cc54.
Proof. vm_refl. Qed.
Lemma D_1cc54 : decode_any W_1cc54 = Some (Load SZ8 true 14 14 2888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc58 : bv 32 := 0x00850613.
Lemma F_1cc58 : fetch_word Ubsan.M.loaded_segments (0x1d138 : word) = Some W_1cc58.
Proof. vm_refl. Qed.
Lemma D_1cc58 : decode_any W_1cc58 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc5c : bv 32 := 0x00078513.
Lemma F_1cc5c : fetch_word Ubsan.M.loaded_segments (0x1d13c : word) = Some W_1cc5c.
Proof. vm_refl. Qed.
Lemma D_1cc5c : decode_any W_1cc5c = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc60 : bv 32 := 0x00000793.
Lemma F_1cc60 : fetch_word Ubsan.M.loaded_segments (0x1d140 : word) = Some W_1cc60.
Proof. vm_refl. Qed.
Lemma D_1cc60 : decode_any W_1cc60 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc64 : bv 32 := 0x0c02206f.
Lemma F_1cc64 : fetch_word Ubsan.M.loaded_segments (0x1d144 : word) = Some W_1cc64.
Proof. vm_refl. Qed.
Lemma D_1cc64 : decode_any W_1cc64 = Some (Jal 0 139456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc68 : bv 32 := 0xff010113.
Lemma F_1cc68 : fetch_word Ubsan.M.loaded_segments (0x1d148 : word) = Some W_1cc68.
Proof. vm_refl. Qed.
Lemma D_1cc68 : decode_any W_1cc68 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc6c : bv 32 := 0x00113423.
Lemma F_1cc6c : fetch_word Ubsan.M.loaded_segments (0x1d14c : word) = Some W_1cc6c.
Proof. vm_refl. Qed.
Lemma D_1cc6c : decode_any W_1cc6c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc70 : bv 32 := 0x00813023.
Lemma F_1cc70 : fetch_word Ubsan.M.loaded_segments (0x1d150 : word) = Some W_1cc70.
Proof. vm_refl. Qed.
Lemma D_1cc70 : decode_any W_1cc70 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc74 : bv 32 := 0x01010413.
Lemma F_1cc74 : fetch_word Ubsan.M.loaded_segments (0x1d154 : word) = Some W_1cc74.
Proof. vm_refl. Qed.
Lemma D_1cc74 : decode_any W_1cc74 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc78 : bv 32 := 0x00030517.
Lemma F_1cc78 : fetch_word Ubsan.M.loaded_segments (0x1d158 : word) = Some W_1cc78.
Proof. vm_refl. Qed.
Lemma D_1cc78 : decode_any W_1cc78 = Some (Auipc 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc7c : bv 32 := 0xdc850513.
Lemma F_1cc7c : fetch_word Ubsan.M.loaded_segments (0x1d15c : word) = Some W_1cc7c.
Proof. vm_refl. Qed.
Lemma D_1cc7c : decode_any W_1cc7c = Some (OpImm ALU_ADD 10 10 3528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc80 : bv 32 := 0x00054503.
Lemma F_1cc80 : fetch_word Ubsan.M.loaded_segments (0x1d160 : word) = Some W_1cc80.
Proof. vm_refl. Qed.
Lemma D_1cc80 : decode_any W_1cc80 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc84 : bv 32 := 0x00157513.
Lemma F_1cc84 : fetch_word Ubsan.M.loaded_segments (0x1d164 : word) = Some W_1cc84.
Proof. vm_refl. Qed.
Lemma D_1cc84 : decode_any W_1cc84 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc88 : bv 32 := 0x00050663.
Lemma F_1cc88 : fetch_word Ubsan.M.loaded_segments (0x1d168 : word) = Some W_1cc88.
Proof. vm_refl. Qed.
Lemma D_1cc88 : decode_any W_1cc88 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc94 : bv 32 := 0x00030517.
Lemma F_1cc94 : fetch_word Ubsan.M.loaded_segments (0x1d174 : word) = Some W_1cc94.
Proof. vm_refl. Qed.
Lemma D_1cc94 : decode_any W_1cc94 = Some (Auipc 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc98 : bv 32 := 0xdac50593.
Lemma F_1cc98 : fetch_word Ubsan.M.loaded_segments (0x1d178 : word) = Some W_1cc98.
Proof. vm_refl. Qed.
Lemma D_1cc98 : decode_any W_1cc98 = Some (OpImm ALU_ADD 11 10 3500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc9c : bv 32 := 0x00100513.
Lemma F_1cc9c : fetch_word Ubsan.M.loaded_segments (0x1d17c : word) = Some W_1cc9c.
Proof. vm_refl. Qed.
Lemma D_1cc9c : decode_any W_1cc9c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cca0 : bv 32 := 0x00a58023.
Lemma F_1cca0 : fetch_word Ubsan.M.loaded_segments (0x1d180 : word) = Some W_1cca0.
Proof. vm_refl. Qed.
Lemma D_1cca0 : decode_any W_1cca0 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cca4 : bv 32 := 0x0002f517.
Lemma F_1cca4 : fetch_word Ubsan.M.loaded_segments (0x1d184 : word) = Some W_1cca4.
Proof. vm_refl. Qed.
Lemma D_1cca4 : decode_any W_1cca4 = Some (Auipc 10 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cca8 : bv 32 := 0xaf453503.
Lemma F_1cca8 : fetch_word Ubsan.M.loaded_segments (0x1d188 : word) = Some W_1cca8.
Proof. vm_refl. Qed.
Lemma D_1cca8 : decode_any W_1cca8 = Some (Load SZ8 true 10 10 2804, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ccac : bv 32 := 0x02050063.
Lemma F_1ccac : fetch_word Ubsan.M.loaded_segments (0x1d18c : word) = Some W_1ccac.
Proof. vm_refl. Qed.
Lemma D_1ccac : decode_any W_1ccac = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cccc : bv 32 := 0x00813083.
Lemma F_1cccc : fetch_word Ubsan.M.loaded_segments (0x1d1ac : word) = Some W_1cccc.
Proof. vm_refl. Qed.
Lemma D_1cccc : decode_any W_1cccc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ccd0 : bv 32 := 0x00013403.
Lemma F_1ccd0 : fetch_word Ubsan.M.loaded_segments (0x1d1b0 : word) = Some W_1ccd0.
Proof. vm_refl. Qed.
Lemma D_1ccd0 : decode_any W_1ccd0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ccd4 : bv 32 := 0x01010113.
Lemma F_1ccd4 : fetch_word Ubsan.M.loaded_segments (0x1d1b4 : word) = Some W_1ccd4.
Proof. vm_refl. Qed.
Lemma D_1ccd4 : decode_any W_1ccd4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ccd8 : bv 32 := 0x00008067.
Lemma F_1ccd8 : fetch_word Ubsan.M.loaded_segments (0x1d1b8 : word) = Some W_1ccd8.
Proof. vm_refl. Qed.
Lemma D_1ccd8 : decode_any W_1ccd8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ccdc : bv 32 := 0xff010113.
Lemma F_1ccdc : fetch_word Ubsan.M.loaded_segments (0x1d1bc : word) = Some W_1ccdc.
Proof. vm_refl. Qed.
Lemma D_1ccdc : decode_any W_1ccdc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cce0 : bv 32 := 0x00113423.
Lemma F_1cce0 : fetch_word Ubsan.M.loaded_segments (0x1d1c0 : word) = Some W_1cce0.
Proof. vm_refl. Qed.
Lemma D_1cce0 : decode_any W_1cce0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cce4 : bv 32 := 0x00813023.
Lemma F_1cce4 : fetch_word Ubsan.M.loaded_segments (0x1d1c4 : word) = Some W_1cce4.
Proof. vm_refl. Qed.
Lemma D_1cce4 : decode_any W_1cce4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cce8 : bv 32 := 0x01010413.
Lemma F_1cce8 : fetch_word Ubsan.M.loaded_segments (0x1d1c8 : word) = Some W_1cce8.
Proof. vm_refl. Qed.
Lemma D_1cce8 : decode_any W_1cce8 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ccec : bv 32 := 0x00030517.
Lemma F_1ccec : fetch_word Ubsan.M.loaded_segments (0x1d1cc : word) = Some W_1ccec.
Proof. vm_refl. Qed.
Lemma D_1ccec : decode_any W_1ccec = Some (Auipc 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ccf0 : bv 32 := 0xd9c50513.
Lemma F_1ccf0 : fetch_word Ubsan.M.loaded_segments (0x1d1d0 : word) = Some W_1ccf0.
Proof. vm_refl. Qed.
Lemma D_1ccf0 : decode_any W_1ccf0 = Some (OpImm ALU_ADD 10 10 3484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ccf4 : bv 32 := 0x00054503.
Lemma F_1ccf4 : fetch_word Ubsan.M.loaded_segments (0x1d1d4 : word) = Some W_1ccf4.
Proof. vm_refl. Qed.
Lemma D_1ccf4 : decode_any W_1ccf4 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ccf8 : bv 32 := 0x00157513.
Lemma F_1ccf8 : fetch_word Ubsan.M.loaded_segments (0x1d1d8 : word) = Some W_1ccf8.
Proof. vm_refl. Qed.
Lemma D_1ccf8 : decode_any W_1ccf8 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ccfc : bv 32 := 0x00050663.
Lemma F_1ccfc : fetch_word Ubsan.M.loaded_segments (0x1d1dc : word) = Some W_1ccfc.
Proof. vm_refl. Qed.
Lemma D_1ccfc : decode_any W_1ccfc = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd08 : bv 32 := 0x00030517.
Lemma F_1cd08 : fetch_word Ubsan.M.loaded_segments (0x1d1e8 : word) = Some W_1cd08.
Proof. vm_refl. Qed.
Lemma D_1cd08 : decode_any W_1cd08 = Some (Auipc 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd0c : bv 32 := 0xd8050593.
Lemma F_1cd0c : fetch_word Ubsan.M.loaded_segments (0x1d1ec : word) = Some W_1cd0c.
Proof. vm_refl. Qed.
Lemma D_1cd0c : decode_any W_1cd0c = Some (OpImm ALU_ADD 11 10 3456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd10 : bv 32 := 0x00100513.
Lemma F_1cd10 : fetch_word Ubsan.M.loaded_segments (0x1d1f0 : word) = Some W_1cd10.
Proof. vm_refl. Qed.
Lemma D_1cd10 : decode_any W_1cd10 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd14 : bv 32 := 0x00a58023.
Lemma F_1cd14 : fetch_word Ubsan.M.loaded_segments (0x1d1f4 : word) = Some W_1cd14.
Proof. vm_refl. Qed.
Lemma D_1cd14 : decode_any W_1cd14 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd18 : bv 32 := 0x0002f517.
Lemma F_1cd18 : fetch_word Ubsan.M.loaded_segments (0x1d1f8 : word) = Some W_1cd18.
Proof. vm_refl. Qed.
Lemma D_1cd18 : decode_any W_1cd18 = Some (Auipc 10 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd1c : bv 32 := 0xa8853503.
Lemma F_1cd1c : fetch_word Ubsan.M.loaded_segments (0x1d1fc : word) = Some W_1cd1c.
Proof. vm_refl. Qed.
Lemma D_1cd1c : decode_any W_1cd1c = Some (Load SZ8 true 10 10 2696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd20 : bv 32 := 0x00050e63.
Lemma F_1cd20 : fetch_word Ubsan.M.loaded_segments (0x1d200 : word) = Some W_1cd20.
Proof. vm_refl. Qed.
Lemma D_1cd20 : decode_any W_1cd20 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd24 : bv 32 := 0x0040006f.
Lemma F_1cd24 : fetch_word Ubsan.M.loaded_segments (0x1d204 : word) = Some W_1cd24.
Proof. vm_refl. Qed.
Lemma D_1cd24 : decode_any W_1cd24 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd28 : bv 32 := 0x00030517.
Lemma F_1cd28 : fetch_word Ubsan.M.loaded_segments (0x1d208 : word) = Some W_1cd28.
Proof. vm_refl. Qed.
Lemma D_1cd28 : decode_any W_1cd28 = Some (Auipc 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd2c : bv 32 := 0xae850513.
Lemma F_1cd2c : fetch_word Ubsan.M.loaded_segments (0x1d20c : word) = Some W_1cd2c.
Proof. vm_refl. Qed.
Lemma D_1cd2c : decode_any W_1cd2c = Some (OpImm ALU_ADD 10 10 2792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd30 : bv 32 := 0x00053503.
Lemma F_1cd30 : fetch_word Ubsan.M.loaded_segments (0x1d210 : word) = Some W_1cd30.
Proof. vm_refl. Qed.
Lemma D_1cd30 : decode_any W_1cd30 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd34 : bv 32 := 0x41c220ef.
Lemma F_1cd34 : fetch_word Ubsan.M.loaded_segments (0x1d214 : word) = Some W_1cd34.
Proof. vm_refl. Qed.
Lemma D_1cd34 : decode_any W_1cd34 = Some (Jal 1 140316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd38 : bv 32 := 0x0040006f.
Lemma F_1cd38 : fetch_word Ubsan.M.loaded_segments (0x1d218 : word) = Some W_1cd38.
Proof. vm_refl. Qed.
Lemma D_1cd38 : decode_any W_1cd38 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd3c : bv 32 := 0x0002f517.
Lemma F_1cd3c : fetch_word Ubsan.M.loaded_segments (0x1d21c : word) = Some W_1cd3c.
Proof. vm_refl. Qed.
Lemma D_1cd3c : decode_any W_1cd3c = Some (Auipc 10 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd40 : bv 32 := 0xa6c53503.
Lemma F_1cd40 : fetch_word Ubsan.M.loaded_segments (0x1d220 : word) = Some W_1cd40.
Proof. vm_refl. Qed.
Lemma D_1cd40 : decode_any W_1cd40 = Some (Load SZ8 true 10 10 2668, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd44 : bv 32 := 0x00050c63.
Lemma F_1cd44 : fetch_word Ubsan.M.loaded_segments (0x1d224 : word) = Some W_1cd44.
Proof. vm_refl. Qed.
Lemma D_1cd44 : decode_any W_1cd44 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd5c : bv 32 := 0x00813083.
Lemma F_1cd5c : fetch_word Ubsan.M.loaded_segments (0x1d23c : word) = Some W_1cd5c.
Proof. vm_refl. Qed.
Lemma D_1cd5c : decode_any W_1cd5c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd60 : bv 32 := 0x00013403.
Lemma F_1cd60 : fetch_word Ubsan.M.loaded_segments (0x1d240 : word) = Some W_1cd60.
Proof. vm_refl. Qed.
Lemma D_1cd60 : decode_any W_1cd60 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd64 : bv 32 := 0x01010113.
Lemma F_1cd64 : fetch_word Ubsan.M.loaded_segments (0x1d244 : word) = Some W_1cd64.
Proof. vm_refl. Qed.
Lemma D_1cd64 : decode_any W_1cd64 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cd68 : bv 32 := 0x00008067.
Lemma F_1cd68 : fetch_word Ubsan.M.loaded_segments (0x1d248 : word) = Some W_1cd68.
Proof. vm_refl. Qed.
Lemma D_1cd68 : decode_any W_1cd68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
