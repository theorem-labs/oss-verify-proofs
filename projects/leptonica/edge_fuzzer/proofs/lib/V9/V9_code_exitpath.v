(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.H Require GcFlushU9.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5cb90 : bv 32 := 0xffff3517.
Lemma F_5cb90 : fetch_word Ubsan.M.loaded_segments (0x5cbe8 : word) = Some W_5cb90.
Proof. vm_refl. Qed.
Lemma D_5cb90 : decode_any W_5cb90 = Some (Auipc 10 1048563, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cb94 : bv 32 := 0x39050513.
Lemma F_5cb94 : fetch_word Ubsan.M.loaded_segments (0x5cbec : word) = Some W_5cb94.
Proof. vm_refl. Qed.
Lemma D_5cb94 : decode_any W_5cb94 = Some (OpImm ALU_ADD 10 10 912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cb98 : bv 32 := 0x0009e597.
Lemma F_5cb98 : fetch_word Ubsan.M.loaded_segments (0x5cbf0 : word) = Some W_5cb98.
Proof. vm_refl. Qed.
Lemma D_5cb98 : decode_any W_5cb98 = Some (Auipc 11 158, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cb9c : bv 32 := 0x96858593.
Lemma F_5cb9c : fetch_word Ubsan.M.loaded_segments (0x5cbf4 : word) = Some W_5cb9c.
Proof. vm_refl. Qed.
Lemma D_5cb9c : decode_any W_5cb9c = Some (OpImm ALU_ADD 11 11 2408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cba0 : bv 32 := 0x000000ef.
Lemma F_5cba0 : fetch_word Ubsan.M.loaded_segments (0x5cbf8 : word) = Some W_5cba0.
Proof. vm_refl. Qed.
Lemma D_5cba0 : decode_any W_5cba0 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cba4 : bv 32 := 0x0040006f.
Lemma F_5cba4 : fetch_word Ubsan.M.loaded_segments (0x5cbfc : word) = Some W_5cba4.
Proof. vm_refl. Qed.
Lemma D_5cba4 : decode_any W_5cba4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cba8 : bv 32 := 0x00813083.
Lemma F_5cba8 : fetch_word Ubsan.M.loaded_segments (0x5cc00 : word) = Some W_5cba8.
Proof. vm_refl. Qed.
Lemma D_5cba8 : decode_any W_5cba8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbac : bv 32 := 0x00013403.
Lemma F_5cbac : fetch_word Ubsan.M.loaded_segments (0x5cc04 : word) = Some W_5cbac.
Proof. vm_refl. Qed.
Lemma D_5cbac : decode_any W_5cbac = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbb0 : bv 32 := 0x01010113.
Lemma F_5cbb0 : fetch_word Ubsan.M.loaded_segments (0x5cc08 : word) = Some W_5cbb0.
Proof. vm_refl. Qed.
Lemma D_5cbb0 : decode_any W_5cbb0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbb4 : bv 32 := 0x00008067.
Lemma F_5cbb4 : fetch_word Ubsan.M.loaded_segments (0x5cc0c : word) = Some W_5cbb4.
Proof. vm_refl. Qed.
Lemma D_5cbb4 : decode_any W_5cbb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbb8 : bv 32 := 0xff010113.
Lemma F_5cbb8 : fetch_word Ubsan.M.loaded_segments (0x5cc10 : word) = Some W_5cbb8.
Proof. vm_refl. Qed.
Lemma D_5cbb8 : decode_any W_5cbb8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbbc : bv 32 := 0x00113423.
Lemma F_5cbbc : fetch_word Ubsan.M.loaded_segments (0x5cc14 : word) = Some W_5cbbc.
Proof. vm_refl. Qed.
Lemma D_5cbbc : decode_any W_5cbbc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbc0 : bv 32 := 0x00813023.
Lemma F_5cbc0 : fetch_word Ubsan.M.loaded_segments (0x5cc18 : word) = Some W_5cbc0.
Proof. vm_refl. Qed.
Lemma D_5cbc0 : decode_any W_5cbc0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbc4 : bv 32 := 0x01010413.
Lemma F_5cbc4 : fetch_word Ubsan.M.loaded_segments (0x5cc1c : word) = Some W_5cbc4.
Proof. vm_refl. Qed.
Lemma D_5cbc4 : decode_any W_5cbc4 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbc8 : bv 32 := 0x0009e517.
Lemma F_5cbc8 : fetch_word Ubsan.M.loaded_segments (0x5cc20 : word) = Some W_5cbc8.
Proof. vm_refl. Qed.
Lemma D_5cbc8 : decode_any W_5cbc8 = Some (Auipc 10 158, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbcc : bv 32 := 0x97850513.
Lemma F_5cbcc : fetch_word Ubsan.M.loaded_segments (0x5cc24 : word) = Some W_5cbcc.
Proof. vm_refl. Qed.
Lemma D_5cbcc : decode_any W_5cbcc = Some (OpImm ALU_ADD 10 10 2424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbd0 : bv 32 := 0x00054503.
Lemma F_5cbd0 : fetch_word Ubsan.M.loaded_segments (0x5cc28 : word) = Some W_5cbd0.
Proof. vm_refl. Qed.
Lemma D_5cbd0 : decode_any W_5cbd0 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbd4 : bv 32 := 0x00157513.
Lemma F_5cbd4 : fetch_word Ubsan.M.loaded_segments (0x5cc2c : word) = Some W_5cbd4.
Proof. vm_refl. Qed.
Lemma D_5cbd4 : decode_any W_5cbd4 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbd8 : bv 32 := 0x00050663.
Lemma F_5cbd8 : fetch_word Ubsan.M.loaded_segments (0x5cc30 : word) = Some W_5cbd8.
Proof. vm_refl. Qed.
Lemma D_5cbd8 : decode_any W_5cbd8 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbdc : bv 32 := 0x0040006f.
Lemma F_5cbdc : fetch_word Ubsan.M.loaded_segments (0x5cc34 : word) = Some W_5cbdc.
Proof. vm_refl. Qed.
Lemma D_5cbdc : decode_any W_5cbdc = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbe0 : bv 32 := 0x0580006f.
Lemma F_5cbe0 : fetch_word Ubsan.M.loaded_segments (0x5cc38 : word) = Some W_5cbe0.
Proof. vm_refl. Qed.
Lemma D_5cbe0 : decode_any W_5cbe0 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbe4 : bv 32 := 0x0009e517.
Lemma F_5cbe4 : fetch_word Ubsan.M.loaded_segments (0x5cc3c : word) = Some W_5cbe4.
Proof. vm_refl. Qed.
Lemma D_5cbe4 : decode_any W_5cbe4 = Some (Auipc 10 158, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbe8 : bv 32 := 0x95c50593.
Lemma F_5cbe8 : fetch_word Ubsan.M.loaded_segments (0x5cc40 : word) = Some W_5cbe8.
Proof. vm_refl. Qed.
Lemma D_5cbe8 : decode_any W_5cbe8 = Some (OpImm ALU_ADD 11 10 2396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbec : bv 32 := 0x00100513.
Lemma F_5cbec : fetch_word Ubsan.M.loaded_segments (0x5cc44 : word) = Some W_5cbec.
Proof. vm_refl. Qed.
Lemma D_5cbec : decode_any W_5cbec = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbf0 : bv 32 := 0x00a58023.
Lemma F_5cbf0 : fetch_word Ubsan.M.loaded_segments (0x5cc48 : word) = Some W_5cbf0.
Proof. vm_refl. Qed.
Lemma D_5cbf0 : decode_any W_5cbf0 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbf4 : bv 32 := 0x0009c517.
Lemma F_5cbf4 : fetch_word Ubsan.M.loaded_segments (0x5cc4c : word) = Some W_5cbf4.
Proof. vm_refl. Qed.
Lemma D_5cbf4 : decode_any W_5cbf4 = Some (Auipc 10 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbf8 : bv 32 := 0x4a453503.
Lemma F_5cbf8 : fetch_word Ubsan.M.loaded_segments (0x5cc50 : word) = Some W_5cbf8.
Proof. vm_refl. Qed.
Lemma D_5cbf8 : decode_any W_5cbf8 = Some (Load SZ8 true 10 10 1188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cbfc : bv 32 := 0x00050e63.
Lemma F_5cbfc : fetch_word Ubsan.M.loaded_segments (0x5cc54 : word) = Some W_5cbfc.
Proof. vm_refl. Qed.
Lemma D_5cbfc : decode_any W_5cbfc = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc00 : bv 32 := 0x0040006f.
Lemma F_5cc00 : fetch_word Ubsan.M.loaded_segments (0x5cc58 : word) = Some W_5cc00.
Proof. vm_refl. Qed.
Lemma D_5cc00 : decode_any W_5cc00 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc04 : bv 32 := 0x0009d517.
Lemma F_5cc04 : fetch_word Ubsan.M.loaded_segments (0x5cc5c : word) = Some W_5cc04.
Proof. vm_refl. Qed.
Lemma D_5cc04 : decode_any W_5cc04 = Some (Auipc 10 157, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc08 : bv 32 := 0x67c50513.
Lemma F_5cc08 : fetch_word Ubsan.M.loaded_segments (0x5cc60 : word) = Some W_5cc08.
Proof. vm_refl. Qed.
Lemma D_5cc08 : decode_any W_5cc08 = Some (OpImm ALU_ADD 10 10 1660, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc0c : bv 32 := 0x00053503.
Lemma F_5cc0c : fetch_word Ubsan.M.loaded_segments (0x5cc64 : word) = Some W_5cc0c.
Proof. vm_refl. Qed.
Lemma D_5cc0c : decode_any W_5cc0c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc10 : bv 32 := 0x4fc850ef.
Lemma F_5cc10 : fetch_word Ubsan.M.loaded_segments (0x5cc68 : word) = Some W_5cc10.
Proof. vm_refl. Qed.
Lemma D_5cc10 : decode_any W_5cc10 = Some (Jal 1 546044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc14 : bv 32 := 0x0040006f.
Lemma F_5cc14 : fetch_word Ubsan.M.loaded_segments (0x5cc6c : word) = Some W_5cc14.
Proof. vm_refl. Qed.
Lemma D_5cc14 : decode_any W_5cc14 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc18 : bv 32 := 0x0009c517.
Lemma F_5cc18 : fetch_word Ubsan.M.loaded_segments (0x5cc70 : word) = Some W_5cc18.
Proof. vm_refl. Qed.
Lemma D_5cc18 : decode_any W_5cc18 = Some (Auipc 10 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc1c : bv 32 := 0x48853503.
Lemma F_5cc1c : fetch_word Ubsan.M.loaded_segments (0x5cc74 : word) = Some W_5cc1c.
Proof. vm_refl. Qed.
Lemma D_5cc1c : decode_any W_5cc1c = Some (Load SZ8 true 10 10 1160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc20 : bv 32 := 0x00050c63.
Lemma F_5cc20 : fetch_word Ubsan.M.loaded_segments (0x5cc78 : word) = Some W_5cc20.
Proof. vm_refl. Qed.
Lemma D_5cc20 : decode_any W_5cc20 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc24 : bv 32 := 0x0040006f.
Lemma F_5cc24 : fetch_word Ubsan.M.loaded_segments (0x5cc7c : word) = Some W_5cc24.
Proof. vm_refl. Qed.
Lemma D_5cc24 : decode_any W_5cc24 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc28 : bv 32 := 0xffff3517.
Lemma F_5cc28 : fetch_word Ubsan.M.loaded_segments (0x5cc80 : word) = Some W_5cc28.
Proof. vm_refl. Qed.
Lemma D_5cc28 : decode_any W_5cc28 = Some (Auipc 10 1048563, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc2c : bv 32 := 0x2f850513.
Lemma F_5cc2c : fetch_word Ubsan.M.loaded_segments (0x5cc84 : word) = Some W_5cc2c.
Proof. vm_refl. Qed.
Lemma D_5cc2c : decode_any W_5cc2c = Some (OpImm ALU_ADD 10 10 760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc30 : bv 32 := 0x000000ef.
Lemma F_5cc30 : fetch_word Ubsan.M.loaded_segments (0x5cc88 : word) = Some W_5cc30.
Proof. vm_refl. Qed.
Lemma D_5cc30 : decode_any W_5cc30 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc34 : bv 32 := 0x0040006f.
Lemma F_5cc34 : fetch_word Ubsan.M.loaded_segments (0x5cc8c : word) = Some W_5cc34.
Proof. vm_refl. Qed.
Lemma D_5cc34 : decode_any W_5cc34 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc38 : bv 32 := 0x00813083.
Lemma F_5cc38 : fetch_word Ubsan.M.loaded_segments (0x5cc90 : word) = Some W_5cc38.
Proof. vm_refl. Qed.
Lemma D_5cc38 : decode_any W_5cc38 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc3c : bv 32 := 0x00013403.
Lemma F_5cc3c : fetch_word Ubsan.M.loaded_segments (0x5cc94 : word) = Some W_5cc3c.
Proof. vm_refl. Qed.
Lemma D_5cc3c : decode_any W_5cc3c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc40 : bv 32 := 0x01010113.
Lemma F_5cc40 : fetch_word Ubsan.M.loaded_segments (0x5cc98 : word) = Some W_5cc40.
Proof. vm_refl. Qed.
Lemma D_5cc40 : decode_any W_5cc40 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc44 : bv 32 := 0x00008067.
Lemma F_5cc44 : fetch_word Ubsan.M.loaded_segments (0x5cc9c : word) = Some W_5cc44.
Proof. vm_refl. Qed.
Lemma D_5cc44 : decode_any W_5cc44 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d070 : bv 32 := 0x000ad517.
Lemma F_5d070 : fetch_word Ubsan.M.loaded_segments (0x5d0c8 : word) = Some W_5d070.
Proof. vm_refl. Qed.
Lemma D_5d070 : decode_any W_5d070 = Some (Auipc 10 173, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d074 : bv 32 := 0x4dc54503.
Lemma F_5d074 : fetch_word Ubsan.M.loaded_segments (0x5d0cc : word) = Some W_5d074.
Proof. vm_refl. Qed.
Lemma D_5d074 : decode_any W_5d074 = Some (Load SZ1 false 10 10 1244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d078 : bv 32 := 0x00051463.
Lemma F_5d078 : fetch_word Ubsan.M.loaded_segments (0x5d0d0 : word) = Some W_5d078.
Proof. vm_refl. Qed.
Lemma D_5d078 : decode_any W_5d078 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d07c : bv 32 := 0x00008067.
Lemma F_5d07c : fetch_word Ubsan.M.loaded_segments (0x5d0d4 : word) = Some W_5d07c.
Proof. vm_refl. Qed.
Lemma D_5d07c : decode_any W_5d07c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d080 : bv 32 := 0xff010113.
Lemma F_5d080 : fetch_word Ubsan.M.loaded_segments (0x5d0d8 : word) = Some W_5d080.
Proof. vm_refl. Qed.
Lemma D_5d080 : decode_any W_5d080 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d084 : bv 32 := 0x00113423.
Lemma F_5d084 : fetch_word Ubsan.M.loaded_segments (0x5d0dc : word) = Some W_5d084.
Proof. vm_refl. Qed.
Lemma D_5d084 : decode_any W_5d084 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d088 : bv 32 := 0x0009c517.
Lemma F_5d088 : fetch_word Ubsan.M.loaded_segments (0x5d0e0 : word) = Some W_5d088.
Proof. vm_refl. Qed.
Lemma D_5d088 : decode_any W_5d088 = Some (Auipc 10 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d08c : bv 32 := 0x03853503.
Lemma F_5d08c : fetch_word Ubsan.M.loaded_segments (0x5d0e4 : word) = Some W_5d08c.
Proof. vm_refl. Qed.
Lemma D_5d08c : decode_any W_5d08c = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d090 : bv 32 := 0x00053503.
Lemma F_5d090 : fetch_word Ubsan.M.loaded_segments (0x5d0e8 : word) = Some W_5d090.
Proof. vm_refl. Qed.
Lemma D_5d090 : decode_any W_5d090 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d094 : bv 32 := 0x445880ef.
Lemma F_5d094 : fetch_word Ubsan.M.loaded_segments (0x5d0ec : word) = Some W_5d094.
Proof. vm_refl. Qed.
Lemma D_5d094 : decode_any W_5d094 = Some (Jal 1 560196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d098 : bv 32 := 0x04d00513.
Lemma F_5d098 : fetch_word Ubsan.M.loaded_segments (0x5d0f0 : word) = Some W_5d098.
Proof. vm_refl. Qed.
Lemma D_5d098 : decode_any W_5d098 = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d09c : bv 32 := 0x279970ef.
Lemma F_5d09c : fetch_word Ubsan.M.loaded_segments (0x5d0f4 : word) = Some W_5d09c.
Proof. vm_refl. Qed.
Lemma D_5d09c : decode_any W_5d09c = Some (Jal 1 621176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2054 : bv 32 := 0xfd010113.
Lemma F_e2054 : fetch_word Ubsan.M.loaded_segments (0xe209c : word) = Some W_e2054.
Proof. vm_refl. Qed.
Lemma D_e2054 : decode_any W_e2054 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2058 : bv 32 := 0x02113423.
Lemma F_e2058 : fetch_word Ubsan.M.loaded_segments (0xe20a0 : word) = Some W_e2058.
Proof. vm_refl. Qed.
Lemma D_e2058 : decode_any W_e2058 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e205c : bv 32 := 0x02813023.
Lemma F_e205c : fetch_word Ubsan.M.loaded_segments (0xe20a4 : word) = Some W_e205c.
Proof. vm_refl. Qed.
Lemma D_e205c : decode_any W_e205c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2060 : bv 32 := 0x00913c23.
Lemma F_e2060 : fetch_word Ubsan.M.loaded_segments (0xe20a8 : word) = Some W_e2060.
Proof. vm_refl. Qed.
Lemma D_e2060 : decode_any W_e2060 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2064 : bv 32 := 0x01213823.
Lemma F_e2064 : fetch_word Ubsan.M.loaded_segments (0xe20ac : word) = Some W_e2064.
Proof. vm_refl. Qed.
Lemma D_e2064 : decode_any W_e2064 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2068 : bv 32 := 0x01313423.
Lemma F_e2068 : fetch_word Ubsan.M.loaded_segments (0xe20b0 : word) = Some W_e2068.
Proof. vm_refl. Qed.
Lemma D_e2068 : decode_any W_e2068 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e206c : bv 32 := 0x00048517.
Lemma F_e206c : fetch_word Ubsan.M.loaded_segments (0xe20b4 : word) = Some W_e206c.
Proof. vm_refl. Qed.
Lemma D_e206c : decode_any W_e206c = Some (Auipc 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2070 : bv 32 := 0x7ec50913.
Lemma F_e2070 : fetch_word Ubsan.M.loaded_segments (0xe20b8 : word) = Some W_e2070.
Proof. vm_refl. Qed.
Lemma D_e2070 : decode_any W_e2070 = Some (OpImm ALU_ADD 18 10 2028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2074 : bv 32 := 0x00490413.
Lemma F_e2074 : fetch_word Ubsan.M.loaded_segments (0xe20bc : word) = Some W_e2074.
Proof. vm_refl. Qed.
Lemma D_e2074 : decode_any W_e2074 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2078 : bv 32 := 0x00040513.
Lemma F_e2078 : fetch_word Ubsan.M.loaded_segments (0xe20c0 : word) = Some W_e2078.
Proof. vm_refl. Qed.
Lemma D_e2078 : decode_any W_e2078 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e207c : bv 32 := 0x5480f0ef.
Lemma F_e207c : fetch_word Ubsan.M.loaded_segments (0xe20c4 : word) = Some W_e207c.
Proof. vm_refl. Qed.
Lemma D_e207c : decode_any W_e207c = Some (Jal 1 62792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2080 : bv 32 := 0x01093503.
Lemma F_e2080 : fetch_word Ubsan.M.loaded_segments (0xe20c8 : word) = Some W_e2080.
Proof. vm_refl. Qed.
Lemma D_e2080 : decode_any W_e2080 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2084 : bv 32 := 0x06050863.
Lemma F_e2084 : fetch_word Ubsan.M.loaded_segments (0xe20cc : word) = Some W_e2084.
Proof. vm_refl. Qed.
Lemma D_e2084 : decode_any W_e2084 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2088 : bv 32 := 0x00892583.
Lemma F_e2088 : fetch_word Ubsan.M.loaded_segments (0xe20d0 : word) = Some W_e2088.
Proof. vm_refl. Qed.
Lemma D_e2088 : decode_any W_e2088 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e208c : bv 32 := 0x0180006f.
Lemma F_e208c : fetch_word Ubsan.M.loaded_segments (0xe20d4 : word) = Some W_e208c.
Proof. vm_refl. Qed.
Lemma D_e208c : decode_any W_e208c = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2090 : bv 32 := 0x00053503.
Lemma F_e2090 : fetch_word Ubsan.M.loaded_segments (0xe20d8 : word) = Some W_e2090.
Proof. vm_refl. Qed.
Lemma D_e2090 : decode_any W_e2090 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2094 : bv 32 := 0x02000593.
Lemma F_e2094 : fetch_word Ubsan.M.loaded_segments (0xe20dc : word) = Some W_e2094.
Proof. vm_refl. Qed.
Lemma D_e2094 : decode_any W_e2094 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2098 : bv 32 := 0x00b92423.
Lemma F_e2098 : fetch_word Ubsan.M.loaded_segments (0xe20e0 : word) = Some W_e2098.
Proof. vm_refl. Qed.
Lemma D_e2098 : decode_any W_e2098 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e209c : bv 32 := 0x00a93823.
Lemma F_e209c : fetch_word Ubsan.M.loaded_segments (0xe20e4 : word) = Some W_e209c.
Proof. vm_refl. Qed.
Lemma D_e209c : decode_any W_e209c = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20a0 : bv 32 := 0x04050a63.
Lemma F_e20a0 : fetch_word Ubsan.M.loaded_segments (0xe20e8 : word) = Some W_e20a0.
Proof. vm_refl. Qed.
Lemma D_e20a0 : decode_any W_e20a0 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20a4 : bv 32 := 0xfff5861b.
Lemma F_e20a4 : fetch_word Ubsan.M.loaded_segments (0xe20ec : word) = Some W_e20a4.
Proof. vm_refl. Qed.
Lemma D_e20a4 : decode_any W_e20a4 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20a8 : bv 32 := 0x00c92423.
Lemma F_e20a8 : fetch_word Ubsan.M.loaded_segments (0xe20f0 : word) = Some W_e20a8.
Proof. vm_refl. Qed.
Lemma D_e20a8 : decode_any W_e20a8 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20ac : bv 32 := 0xfeb052e3.
Lemma F_e20ac : fetch_word Ubsan.M.loaded_segments (0xe20f4 : word) = Some W_e20ac.
Proof. vm_refl. Qed.
Lemma D_e20ac : decode_any W_e20ac = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20b0 : bv 32 := 0x01093503.
Lemma F_e20b0 : fetch_word Ubsan.M.loaded_segments (0xe20f8 : word) = Some W_e20b0.
Proof. vm_refl. Qed.
Lemma D_e20b0 : decode_any W_e20b0 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20b4 : bv 32 := 0x00361613.
Lemma F_e20b4 : fetch_word Ubsan.M.loaded_segments (0xe20fc : word) = Some W_e20b4.
Proof. vm_refl. Qed.
Lemma D_e20b4 : decode_any W_e20b4 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20b8 : bv 32 := 0x00c50533.
Lemma F_e20b8 : fetch_word Ubsan.M.loaded_segments (0xe2100 : word) = Some W_e20b8.
Proof. vm_refl. Qed.
Lemma D_e20b8 : decode_any W_e20b8 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20bc : bv 32 := 0x00853983.
Lemma F_e20bc : fetch_word Ubsan.M.loaded_segments (0xe2104 : word) = Some W_e20bc.
Proof. vm_refl. Qed.
Lemma D_e20bc : decode_any W_e20bc = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20c0 : bv 32 := 0x10853483.
Lemma F_e20c0 : fetch_word Ubsan.M.loaded_segments (0xe2108 : word) = Some W_e20c0.
Proof. vm_refl. Qed.
Lemma D_e20c0 : decode_any W_e20c0 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20c4 : bv 32 := 0x00040513.
Lemma F_e20c4 : fetch_word Ubsan.M.loaded_segments (0xe210c : word) = Some W_e20c4.
Proof. vm_refl. Qed.
Lemma D_e20c4 : decode_any W_e20c4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20c8 : bv 32 := 0x7840f0ef.
Lemma F_e20c8 : fetch_word Ubsan.M.loaded_segments (0xe2110 : word) = Some W_e20c8.
Proof. vm_refl. Qed.
Lemma D_e20c8 : decode_any W_e20c8 = Some (Jal 1 63364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20cc : bv 32 := 0x00048513.
Lemma F_e20cc : fetch_word Ubsan.M.loaded_segments (0xe2114 : word) = Some W_e20cc.
Proof. vm_refl. Qed.
Lemma D_e20cc : decode_any W_e20cc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20d0 : bv 32 := 0x000980e7.
Lemma F_e20d0 : fetch_word Ubsan.M.loaded_segments (0xe2118 : word) = Some W_e20d0.
Proof. vm_refl. Qed.
Lemma D_e20d0 : decode_any W_e20d0 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20d4 : bv 32 := 0x00040513.
Lemma F_e20d4 : fetch_word Ubsan.M.loaded_segments (0xe211c : word) = Some W_e20d4.
Proof. vm_refl. Qed.
Lemma D_e20d4 : decode_any W_e20d4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20d8 : bv 32 := 0x4ec0f0ef.
Lemma F_e20d8 : fetch_word Ubsan.M.loaded_segments (0xe2120 : word) = Some W_e20d8.
Proof. vm_refl. Qed.
Lemma D_e20d8 : decode_any W_e20d8 = Some (Jal 1 62700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20dc : bv 32 := 0x00892503.
Lemma F_e20dc : fetch_word Ubsan.M.loaded_segments (0xe2124 : word) = Some W_e20dc.
Proof. vm_refl. Qed.
Lemma D_e20dc : decode_any W_e20dc = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20e0 : bv 32 := 0xfff5061b.
Lemma F_e20e0 : fetch_word Ubsan.M.loaded_segments (0xe2128 : word) = Some W_e20e0.
Proof. vm_refl. Qed.
Lemma D_e20e0 : decode_any W_e20e0 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20e4 : bv 32 := 0x00c92423.
Lemma F_e20e4 : fetch_word Ubsan.M.loaded_segments (0xe212c : word) = Some W_e20e4.
Proof. vm_refl. Qed.
Lemma D_e20e4 : decode_any W_e20e4 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20e8 : bv 32 := 0xfca044e3.
Lemma F_e20e8 : fetch_word Ubsan.M.loaded_segments (0xe2130 : word) = Some W_e20e8.
Proof. vm_refl. Qed.
Lemma D_e20e8 : decode_any W_e20e8 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20ec : bv 32 := 0x01093503.
Lemma F_e20ec : fetch_word Ubsan.M.loaded_segments (0xe2134 : word) = Some W_e20ec.
Proof. vm_refl. Qed.
Lemma D_e20ec : decode_any W_e20ec = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20f0 : bv 32 := 0xfa1ff06f.
Lemma F_e20f0 : fetch_word Ubsan.M.loaded_segments (0xe2138 : word) = Some W_e20f0.
Proof. vm_refl. Qed.
Lemma D_e20f0 : decode_any W_e20f0 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20f4 : bv 32 := 0x00100513.
Lemma F_e20f4 : fetch_word Ubsan.M.loaded_segments (0xe213c : word) = Some W_e20f4.
Proof. vm_refl. Qed.
Lemma D_e20f4 : decode_any W_e20f4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20f8 : bv 32 := 0x00a90023.
Lemma F_e20f8 : fetch_word Ubsan.M.loaded_segments (0xe2140 : word) = Some W_e20f8.
Proof. vm_refl. Qed.
Lemma D_e20f8 : decode_any W_e20f8 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e20fc : bv 32 := 0x00040513.
Lemma F_e20fc : fetch_word Ubsan.M.loaded_segments (0xe2144 : word) = Some W_e20fc.
Proof. vm_refl. Qed.
Lemma D_e20fc : decode_any W_e20fc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2100 : bv 32 := 0x02813083.
Lemma F_e2100 : fetch_word Ubsan.M.loaded_segments (0xe2148 : word) = Some W_e2100.
Proof. vm_refl. Qed.
Lemma D_e2100 : decode_any W_e2100 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2104 : bv 32 := 0x02013403.
Lemma F_e2104 : fetch_word Ubsan.M.loaded_segments (0xe214c : word) = Some W_e2104.
Proof. vm_refl. Qed.
Lemma D_e2104 : decode_any W_e2104 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2108 : bv 32 := 0x01813483.
Lemma F_e2108 : fetch_word Ubsan.M.loaded_segments (0xe2150 : word) = Some W_e2108.
Proof. vm_refl. Qed.
Lemma D_e2108 : decode_any W_e2108 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e210c : bv 32 := 0x01013903.
Lemma F_e210c : fetch_word Ubsan.M.loaded_segments (0xe2154 : word) = Some W_e210c.
Proof. vm_refl. Qed.
Lemma D_e210c : decode_any W_e210c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2110 : bv 32 := 0x00813983.
Lemma F_e2110 : fetch_word Ubsan.M.loaded_segments (0xe2158 : word) = Some W_e2110.
Proof. vm_refl. Qed.
Lemma D_e2110 : decode_any W_e2110 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2114 : bv 32 := 0x03010113.
Lemma F_e2114 : fetch_word Ubsan.M.loaded_segments (0xe215c : word) = Some W_e2114.
Proof. vm_refl. Qed.
Lemma D_e2114 : decode_any W_e2114 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2118 : bv 32 := 0x7340f06f.
Lemma F_e2118 : fetch_word Ubsan.M.loaded_segments (0xe2160 : word) = Some W_e2118.
Proof. vm_refl. Qed.
Lemma D_e2118 : decode_any W_e2118 = Some (Jal 0 63284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e211c : bv 32 := 0x00008067.
Lemma F_e211c : fetch_word Ubsan.M.loaded_segments (0xe2164 : word) = Some W_e211c.
Proof. vm_refl. Qed.
Lemma D_e211c : decode_any W_e211c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2120 : bv 32 := 0xfd010113.
Lemma F_e2120 : fetch_word Ubsan.M.loaded_segments (0xe2168 : word) = Some W_e2120.
Proof. vm_refl. Qed.
Lemma D_e2120 : decode_any W_e2120 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2124 : bv 32 := 0x02113423.
Lemma F_e2124 : fetch_word Ubsan.M.loaded_segments (0xe216c : word) = Some W_e2124.
Proof. vm_refl. Qed.
Lemma D_e2124 : decode_any W_e2124 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2128 : bv 32 := 0x02813023.
Lemma F_e2128 : fetch_word Ubsan.M.loaded_segments (0xe2170 : word) = Some W_e2128.
Proof. vm_refl. Qed.
Lemma D_e2128 : decode_any W_e2128 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e212c : bv 32 := 0x00913c23.
Lemma F_e212c : fetch_word Ubsan.M.loaded_segments (0xe2174 : word) = Some W_e212c.
Proof. vm_refl. Qed.
Lemma D_e212c : decode_any W_e212c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2130 : bv 32 := 0x01213823.
Lemma F_e2130 : fetch_word Ubsan.M.loaded_segments (0xe2178 : word) = Some W_e2130.
Proof. vm_refl. Qed.
Lemma D_e2130 : decode_any W_e2130 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2134 : bv 32 := 0x01313423.
Lemma F_e2134 : fetch_word Ubsan.M.loaded_segments (0xe217c : word) = Some W_e2134.
Proof. vm_refl. Qed.
Lemma D_e2134 : decode_any W_e2134 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2138 : bv 32 := 0x00050493.
Lemma F_e2138 : fetch_word Ubsan.M.loaded_segments (0xe2180 : word) = Some W_e2138.
Proof. vm_refl. Qed.
Lemma D_e2138 : decode_any W_e2138 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e213c : bv 32 := 0x00048517.
Lemma F_e213c : fetch_word Ubsan.M.loaded_segments (0xe2184 : word) = Some W_e213c.
Proof. vm_refl. Qed.
Lemma D_e213c : decode_any W_e213c = Some (Auipc 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2140 : bv 32 := 0x71c50993.
Lemma F_e2140 : fetch_word Ubsan.M.loaded_segments (0xe2188 : word) = Some W_e2140.
Proof. vm_refl. Qed.
Lemma D_e2140 : decode_any W_e2140 = Some (OpImm ALU_ADD 19 10 1820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2144 : bv 32 := 0x00498413.
Lemma F_e2144 : fetch_word Ubsan.M.loaded_segments (0xe218c : word) = Some W_e2144.
Proof. vm_refl. Qed.
Lemma D_e2144 : decode_any W_e2144 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2148 : bv 32 := 0x00040513.
Lemma F_e2148 : fetch_word Ubsan.M.loaded_segments (0xe2190 : word) = Some W_e2148.
Proof. vm_refl. Qed.
Lemma D_e2148 : decode_any W_e2148 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e214c : bv 32 := 0x4780f0ef.
Lemma F_e214c : fetch_word Ubsan.M.loaded_segments (0xe2194 : word) = Some W_e214c.
Proof. vm_refl. Qed.
Lemma D_e214c : decode_any W_e214c = Some (Jal 1 62584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2150 : bv 32 := 0x0009c503.
Lemma F_e2150 : fetch_word Ubsan.M.loaded_segments (0xe2198 : word) = Some W_e2150.
Proof. vm_refl. Qed.
Lemma D_e2150 : decode_any W_e2150 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2154 : bv 32 := 0xfff00913.
Lemma F_e2154 : fetch_word Ubsan.M.loaded_segments (0xe219c : word) = Some W_e2154.
Proof. vm_refl. Qed.
Lemma D_e2154 : decode_any W_e2154 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2158 : bv 32 := 0x06051263.
Lemma F_e2158 : fetch_word Ubsan.M.loaded_segments (0xe21a0 : word) = Some W_e2158.
Proof. vm_refl. Qed.
Lemma D_e2158 : decode_any W_e2158 = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e215c : bv 32 := 0x0109b503.
Lemma F_e215c : fetch_word Ubsan.M.loaded_segments (0xe21a4 : word) = Some W_e215c.
Proof. vm_refl. Qed.
Lemma D_e215c : decode_any W_e215c = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2160 : bv 32 := 0x00051663.
Lemma F_e2160 : fetch_word Ubsan.M.loaded_segments (0xe21a8 : word) = Some W_e2160.
Proof. vm_refl. Qed.
Lemma D_e2160 : decode_any W_e2160 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2164 : bv 32 := 0x01898513.
Lemma F_e2164 : fetch_word Ubsan.M.loaded_segments (0xe21ac : word) = Some W_e2164.
Proof. vm_refl. Qed.
Lemma D_e2164 : decode_any W_e2164 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2168 : bv 32 := 0x00a9b823.
Lemma F_e2168 : fetch_word Ubsan.M.loaded_segments (0xe21b0 : word) = Some W_e2168.
Proof. vm_refl. Qed.
Lemma D_e2168 : decode_any W_e2168 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e216c : bv 32 := 0x0089a583.
Lemma F_e216c : fetch_word Ubsan.M.loaded_segments (0xe21b4 : word) = Some W_e216c.
Proof. vm_refl. Qed.
Lemma D_e216c : decode_any W_e216c = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2170 : bv 32 := 0x02000613.
Lemma F_e2170 : fetch_word Ubsan.M.loaded_segments (0xe21b8 : word) = Some W_e2170.
Proof. vm_refl. Qed.
Lemma D_e2170 : decode_any W_e2170 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2174 : bv 32 := 0x02c59263.
Lemma F_e2174 : fetch_word Ubsan.M.loaded_segments (0xe21bc : word) = Some W_e2174.
Proof. vm_refl. Qed.
Lemma D_e2174 : decode_any W_e2174 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2178 : bv 32 := 0x20800513.
Lemma F_e2178 : fetch_word Ubsan.M.loaded_segments (0xe21c0 : word) = Some W_e2178.
Proof. vm_refl. Qed.
Lemma D_e2178 : decode_any W_e2178 = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e217c : bv 32 := 0x00100593.
Lemma F_e217c : fetch_word Ubsan.M.loaded_segments (0xe21c4 : word) = Some W_e217c.
Proof. vm_refl. Qed.
Lemma D_e217c : decode_any W_e217c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2180 : bv 32 := 0x3f4000ef.
Lemma F_e2180 : fetch_word Ubsan.M.loaded_segments (0xe21c8 : word) = Some W_e2180.
Proof. vm_refl. Qed.
Lemma D_e2180 : decode_any W_e2180 = Some (Jal 1 1012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2184 : bv 32 := 0x02050c63.
Lemma F_e2184 : fetch_word Ubsan.M.loaded_segments (0xe21cc : word) = Some W_e2184.
Proof. vm_refl. Qed.
Lemma D_e2184 : decode_any W_e2184 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2188 : bv 32 := 0x00000593.
Lemma F_e2188 : fetch_word Ubsan.M.loaded_segments (0xe21d0 : word) = Some W_e2188.
Proof. vm_refl. Qed.
Lemma D_e2188 : decode_any W_e2188 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e218c : bv 32 := 0x0109b603.
Lemma F_e218c : fetch_word Ubsan.M.loaded_segments (0xe21d4 : word) = Some W_e218c.
Proof. vm_refl. Qed.
Lemma D_e218c : decode_any W_e218c = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2190 : bv 32 := 0x00c53023.
Lemma F_e2190 : fetch_word Ubsan.M.loaded_segments (0xe21d8 : word) = Some W_e2190.
Proof. vm_refl. Qed.
Lemma D_e2190 : decode_any W_e2190 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2194 : bv 32 := 0x00a9b823.
Lemma F_e2194 : fetch_word Ubsan.M.loaded_segments (0xe21dc : word) = Some W_e2194.
Proof. vm_refl. Qed.
Lemma D_e2194 : decode_any W_e2194 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2198 : bv 32 := 0x00000913.
Lemma F_e2198 : fetch_word Ubsan.M.loaded_segments (0xe21e0 : word) = Some W_e2198.
Proof. vm_refl. Qed.
Lemma D_e2198 : decode_any W_e2198 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e219c : bv 32 := 0x00359613.
Lemma F_e219c : fetch_word Ubsan.M.loaded_segments (0xe21e4 : word) = Some W_e219c.
Proof. vm_refl. Qed.
Lemma D_e219c : decode_any W_e219c = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21a0 : bv 32 := 0x00c50533.
Lemma F_e21a0 : fetch_word Ubsan.M.loaded_segments (0xe21e8 : word) = Some W_e21a0.
Proof. vm_refl. Qed.
Lemma D_e21a0 : decode_any W_e21a0 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21a4 : bv 32 := 0x00000617.
Lemma F_e21a4 : fetch_word Ubsan.M.loaded_segments (0xe21ec : word) = Some W_e21a4.
Proof. vm_refl. Qed.
Lemma D_e21a4 : decode_any W_e21a4 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21a8 : bv 32 := 0x00158593.
Lemma F_e21a8 : fetch_word Ubsan.M.loaded_segments (0xe21f0 : word) = Some W_e21a8.
Proof. vm_refl. Qed.
Lemma D_e21a8 : decode_any W_e21a8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21ac : bv 32 := 0x04060613.
Lemma F_e21ac : fetch_word Ubsan.M.loaded_segments (0xe21f4 : word) = Some W_e21ac.
Proof. vm_refl. Qed.
Lemma D_e21ac : decode_any W_e21ac = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21b0 : bv 32 := 0x00c53423.
Lemma F_e21b0 : fetch_word Ubsan.M.loaded_segments (0xe21f8 : word) = Some W_e21b0.
Proof. vm_refl. Qed.
Lemma D_e21b0 : decode_any W_e21b0 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21b4 : bv 32 := 0x10953423.
Lemma F_e21b4 : fetch_word Ubsan.M.loaded_segments (0xe21fc : word) = Some W_e21b4.
Proof. vm_refl. Qed.
Lemma D_e21b4 : decode_any W_e21b4 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21b8 : bv 32 := 0x00b9a423.
Lemma F_e21b8 : fetch_word Ubsan.M.loaded_segments (0xe2200 : word) = Some W_e21b8.
Proof. vm_refl. Qed.
Lemma D_e21b8 : decode_any W_e21b8 = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21bc : bv 32 := 0x00040513.
Lemma F_e21bc : fetch_word Ubsan.M.loaded_segments (0xe2204 : word) = Some W_e21bc.
Proof. vm_refl. Qed.
Lemma D_e21bc : decode_any W_e21bc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21c0 : bv 32 := 0x68c0f0ef.
Lemma F_e21c0 : fetch_word Ubsan.M.loaded_segments (0xe2208 : word) = Some W_e21c0.
Proof. vm_refl. Qed.
Lemma D_e21c0 : decode_any W_e21c0 = Some (Jal 1 63116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21c4 : bv 32 := 0x00090513.
Lemma F_e21c4 : fetch_word Ubsan.M.loaded_segments (0xe220c : word) = Some W_e21c4.
Proof. vm_refl. Qed.
Lemma D_e21c4 : decode_any W_e21c4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21c8 : bv 32 := 0x02813083.
Lemma F_e21c8 : fetch_word Ubsan.M.loaded_segments (0xe2210 : word) = Some W_e21c8.
Proof. vm_refl. Qed.
Lemma D_e21c8 : decode_any W_e21c8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21cc : bv 32 := 0x02013403.
Lemma F_e21cc : fetch_word Ubsan.M.loaded_segments (0xe2214 : word) = Some W_e21cc.
Proof. vm_refl. Qed.
Lemma D_e21cc : decode_any W_e21cc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21d0 : bv 32 := 0x01813483.
Lemma F_e21d0 : fetch_word Ubsan.M.loaded_segments (0xe2218 : word) = Some W_e21d0.
Proof. vm_refl. Qed.
Lemma D_e21d0 : decode_any W_e21d0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21d4 : bv 32 := 0x01013903.
Lemma F_e21d4 : fetch_word Ubsan.M.loaded_segments (0xe221c : word) = Some W_e21d4.
Proof. vm_refl. Qed.
Lemma D_e21d4 : decode_any W_e21d4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21d8 : bv 32 := 0x00813983.
Lemma F_e21d8 : fetch_word Ubsan.M.loaded_segments (0xe2220 : word) = Some W_e21d8.
Proof. vm_refl. Qed.
Lemma D_e21d8 : decode_any W_e21d8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21dc : bv 32 := 0x03010113.
Lemma F_e21dc : fetch_word Ubsan.M.loaded_segments (0xe2224 : word) = Some W_e21dc.
Proof. vm_refl. Qed.
Lemma D_e21dc : decode_any W_e21dc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21e0 : bv 32 := 0x00008067.
Lemma F_e21e0 : fetch_word Ubsan.M.loaded_segments (0xe2228 : word) = Some W_e21e0.
Proof. vm_refl. Qed.
Lemma D_e21e0 : decode_any W_e21e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21e4 : bv 32 := 0x00050067.
Lemma F_e21e4 : fetch_word Ubsan.M.loaded_segments (0xe222c : word) = Some W_e21e4.
Proof. vm_refl. Qed.
Lemma D_e21e4 : decode_any W_e21e4 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21e8 : bv 32 := 0x00008067.
Lemma F_e21e8 : fetch_word Ubsan.M.loaded_segments (0xe2230 : word) = Some W_e21e8.
Proof. vm_refl. Qed.
Lemma D_e21e8 : decode_any W_e21e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21ec : bv 32 := 0xfe010113.
Lemma F_e21ec : fetch_word Ubsan.M.loaded_segments (0xe2234 : word) = Some W_e21ec.
Proof. vm_refl. Qed.
Lemma D_e21ec : decode_any W_e21ec = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21f0 : bv 32 := 0x00113c23.
Lemma F_e21f0 : fetch_word Ubsan.M.loaded_segments (0xe2238 : word) = Some W_e21f0.
Proof. vm_refl. Qed.
Lemma D_e21f0 : decode_any W_e21f0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21f4 : bv 32 := 0x00813823.
Lemma F_e21f4 : fetch_word Ubsan.M.loaded_segments (0xe223c : word) = Some W_e21f4.
Proof. vm_refl. Qed.
Lemma D_e21f4 : decode_any W_e21f4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21f8 : bv 32 := 0x00913423.
Lemma F_e21f8 : fetch_word Ubsan.M.loaded_segments (0xe2240 : word) = Some W_e21f8.
Proof. vm_refl. Qed.
Lemma D_e21f8 : decode_any W_e21f8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e21fc : bv 32 := 0x00017517.
Lemma F_e21fc : fetch_word Ubsan.M.loaded_segments (0xe2244 : word) = Some W_e21fc.
Proof. vm_refl. Qed.
Lemma D_e21fc : decode_any W_e21fc = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2200 : bv 32 := 0x00017597.
Lemma F_e2200 : fetch_word Ubsan.M.loaded_segments (0xe2248 : word) = Some W_e2200.
Proof. vm_refl. Qed.
Lemma D_e2200 : decode_any W_e2200 = Some (Auipc 11 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2204 : bv 32 := 0x06c53503.
Lemma F_e2204 : fetch_word Ubsan.M.loaded_segments (0xe224c : word) = Some W_e2204.
Proof. vm_refl. Qed.
Lemma D_e2204 : decode_any W_e2204 = Some (Load SZ8 true 10 10 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2208 : bv 32 := 0x0705b403.
Lemma F_e2208 : fetch_word Ubsan.M.loaded_segments (0xe2250 : word) = Some W_e2208.
Proof. vm_refl. Qed.
Lemma D_e2208 : decode_any W_e2208 = Some (Load SZ8 true 8 11 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e220c : bv 32 := 0x00a47c63.
Lemma F_e220c : fetch_word Ubsan.M.loaded_segments (0xe2254 : word) = Some W_e220c.
Proof. vm_refl. Qed.
Lemma D_e220c : decode_any W_e220c = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2210 : bv 32 := 0xff853583.
Lemma F_e2210 : fetch_word Ubsan.M.loaded_segments (0xe2258 : word) = Some W_e2210.
Proof. vm_refl. Qed.
Lemma D_e2210 : decode_any W_e2210 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2214 : bv 32 := 0xff850493.
Lemma F_e2214 : fetch_word Ubsan.M.loaded_segments (0xe225c : word) = Some W_e2214.
Proof. vm_refl. Qed.
Lemma D_e2214 : decode_any W_e2214 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2218 : bv 32 := 0x000580e7.
Lemma F_e2218 : fetch_word Ubsan.M.loaded_segments (0xe2260 : word) = Some W_e2218.
Proof. vm_refl. Qed.
Lemma D_e2218 : decode_any W_e2218 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e221c : bv 32 := 0x00048513.
Lemma F_e221c : fetch_word Ubsan.M.loaded_segments (0xe2264 : word) = Some W_e221c.
Proof. vm_refl. Qed.
Lemma D_e221c : decode_any W_e221c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2220 : bv 32 := 0xfe9468e3.
Lemma F_e2220 : fetch_word Ubsan.M.loaded_segments (0xe2268 : word) = Some W_e2220.
Proof. vm_refl. Qed.
Lemma D_e2220 : decode_any W_e2220 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2224 : bv 32 := 0x01813083.
Lemma F_e2224 : fetch_word Ubsan.M.loaded_segments (0xe226c : word) = Some W_e2224.
Proof. vm_refl. Qed.
Lemma D_e2224 : decode_any W_e2224 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2228 : bv 32 := 0x01013403.
Lemma F_e2228 : fetch_word Ubsan.M.loaded_segments (0xe2270 : word) = Some W_e2228.
Proof. vm_refl. Qed.
Lemma D_e2228 : decode_any W_e2228 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e222c : bv 32 := 0x00813483.
Lemma F_e222c : fetch_word Ubsan.M.loaded_segments (0xe2274 : word) = Some W_e222c.
Proof. vm_refl. Qed.
Lemma D_e222c : decode_any W_e222c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2230 : bv 32 := 0x02010113.
Lemma F_e2230 : fetch_word Ubsan.M.loaded_segments (0xe2278 : word) = Some W_e2230.
Proof. vm_refl. Qed.
Lemma D_e2230 : decode_any W_e2230 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2234 : bv 32 := 0xfb5ff06f.
Lemma F_e2234 : fetch_word Ubsan.M.loaded_segments (0xe227c : word) = Some W_e2234.
Proof. vm_refl. Qed.
Lemma D_e2234 : decode_any W_e2234 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2238 : bv 32 := 0xff010113.
Lemma F_e2238 : fetch_word Ubsan.M.loaded_segments (0xe2280 : word) = Some W_e2238.
Proof. vm_refl. Qed.
Lemma D_e2238 : decode_any W_e2238 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e223c : bv 32 := 0x00113423.
Lemma F_e223c : fetch_word Ubsan.M.loaded_segments (0xe2284 : word) = Some W_e223c.
Proof. vm_refl. Qed.
Lemma D_e223c : decode_any W_e223c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2240 : bv 32 := 0x00813023.
Lemma F_e2240 : fetch_word Ubsan.M.loaded_segments (0xe2288 : word) = Some W_e2240.
Proof. vm_refl. Qed.
Lemma D_e2240 : decode_any W_e2240 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2244 : bv 32 := 0x00000593.
Lemma F_e2244 : fetch_word Ubsan.M.loaded_segments (0xe228c : word) = Some W_e2244.
Proof. vm_refl. Qed.
Lemma D_e2244 : decode_any W_e2244 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2248 : bv 32 := 0x00020613.
Lemma F_e2248 : fetch_word Ubsan.M.loaded_segments (0xe2290 : word) = Some W_e2248.
Proof. vm_refl. Qed.
Lemma D_e2248 : decode_any W_e2248 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e224c : bv 32 := 0xf5862603.
Lemma F_e224c : fetch_word Ubsan.M.loaded_segments (0xe2294 : word) = Some W_e224c.
Proof. vm_refl. Qed.
Lemma D_e224c : decode_any W_e224c = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2250 : bv 32 := 0x00049697.
Lemma F_e2250 : fetch_word Ubsan.M.loaded_segments (0xe2298 : word) = Some W_e2250.
Proof. vm_refl. Qed.
Lemma D_e2250 : decode_any W_e2250 = Some (Auipc 13 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2254 : bv 32 := 0x82868693.
Lemma F_e2254 : fetch_word Ubsan.M.loaded_segments (0xe229c : word) = Some W_e2254.
Proof. vm_refl. Qed.
Lemma D_e2254 : decode_any W_e2254 = Some (OpImm ALU_ADD 13 13 2088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2258 : bv 32 := 0x1606a72f.
Lemma F_e2258 : fetch_word Ubsan.M.loaded_segments (0xe22a0 : word) = Some W_e2258.
Proof. vm_refl. Qed.
Lemma D_e2258 : decode_any W_e2258 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e225c : bv 32 := 0x00b71663.
Lemma F_e225c : fetch_word Ubsan.M.loaded_segments (0xe22a4 : word) = Some W_e225c.
Proof. vm_refl. Qed.
Lemma D_e225c : decode_any W_e225c = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2260 : bv 32 := 0x1ec6a7af.
Lemma F_e2260 : fetch_word Ubsan.M.loaded_segments (0xe22a8 : word) = Some W_e2260.
Proof. vm_refl. Qed.
Lemma D_e2260 : decode_any W_e2260 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2264 : bv 32 := 0xfe079ae3.
Lemma F_e2264 : fetch_word Ubsan.M.loaded_segments (0xe22ac : word) = Some W_e2264.
Proof. vm_refl. Qed.
Lemma D_e2264 : decode_any W_e2264 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2268 : bv 32 := 0x0007059b.
Lemma F_e2268 : fetch_word Ubsan.M.loaded_segments (0xe22b0 : word) = Some W_e2268.
Proof. vm_refl. Qed.
Lemma D_e2268 : decode_any W_e2268 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e226c : bv 32 := 0x02c58263.
Lemma F_e226c : fetch_word Ubsan.M.loaded_segments (0xe22b4 : word) = Some W_e226c.
Proof. vm_refl. Qed.
Lemma D_e226c : decode_any W_e226c = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2270 : bv 32 := 0x02058263.
Lemma F_e2270 : fetch_word Ubsan.M.loaded_segments (0xe22b8 : word) = Some W_e2270.
Proof. vm_refl. Qed.
Lemma D_e2270 : decode_any W_e2270 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2274 : bv 32 := 0x04900893.
Lemma F_e2274 : fetch_word Ubsan.M.loaded_segments (0xe22bc : word) = Some W_e2274.
Proof. vm_refl. Qed.
Lemma D_e2274 : decode_any W_e2274 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2278 : bv 32 := 0x00000593.
Lemma F_e2278 : fetch_word Ubsan.M.loaded_segments (0xe22c0 : word) = Some W_e2278.
Proof. vm_refl. Qed.
Lemma D_e2278 : decode_any W_e2278 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e227c : bv 32 := 0x00000613.
Lemma F_e227c : fetch_word Ubsan.M.loaded_segments (0xe22c4 : word) = Some W_e227c.
Proof. vm_refl. Qed.
Lemma D_e227c : decode_any W_e227c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2280 : bv 32 := 0x00000693.
Lemma F_e2280 : fetch_word Ubsan.M.loaded_segments (0xe22c8 : word) = Some W_e2280.
Proof. vm_refl. Qed.
Lemma D_e2280 : decode_any W_e2280 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2284 : bv 32 := 0x00000513.
Lemma F_e2284 : fetch_word Ubsan.M.loaded_segments (0xe22cc : word) = Some W_e2284.
Proof. vm_refl. Qed.
Lemma D_e2284 : decode_any W_e2284 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2288 : bv 32 := 0x00000073.
Lemma F_e2288 : fetch_word Ubsan.M.loaded_segments (0xe22d0 : word) = Some W_e2288.
Proof. vm_refl. Qed.
Lemma E_e2288 : is_ecall W_e2288 = true.
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e228c : bv 32 := 0xff9ff06f.
Lemma F_e228c : fetch_word Ubsan.M.loaded_segments (0xe22d4 : word) = Some W_e228c.
Proof. vm_refl. Qed.
Lemma D_e228c : decode_any W_e228c = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2290 : bv 32 := 0x00000023.
Lemma F_e2290 : fetch_word Ubsan.M.loaded_segments (0xe22d8 : word) = Some W_e2290.
Proof. vm_refl. Qed.
Lemma D_e2290 : decode_any W_e2290 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2294 : bv 32 := 0x00050413.
Lemma F_e2294 : fetch_word Ubsan.M.loaded_segments (0xe22dc : word) = Some W_e2294.
Proof. vm_refl. Qed.
Lemma D_e2294 : decode_any W_e2294 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2298 : bv 32 := 0xdbdff0ef.
Lemma F_e2298 : fetch_word Ubsan.M.loaded_segments (0xe22e0 : word) = Some W_e2298.
Proof. vm_refl. Qed.
Lemma D_e2298 : decode_any W_e2298 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e229c : bv 32 := 0xf51ff0ef.
Lemma F_e229c : fetch_word Ubsan.M.loaded_segments (0xe22e4 : word) = Some W_e229c.
Proof. vm_refl. Qed.
Lemma D_e229c : decode_any W_e229c = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e22a0 : bv 32 := 0x4d9030ef.
Lemma F_e22a0 : fetch_word Ubsan.M.loaded_segments (0xe22e8 : word) = Some W_e22a0.
Proof. vm_refl. Qed.
Lemma D_e22a0 : decode_any W_e22a0 = Some (Jal 1 15576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e22a4 : bv 32 := 0x00040513.
Lemma F_e22a4 : fetch_word Ubsan.M.loaded_segments (0xe22ec : word) = Some W_e22a4.
Proof. vm_refl. Qed.
Lemma D_e22a4 : decode_any W_e22a4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e22a8 : bv 32 := 0xd61ff0ef.
Lemma F_e22a8 : fetch_word Ubsan.M.loaded_segments (0xe22f0 : word) = Some W_e22a8.
Proof. vm_refl. Qed.
Lemma D_e22a8 : decode_any W_e22a8 = Some (Jal 1 2096480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f15c4 : bv 32 := 0x00039597.
Lemma F_f15c4 : fetch_word Ubsan.M.loaded_segments (0xf160c : word) = Some W_f15c4.
Proof. vm_refl. Qed.
Lemma D_f15c4 : decode_any W_f15c4 = Some (Auipc 11 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f15c8 : bv 32 := 0x4df58683.
Lemma F_f15c8 : fetch_word Ubsan.M.loaded_segments (0xf1610 : word) = Some W_f15c8.
Proof. vm_refl. Qed.
Lemma D_f15c8 : decode_any W_f15c8 = Some (Load SZ1 true 13 11 1247, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f15cc : bv 32 := 0x1e068863.
Lemma F_f15cc : fetch_word Ubsan.M.loaded_segments (0xf1614 : word) = Some W_f15cc.
Proof. vm_refl. Qed.
Lemma D_f15cc : decode_any W_f15cc = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f17bc : bv 32 := 0x00008067.
Lemma F_f17bc : fetch_word Ubsan.M.loaded_segments (0xf1804 : word) = Some W_f17bc.
Proof. vm_refl. Qed.
Lemma D_f17bc : decode_any W_f17bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f184c : bv 32 := 0x00052583.
Lemma F_f184c : fetch_word Ubsan.M.loaded_segments (0xf1894 : word) = Some W_f184c.
Proof. vm_refl. Qed.
Lemma D_f184c : decode_any W_f184c = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1850 : bv 32 := 0x0005c463.
Lemma F_f1850 : fetch_word Ubsan.M.loaded_segments (0xf1898 : word) = Some W_f1850.
Proof. vm_refl. Qed.
Lemma D_f1850 : decode_any W_f1850 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1854 : bv 32 := 0x00008067.
Lemma F_f1854 : fetch_word Ubsan.M.loaded_segments (0xf189c : word) = Some W_f1854.
Proof. vm_refl. Qed.
Lemma D_f1854 : decode_any W_f1854 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

