(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.H Require GcFlushS8.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_13bd0 : bv 32 := 0xfd010113.
Lemma F_13bd0 : fetch_word Plain.M.loaded_segments (0x13cd4 : word) = Some W_13bd0.
Proof. vm_refl. Qed.
Lemma D_13bd0 : decode_any W_13bd0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bd4 : bv 32 := 0x02113423.
Lemma F_13bd4 : fetch_word Plain.M.loaded_segments (0x13cd8 : word) = Some W_13bd4.
Proof. vm_refl. Qed.
Lemma D_13bd4 : decode_any W_13bd4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bd8 : bv 32 := 0x02813023.
Lemma F_13bd8 : fetch_word Plain.M.loaded_segments (0x13cdc : word) = Some W_13bd8.
Proof. vm_refl. Qed.
Lemma D_13bd8 : decode_any W_13bd8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bdc : bv 32 := 0x00913c23.
Lemma F_13bdc : fetch_word Plain.M.loaded_segments (0x13ce0 : word) = Some W_13bdc.
Proof. vm_refl. Qed.
Lemma D_13bdc : decode_any W_13bdc = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13be0 : bv 32 := 0x00058413.
Lemma F_13be0 : fetch_word Plain.M.loaded_segments (0x13ce4 : word) = Some W_13be0.
Proof. vm_refl. Qed.
Lemma D_13be0 : decode_any W_13be0 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13be4 : bv 32 := 0x00300593.
Lemma F_13be4 : fetch_word Plain.M.loaded_segments (0x13ce8 : word) = Some W_13be4.
Proof. vm_refl. Qed.
Lemma D_13be4 : decode_any W_13be4 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13be8 : bv 32 := 0x04b46463.
Lemma F_13be8 : fetch_word Plain.M.loaded_segments (0x13cec : word) = Some W_13be8.
Proof. vm_refl. Qed.
Lemma D_13be8 : decode_any W_13be8 = Some (Branch BC_LTU 8 11 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bec : bv 32 := 0x00050493.
Lemma F_13bec : fetch_word Plain.M.loaded_segments (0x13cf0 : word) = Some W_13bec.
Proof. vm_refl. Qed.
Lemma D_13bec : decode_any W_13bec = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bf0 : bv 32 := 0x00000517.
Lemma F_13bf0 : fetch_word Plain.M.loaded_segments (0x13cf4 : word) = Some W_13bf0.
Proof. vm_refl. Qed.
Lemma D_13bf0 : decode_any W_13bf0 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bf4 : bv 32 := 0x05850513.
Lemma F_13bf4 : fetch_word Plain.M.loaded_segments (0x13cf8 : word) = Some W_13bf4.
Proof. vm_refl. Qed.
Lemma D_13bf4 : decode_any W_13bf4 = Some (OpImm ALU_ADD 10 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bf8 : bv 32 := 0x170000ef.
Lemma F_13bf8 : fetch_word Plain.M.loaded_segments (0x13cfc : word) = Some W_13bf8.
Proof. vm_refl. Qed.
Lemma D_13bf8 : decode_any W_13bf8 = Some (Jal 1 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bfc : bv 32 := 0x00048513.
Lemma F_13bfc : fetch_word Plain.M.loaded_segments (0x13d00 : word) = Some W_13bfc.
Proof. vm_refl. Qed.
Lemma D_13bfc : decode_any W_13bfc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c00 : bv 32 := 0x00040593.
Lemma F_13c00 : fetch_word Plain.M.loaded_segments (0x13d04 : word) = Some W_13c00.
Proof. vm_refl. Qed.
Lemma D_13c00 : decode_any W_13c00 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c04 : bv 32 := 0x4ac020ef.
Lemma F_13c04 : fetch_word Plain.M.loaded_segments (0x13d08 : word) = Some W_13c04.
Proof. vm_refl. Qed.
Lemma D_13c04 : decode_any W_13c04 = Some (Jal 1 9388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c08 : bv 32 := 0x00a13823.
Lemma F_13c08 : fetch_word Plain.M.loaded_segments (0x13d0c : word) = Some W_13c08.
Proof. vm_refl. Qed.
Lemma D_13c08 : decode_any W_13c08 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c0c : bv 32 := 0x02050263.
Lemma F_13c0c : fetch_word Plain.M.loaded_segments (0x13d10 : word) = Some W_13c0c.
Proof. vm_refl. Qed.
Lemma D_13c0c : decode_any W_13c0c = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c10 : bv 32 := 0x00100593.
Lemma F_13c10 : fetch_word Plain.M.loaded_segments (0x13d14 : word) = Some W_13c10.
Proof. vm_refl. Qed.
Lemma D_13c10 : decode_any W_13c10 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c14 : bv 32 := 0x00100613.
Lemma F_13c14 : fetch_word Plain.M.loaded_segments (0x13d18 : word) = Some W_13c14.
Proof. vm_refl. Qed.
Lemma D_13c14 : decode_any W_13c14 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c18 : bv 32 := 0x0e9020ef.
Lemma F_13c18 : fetch_word Plain.M.loaded_segments (0x13d1c : word) = Some W_13c18.
Proof. vm_refl. Qed.
Lemma D_13c18 : decode_any W_13c18 = Some (Jal 1 10472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c1c : bv 32 := 0x00a13423.
Lemma F_13c1c : fetch_word Plain.M.loaded_segments (0x13d20 : word) = Some W_13c1c.
Proof. vm_refl. Qed.
Lemma D_13c1c : decode_any W_13c1c = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c20 : bv 32 := 0x00810513.
Lemma F_13c20 : fetch_word Plain.M.loaded_segments (0x13d24 : word) = Some W_13c20.
Proof. vm_refl. Qed.
Lemma D_13c20 : decode_any W_13c20 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c24 : bv 32 := 0x31d020ef.
Lemma F_13c24 : fetch_word Plain.M.loaded_segments (0x13d28 : word) = Some W_13c24.
Proof. vm_refl. Qed.
Lemma D_13c24 : decode_any W_13c24 = Some (Jal 1 11036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c28 : bv 32 := 0x01010513.
Lemma F_13c28 : fetch_word Plain.M.loaded_segments (0x13d2c : word) = Some W_13c28.
Proof. vm_refl. Qed.
Lemma D_13c28 : decode_any W_13c28 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c2c : bv 32 := 0x584010ef.
Lemma F_13c2c : fetch_word Plain.M.loaded_segments (0x13d30 : word) = Some W_13c2c.
Proof. vm_refl. Qed.
Lemma D_13c2c : decode_any W_13c2c = Some (Jal 1 5508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c30 : bv 32 := 0x00000513.
Lemma F_13c30 : fetch_word Plain.M.loaded_segments (0x13d34 : word) = Some W_13c30.
Proof. vm_refl. Qed.
Lemma D_13c30 : decode_any W_13c30 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c34 : bv 32 := 0x02813083.
Lemma F_13c34 : fetch_word Plain.M.loaded_segments (0x13d38 : word) = Some W_13c34.
Proof. vm_refl. Qed.
Lemma D_13c34 : decode_any W_13c34 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c38 : bv 32 := 0x02013403.
Lemma F_13c38 : fetch_word Plain.M.loaded_segments (0x13d3c : word) = Some W_13c38.
Proof. vm_refl. Qed.
Lemma D_13c38 : decode_any W_13c38 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c3c : bv 32 := 0x01813483.
Lemma F_13c3c : fetch_word Plain.M.loaded_segments (0x13d40 : word) = Some W_13c3c.
Proof. vm_refl. Qed.
Lemma D_13c3c : decode_any W_13c3c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c40 : bv 32 := 0x03010113.
Lemma F_13c40 : fetch_word Plain.M.loaded_segments (0x13d44 : word) = Some W_13c40.
Proof. vm_refl. Qed.
Lemma D_13c40 : decode_any W_13c40 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c44 : bv 32 := 0x00008067.
Lemma F_13c44 : fetch_word Plain.M.loaded_segments (0x13d48 : word) = Some W_13c44.
Proof. vm_refl. Qed.
Lemma D_13c44 : decode_any W_13c44 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c4c : bv 32 := 0xff010113.
Lemma F_13c4c : fetch_word Plain.M.loaded_segments (0x13d50 : word) = Some W_13c4c.
Proof. vm_refl. Qed.
Lemma D_13c4c : decode_any W_13c4c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c50 : bv 32 := 0x00113423.
Lemma F_13c50 : fetch_word Plain.M.loaded_segments (0x13d54 : word) = Some W_13c50.
Proof. vm_refl. Qed.
Lemma D_13c50 : decode_any W_13c50 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c54 : bv 32 := 0x00813023.
Lemma F_13c54 : fetch_word Plain.M.loaded_segments (0x13d58 : word) = Some W_13c54.
Proof. vm_refl. Qed.
Lemma D_13c54 : decode_any W_13c54 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c58 : bv 32 := 0x00060413.
Lemma F_13c58 : fetch_word Plain.M.loaded_segments (0x13d5c : word) = Some W_13c58.
Proof. vm_refl. Qed.
Lemma D_13c58 : decode_any W_13c58 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c5c : bv 32 := 0x00050613.
Lemma F_13c5c : fetch_word Plain.M.loaded_segments (0x13d60 : word) = Some W_13c5c.
Proof. vm_refl. Qed.
Lemma D_13c5c : decode_any W_13c5c = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c60 : bv 32 := 0xffffd517.
Lemma F_13c60 : fetch_word Plain.M.loaded_segments (0x13d64 : word) = Some W_13c60.
Proof. vm_refl. Qed.
Lemma D_13c60 : decode_any W_13c60 = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c64 : bv 32 := 0xf0350513.
Lemma F_13c64 : fetch_word Plain.M.loaded_segments (0x13d68 : word) = Some W_13c64.
Proof. vm_refl. Qed.
Lemma D_13c64 : decode_any W_13c64 = Some (OpImm ALU_ADD 10 10 3843, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c68 : bv 32 := 0x018000ef.
Lemma F_13c68 : fetch_word Plain.M.loaded_segments (0x13d6c : word) = Some W_13c68.
Proof. vm_refl. Qed.
Lemma D_13c68 : decode_any W_13c68 = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c6c : bv 32 := 0x00040513.
Lemma F_13c6c : fetch_word Plain.M.loaded_segments (0x13d70 : word) = Some W_13c6c.
Proof. vm_refl. Qed.
Lemma D_13c6c : decode_any W_13c6c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c70 : bv 32 := 0x00813083.
Lemma F_13c70 : fetch_word Plain.M.loaded_segments (0x13d74 : word) = Some W_13c70.
Proof. vm_refl. Qed.
Lemma D_13c70 : decode_any W_13c70 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c74 : bv 32 := 0x00013403.
Lemma F_13c74 : fetch_word Plain.M.loaded_segments (0x13d78 : word) = Some W_13c74.
Proof. vm_refl. Qed.
Lemma D_13c74 : decode_any W_13c74 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c78 : bv 32 := 0x01010113.
Lemma F_13c78 : fetch_word Plain.M.loaded_segments (0x13d7c : word) = Some W_13c78.
Proof. vm_refl. Qed.
Lemma D_13c78 : decode_any W_13c78 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c7c : bv 32 := 0x00008067.
Lemma F_13c7c : fetch_word Plain.M.loaded_segments (0x13d80 : word) = Some W_13c7c.
Proof. vm_refl. Qed.
Lemma D_13c7c : decode_any W_13c7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d1c : bv 32 := 0xff010113.
Lemma F_13d1c : fetch_word Plain.M.loaded_segments (0x13e20 : word) = Some W_13d1c.
Proof. vm_refl. Qed.
Lemma D_13d1c : decode_any W_13d1c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d20 : bv 32 := 0x00113423.
Lemma F_13d20 : fetch_word Plain.M.loaded_segments (0x13e24 : word) = Some W_13d20.
Proof. vm_refl. Qed.
Lemma D_13d20 : decode_any W_13d20 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d24 : bv 32 := 0x00813023.
Lemma F_13d24 : fetch_word Plain.M.loaded_segments (0x13e28 : word) = Some W_13d24.
Proof. vm_refl. Qed.
Lemma D_13d24 : decode_any W_13d24 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d28 : bv 32 := 0x00060413.
Lemma F_13d28 : fetch_word Plain.M.loaded_segments (0x13e2c : word) = Some W_13d28.
Proof. vm_refl. Qed.
Lemma D_13d28 : decode_any W_13d28 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d2c : bv 32 := 0x00050613.
Lemma F_13d2c : fetch_word Plain.M.loaded_segments (0x13e30 : word) = Some W_13d2c.
Proof. vm_refl. Qed.
Lemma D_13d2c : decode_any W_13d2c = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d30 : bv 32 := 0xffffd517.
Lemma F_13d30 : fetch_word Plain.M.loaded_segments (0x13e34 : word) = Some W_13d30.
Proof. vm_refl. Qed.
Lemma D_13d30 : decode_any W_13d30 = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d34 : bv 32 := 0xe3350513.
Lemma F_13d34 : fetch_word Plain.M.loaded_segments (0x13e38 : word) = Some W_13d34.
Proof. vm_refl. Qed.
Lemma D_13d34 : decode_any W_13d34 = Some (OpImm ALU_ADD 10 10 3635, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d38 : bv 32 := 0xf49ff0ef.
Lemma F_13d38 : fetch_word Plain.M.loaded_segments (0x13e3c : word) = Some W_13d38.
Proof. vm_refl. Qed.
Lemma D_13d38 : decode_any W_13d38 = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d3c : bv 32 := 0x00040513.
Lemma F_13d3c : fetch_word Plain.M.loaded_segments (0x13e40 : word) = Some W_13d3c.
Proof. vm_refl. Qed.
Lemma D_13d3c : decode_any W_13d3c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d40 : bv 32 := 0x00813083.
Lemma F_13d40 : fetch_word Plain.M.loaded_segments (0x13e44 : word) = Some W_13d40.
Proof. vm_refl. Qed.
Lemma D_13d40 : decode_any W_13d40 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d44 : bv 32 := 0x00013403.
Lemma F_13d44 : fetch_word Plain.M.loaded_segments (0x13e48 : word) = Some W_13d44.
Proof. vm_refl. Qed.
Lemma D_13d44 : decode_any W_13d44 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d48 : bv 32 := 0x01010113.
Lemma F_13d48 : fetch_word Plain.M.loaded_segments (0x13e4c : word) = Some W_13d48.
Proof. vm_refl. Qed.
Lemma D_13d48 : decode_any W_13d48 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d4c : bv 32 := 0x00008067.
Lemma F_13d4c : fetch_word Plain.M.loaded_segments (0x13e50 : word) = Some W_13d4c.
Proof. vm_refl. Qed.
Lemma D_13d4c : decode_any W_13d4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d68 : bv 32 := 0x00051663.
Lemma F_13d68 : fetch_word Plain.M.loaded_segments (0x13e6c : word) = Some W_13d68.
Proof. vm_refl. Qed.
Lemma D_13d68 : decode_any W_13d68 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d74 : bv 32 := 0x0000d597.
Lemma F_13d74 : fetch_word Plain.M.loaded_segments (0x13e78 : word) = Some W_13d74.
Proof. vm_refl. Qed.
Lemma D_13d74 : decode_any W_13d74 = Some (Auipc 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d78 : bv 32 := 0x1aa5b023.
Lemma F_13d78 : fetch_word Plain.M.loaded_segments (0x13e7c : word) = Some W_13d78.
Proof. vm_refl. Qed.
Lemma D_13d78 : decode_any W_13d78 = Some (Store SZ8 11 10 416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d7c : bv 32 := 0x00008067.
Lemma F_13d7c : fetch_word Plain.M.loaded_segments (0x13e80 : word) = Some W_13d7c.
Proof. vm_refl. Qed.
Lemma D_13d7c : decode_any W_13d7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ebc : bv 32 := 0xfe010113.
Lemma F_13ebc : fetch_word Plain.M.loaded_segments (0x13fc0 : word) = Some W_13ebc.
Proof. vm_refl. Qed.
Lemma D_13ebc : decode_any W_13ebc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ec0 : bv 32 := 0x00113c23.
Lemma F_13ec0 : fetch_word Plain.M.loaded_segments (0x13fc4 : word) = Some W_13ec0.
Proof. vm_refl. Qed.
Lemma D_13ec0 : decode_any W_13ec0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ec4 : bv 32 := 0x00813823.
Lemma F_13ec4 : fetch_word Plain.M.loaded_segments (0x13fc8 : word) = Some W_13ec4.
Proof. vm_refl. Qed.
Lemma D_13ec4 : decode_any W_13ec4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ec8 : bv 32 := 0x00913423.
Lemma F_13ec8 : fetch_word Plain.M.loaded_segments (0x13fcc : word) = Some W_13ec8.
Proof. vm_refl. Qed.
Lemma D_13ec8 : decode_any W_13ec8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ecc : bv 32 := 0x00050413.
Lemma F_13ecc : fetch_word Plain.M.loaded_segments (0x13fd0 : word) = Some W_13ecc.
Proof. vm_refl. Qed.
Lemma D_13ecc : decode_any W_13ecc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ed0 : bv 32 := 0xfff0c537.
Lemma F_13ed0 : fetch_word Plain.M.loaded_segments (0x13fd4 : word) = Some W_13ed0.
Proof. vm_refl. Qed.
Lemma D_13ed0 : decode_any W_13ed0 = Some (Lui 10 1048332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ed4 : bv 32 := 0xdbf50593.
Lemma F_13ed4 : fetch_word Plain.M.loaded_segments (0x13fd8 : word) = Some W_13ed4.
Proof. vm_refl. Qed.
Lemma D_13ed4 : decode_any W_13ed4 = Some (OpImm ALU_ADD 11 10 3519, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ed8 : bv 32 := 0x00b405bb.
Lemma F_13ed8 : fetch_word Plain.M.loaded_segments (0x13fdc : word) = Some W_13ed8.
Proof. vm_refl. Qed.
Lemma D_13ed8 : decode_any W_13ed8 = Some (Op32 ALU_ADD 11 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13edc : bv 32 := 0xdc05051b.
Lemma F_13edc : fetch_word Plain.M.loaded_segments (0x13fe0 : word) = Some W_13edc.
Proof. vm_refl. Qed.
Lemma D_13edc : decode_any W_13edc = Some (OpImm32 10 10 3520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ee0 : bv 32 := 0x00a5f463.
Lemma F_13ee0 : fetch_word Plain.M.loaded_segments (0x13fe4 : word) = Some W_13ee0.
Proof. vm_refl. Qed.
Lemma D_13ee0 : decode_any W_13ee0 = Some (Branch BC_GEU 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ee8 : bv 32 := 0x00100513.
Lemma F_13ee8 : fetch_word Plain.M.loaded_segments (0x13fec : word) = Some W_13ee8.
Proof. vm_refl. Qed.
Lemma D_13ee8 : decode_any W_13ee8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13eec : bv 32 := 0x01000593.
Lemma F_13eec : fetch_word Plain.M.loaded_segments (0x13ff0 : word) = Some W_13eec.
Proof. vm_refl. Qed.
Lemma D_13eec : decode_any W_13eec = Some (OpImm ALU_ADD 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ef0 : bv 32 := 0x328030ef.
Lemma F_13ef0 : fetch_word Plain.M.loaded_segments (0x13ff4 : word) = Some W_13ef0.
Proof. vm_refl. Qed.
Lemma D_13ef0 : decode_any W_13ef0 = Some (Jal 1 13096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ef4 : bv 32 := 0x00050493.
Lemma F_13ef4 : fetch_word Plain.M.loaded_segments (0x13ff8 : word) = Some W_13ef4.
Proof. vm_refl. Qed.
Lemma D_13ef4 : decode_any W_13ef4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ef8 : bv 32 := 0x00a13023.
Lemma F_13ef8 : fetch_word Plain.M.loaded_segments (0x13ffc : word) = Some W_13ef8.
Proof. vm_refl. Qed.
Lemma D_13ef8 : decode_any W_13ef8 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13efc : bv 32 := 0x00800593.
Lemma F_13efc : fetch_word Plain.M.loaded_segments (0x14000 : word) = Some W_13efc.
Proof. vm_refl. Qed.
Lemma D_13efc : decode_any W_13efc = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f00 : bv 32 := 0x00040513.
Lemma F_13f00 : fetch_word Plain.M.loaded_segments (0x14004 : word) = Some W_13f00.
Proof. vm_refl. Qed.
Lemma D_13f00 : decode_any W_13f00 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f04 : bv 32 := 0x314030ef.
Lemma F_13f04 : fetch_word Plain.M.loaded_segments (0x14008 : word) = Some W_13f04.
Proof. vm_refl. Qed.
Lemma D_13f04 : decode_any W_13f04 = Some (Jal 1 13076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f08 : bv 32 := 0x00a4b423.
Lemma F_13f08 : fetch_word Plain.M.loaded_segments (0x1400c : word) = Some W_13f08.
Proof. vm_refl. Qed.
Lemma D_13f08 : decode_any W_13f08 = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f0c : bv 32 := 0x00050a63.
Lemma F_13f0c : fetch_word Plain.M.loaded_segments (0x14010 : word) = Some W_13f0c.
Proof. vm_refl. Qed.
Lemma D_13f0c : decode_any W_13f0c = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f10 : bv 32 := 0x00048513.
Lemma F_13f10 : fetch_word Plain.M.loaded_segments (0x14014 : word) = Some W_13f10.
Proof. vm_refl. Qed.
Lemma D_13f10 : decode_any W_13f10 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f14 : bv 32 := 0x0084a023.
Lemma F_13f14 : fetch_word Plain.M.loaded_segments (0x14018 : word) = Some W_13f14.
Proof. vm_refl. Qed.
Lemma D_13f14 : decode_any W_13f14 = Some (Store SZ4 9 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f18 : bv 32 := 0x0004a223.
Lemma F_13f18 : fetch_word Plain.M.loaded_segments (0x1401c : word) = Some W_13f18.
Proof. vm_refl. Qed.
Lemma D_13f18 : decode_any W_13f18 = Some (Store SZ4 9 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f1c : bv 32 := 0x0400006f.
Lemma F_13f1c : fetch_word Plain.M.loaded_segments (0x14020 : word) = Some W_13f1c.
Proof. vm_refl. Qed.
Lemma D_13f1c : decode_any W_13f1c = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f5c : bv 32 := 0x01813083.
Lemma F_13f5c : fetch_word Plain.M.loaded_segments (0x14060 : word) = Some W_13f5c.
Proof. vm_refl. Qed.
Lemma D_13f5c : decode_any W_13f5c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f60 : bv 32 := 0x01013403.
Lemma F_13f60 : fetch_word Plain.M.loaded_segments (0x14064 : word) = Some W_13f60.
Proof. vm_refl. Qed.
Lemma D_13f60 : decode_any W_13f60 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f64 : bv 32 := 0x00813483.
Lemma F_13f64 : fetch_word Plain.M.loaded_segments (0x14068 : word) = Some W_13f64.
Proof. vm_refl. Qed.
Lemma D_13f64 : decode_any W_13f64 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f68 : bv 32 := 0x02010113.
Lemma F_13f68 : fetch_word Plain.M.loaded_segments (0x1406c : word) = Some W_13f68.
Proof. vm_refl. Qed.
Lemma D_13f68 : decode_any W_13f68 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f6c : bv 32 := 0x00008067.
Lemma F_13f6c : fetch_word Plain.M.loaded_segments (0x14070 : word) = Some W_13f6c.
Proof. vm_refl. Qed.
Lemma D_13f6c : decode_any W_13f6c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f70 : bv 32 := 0xf9010113.
Lemma F_13f70 : fetch_word Plain.M.loaded_segments (0x14074 : word) = Some W_13f70.
Proof. vm_refl. Qed.
Lemma D_13f70 : decode_any W_13f70 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f74 : bv 32 := 0x06113423.
Lemma F_13f74 : fetch_word Plain.M.loaded_segments (0x14078 : word) = Some W_13f74.
Proof. vm_refl. Qed.
Lemma D_13f74 : decode_any W_13f74 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f78 : bv 32 := 0x06813023.
Lemma F_13f78 : fetch_word Plain.M.loaded_segments (0x1407c : word) = Some W_13f78.
Proof. vm_refl. Qed.
Lemma D_13f78 : decode_any W_13f78 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f7c : bv 32 := 0x04913c23.
Lemma F_13f7c : fetch_word Plain.M.loaded_segments (0x14080 : word) = Some W_13f7c.
Proof. vm_refl. Qed.
Lemma D_13f7c : decode_any W_13f7c = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f80 : bv 32 := 0x05213823.
Lemma F_13f80 : fetch_word Plain.M.loaded_segments (0x14084 : word) = Some W_13f80.
Proof. vm_refl. Qed.
Lemma D_13f80 : decode_any W_13f80 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f84 : bv 32 := 0x05313423.
Lemma F_13f84 : fetch_word Plain.M.loaded_segments (0x14088 : word) = Some W_13f84.
Proof. vm_refl. Qed.
Lemma D_13f84 : decode_any W_13f84 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f88 : bv 32 := 0x05413023.
Lemma F_13f88 : fetch_word Plain.M.loaded_segments (0x1408c : word) = Some W_13f88.
Proof. vm_refl. Qed.
Lemma D_13f88 : decode_any W_13f88 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f8c : bv 32 := 0x03513c23.
Lemma F_13f8c : fetch_word Plain.M.loaded_segments (0x14090 : word) = Some W_13f8c.
Proof. vm_refl. Qed.
Lemma D_13f8c : decode_any W_13f8c = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f90 : bv 32 := 0x03613823.
Lemma F_13f90 : fetch_word Plain.M.loaded_segments (0x14094 : word) = Some W_13f90.
Proof. vm_refl. Qed.
Lemma D_13f90 : decode_any W_13f90 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f94 : bv 32 := 0x03713423.
Lemma F_13f94 : fetch_word Plain.M.loaded_segments (0x14098 : word) = Some W_13f94.
Proof. vm_refl. Qed.
Lemma D_13f94 : decode_any W_13f94 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f98 : bv 32 := 0x03813023.
Lemma F_13f98 : fetch_word Plain.M.loaded_segments (0x1409c : word) = Some W_13f98.
Proof. vm_refl. Qed.
Lemma D_13f98 : decode_any W_13f98 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f9c : bv 32 := 0x01913c23.
Lemma F_13f9c : fetch_word Plain.M.loaded_segments (0x140a0 : word) = Some W_13f9c.
Proof. vm_refl. Qed.
Lemma D_13f9c : decode_any W_13f9c = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fa0 : bv 32 := 0x01a13823.
Lemma F_13fa0 : fetch_word Plain.M.loaded_segments (0x140a4 : word) = Some W_13fa0.
Proof. vm_refl. Qed.
Lemma D_13fa0 : decode_any W_13fa0 = Some (Store SZ8 2 26 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fa4 : bv 32 := 0x01b13423.
Lemma F_13fa4 : fetch_word Plain.M.loaded_segments (0x140a8 : word) = Some W_13fa4.
Proof. vm_refl. Qed.
Lemma D_13fa4 : decode_any W_13fa4 = Some (Store SZ8 2 27 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fa8 : bv 32 := 0x0c050263.
Lemma F_13fa8 : fetch_word Plain.M.loaded_segments (0x140ac : word) = Some W_13fa8.
Proof. vm_refl. Qed.
Lemma D_13fa8 : decode_any W_13fa8 = Some (Branch BC_EQ 10 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fac : bv 32 := 0x00050413.
Lemma F_13fac : fetch_word Plain.M.loaded_segments (0x140b0 : word) = Some W_13fac.
Proof. vm_refl. Qed.
Lemma D_13fac : decode_any W_13fac = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fb0 : bv 32 := 0x00053483.
Lemma F_13fb0 : fetch_word Plain.M.loaded_segments (0x140b4 : word) = Some W_13fb0.
Proof. vm_refl. Qed.
Lemma D_13fb0 : decode_any W_13fb0 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fb4 : bv 32 := 0x10048c63.
Lemma F_13fb4 : fetch_word Plain.M.loaded_segments (0x140b8 : word) = Some W_13fb4.
Proof. vm_refl. Qed.
Lemma D_13fb4 : decode_any W_13fb4 = Some (Branch BC_EQ 9 0 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fb8 : bv 32 := 0x0044a503.
Lemma F_13fb8 : fetch_word Plain.M.loaded_segments (0x140bc : word) = Some W_13fb8.
Proof. vm_refl. Qed.
Lemma D_13fb8 : decode_any W_13fb8 = Some (Load SZ4 true 10 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fbc : bv 32 := 0x08a05c63.
Lemma F_13fbc : fetch_word Plain.M.loaded_segments (0x140c0 : word) = Some W_13fbc.
Proof. vm_refl. Qed.
Lemma D_13fbc : decode_any W_13fbc = Some (Branch BC_GE 0 10 152, 4%Z).
Proof. vm_refl. Qed.
