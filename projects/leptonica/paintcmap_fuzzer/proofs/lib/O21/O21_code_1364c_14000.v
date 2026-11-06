(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.H Require GcFlushS21.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_13bbc : bv 32 := 0xfd010113.
Lemma F_13bbc : fetch_word Plain.M.loaded_segments (0x13cc0 : word) = Some W_13bbc.
Proof. vm_refl. Qed.
Lemma D_13bbc : decode_any W_13bbc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bc0 : bv 32 := 0x02113423.
Lemma F_13bc0 : fetch_word Plain.M.loaded_segments (0x13cc4 : word) = Some W_13bc0.
Proof. vm_refl. Qed.
Lemma D_13bc0 : decode_any W_13bc0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bc4 : bv 32 := 0x02813023.
Lemma F_13bc4 : fetch_word Plain.M.loaded_segments (0x13cc8 : word) = Some W_13bc4.
Proof. vm_refl. Qed.
Lemma D_13bc4 : decode_any W_13bc4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bc8 : bv 32 := 0x00913c23.
Lemma F_13bc8 : fetch_word Plain.M.loaded_segments (0x13ccc : word) = Some W_13bc8.
Proof. vm_refl. Qed.
Lemma D_13bc8 : decode_any W_13bc8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bcc : bv 32 := 0x00058413.
Lemma F_13bcc : fetch_word Plain.M.loaded_segments (0x13cd0 : word) = Some W_13bcc.
Proof. vm_refl. Qed.
Lemma D_13bcc : decode_any W_13bcc = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bd0 : bv 32 := 0x00300593.
Lemma F_13bd0 : fetch_word Plain.M.loaded_segments (0x13cd4 : word) = Some W_13bd0.
Proof. vm_refl. Qed.
Lemma D_13bd0 : decode_any W_13bd0 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bd4 : bv 32 := 0x0cb46063.
Lemma F_13bd4 : fetch_word Plain.M.loaded_segments (0x13cd8 : word) = Some W_13bd4.
Proof. vm_refl. Qed.
Lemma D_13bd4 : decode_any W_13bd4 = Some (Branch BC_LTU 8 11 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bd8 : bv 32 := 0x00050493.
Lemma F_13bd8 : fetch_word Plain.M.loaded_segments (0x13cdc : word) = Some W_13bd8.
Proof. vm_refl. Qed.
Lemma D_13bd8 : decode_any W_13bd8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bdc : bv 32 := 0x00000517.
Lemma F_13bdc : fetch_word Plain.M.loaded_segments (0x13ce0 : word) = Some W_13bdc.
Proof. vm_refl. Qed.
Lemma D_13bdc : decode_any W_13bdc = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13be0 : bv 32 := 0x0d050513.
Lemma F_13be0 : fetch_word Plain.M.loaded_segments (0x13ce4 : word) = Some W_13be0.
Proof. vm_refl. Qed.
Lemma D_13be0 : decode_any W_13be0 = Some (OpImm ALU_ADD 10 10 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13be4 : bv 32 := 0x1e8000ef.
Lemma F_13be4 : fetch_word Plain.M.loaded_segments (0x13ce8 : word) = Some W_13be4.
Proof. vm_refl. Qed.
Lemma D_13be4 : decode_any W_13be4 = Some (Jal 1 488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13be8 : bv 32 := 0x00048513.
Lemma F_13be8 : fetch_word Plain.M.loaded_segments (0x13cec : word) = Some W_13be8.
Proof. vm_refl. Qed.
Lemma D_13be8 : decode_any W_13be8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bec : bv 32 := 0x00040593.
Lemma F_13bec : fetch_word Plain.M.loaded_segments (0x13cf0 : word) = Some W_13bec.
Proof. vm_refl. Qed.
Lemma D_13bec : decode_any W_13bec = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bf0 : bv 32 := 0x539020ef.
Lemma F_13bf0 : fetch_word Plain.M.loaded_segments (0x13cf4 : word) = Some W_13bf0.
Proof. vm_refl. Qed.
Lemma D_13bf0 : decode_any W_13bf0 = Some (Jal 1 11576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bf4 : bv 32 := 0x00a13823.
Lemma F_13bf4 : fetch_word Plain.M.loaded_segments (0x13cf8 : word) = Some W_13bf4.
Proof. vm_refl. Qed.
Lemma D_13bf4 : decode_any W_13bf4 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bf8 : bv 32 := 0x08050e63.
Lemma F_13bf8 : fetch_word Plain.M.loaded_segments (0x13cfc : word) = Some W_13bf8.
Proof. vm_refl. Qed.
Lemma D_13bf8 : decode_any W_13bf8 = Some (Branch BC_EQ 10 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bfc : bv 32 := 0x00050413.
Lemma F_13bfc : fetch_word Plain.M.loaded_segments (0x13d00 : word) = Some W_13bfc.
Proof. vm_refl. Qed.
Lemma D_13bfc : decode_any W_13bfc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c00 : bv 32 := 0x11600513.
Lemma F_13c00 : fetch_word Plain.M.loaded_segments (0x13d04 : word) = Some W_13c00.
Proof. vm_refl. Qed.
Lemma D_13c00 : decode_any W_13c00 = Some (OpImm ALU_ADD 10 0 278, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c04 : bv 32 := 0x02300593.
Lemma F_13c04 : fetch_word Plain.M.loaded_segments (0x13d08 : word) = Some W_13c04.
Proof. vm_refl. Qed.
Lemma D_13c04 : decode_any W_13c04 = Some (OpImm ALU_ADD 11 0 35, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c08 : bv 32 := 0x07a00613.
Lemma F_13c08 : fetch_word Plain.M.loaded_segments (0x13d0c : word) = Some W_13c08.
Proof. vm_refl. Qed.
Lemma D_13c08 : decode_any W_13c08 = Some (OpImm ALU_ADD 12 0 122, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c0c : bv 32 := 0x03200693.
Lemma F_13c0c : fetch_word Plain.M.loaded_segments (0x13d10 : word) = Some W_13c0c.
Proof. vm_refl. Qed.
Lemma D_13c0c : decode_any W_13c0c = Some (OpImm ALU_ADD 13 0 50, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c10 : bv 32 := 0x3a8000ef.
Lemma F_13c10 : fetch_word Plain.M.loaded_segments (0x13d14 : word) = Some W_13c10.
Proof. vm_refl. Qed.
Lemma D_13c10 : decode_any W_13c10 = Some (Jal 1 936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c14 : bv 32 := 0x00050493.
Lemma F_13c14 : fetch_word Plain.M.loaded_segments (0x13d18 : word) = Some W_13c14.
Proof. vm_refl. Qed.
Lemma D_13c14 : decode_any W_13c14 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c18 : bv 32 := 0x00a13423.
Lemma F_13c18 : fetch_word Plain.M.loaded_segments (0x13d1c : word) = Some W_13c18.
Proof. vm_refl. Qed.
Lemma D_13c18 : decode_any W_13c18 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c1c : bv 32 := 0x00000513.
Lemma F_13c1c : fetch_word Plain.M.loaded_segments (0x13d20 : word) = Some W_13c1c.
Proof. vm_refl. Qed.
Lemma D_13c1c : decode_any W_13c1c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c20 : bv 32 := 0x00040593.
Lemma F_13c20 : fetch_word Plain.M.loaded_segments (0x13d24 : word) = Some W_13c20.
Proof. vm_refl. Qed.
Lemma D_13c20 : decode_any W_13c20 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c24 : bv 32 := 0x07c010ef.
Lemma F_13c24 : fetch_word Plain.M.loaded_segments (0x13d28 : word) = Some W_13c24.
Proof. vm_refl. Qed.
Lemma D_13c24 : decode_any W_13c24 = Some (Jal 1 4220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c28 : bv 32 := 0x00a13023.
Lemma F_13c28 : fetch_word Plain.M.loaded_segments (0x13d2c : word) = Some W_13c28.
Proof. vm_refl. Qed.
Lemma D_13c28 : decode_any W_13c28 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c2c : bv 32 := 0x00200613.
Lemma F_13c2c : fetch_word Plain.M.loaded_segments (0x13d30 : word) = Some W_13c2c.
Proof. vm_refl. Qed.
Lemma D_13c2c : decode_any W_13c2c = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c30 : bv 32 := 0x0ff00693.
Lemma F_13c30 : fetch_word Plain.M.loaded_segments (0x13d34 : word) = Some W_13c30.
Proof. vm_refl. Qed.
Lemma D_13c30 : decode_any W_13c30 = Some (OpImm ALU_ADD 13 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c34 : bv 32 := 0x0ff00713.
Lemma F_13c34 : fetch_word Plain.M.loaded_segments (0x13d38 : word) = Some W_13c34.
Proof. vm_refl. Qed.
Lemma D_13c34 : decode_any W_13c34 = Some (OpImm ALU_ADD 14 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c38 : bv 32 := 0x06400793.
Lemma F_13c38 : fetch_word Plain.M.loaded_segments (0x13d3c : word) = Some W_13c38.
Proof. vm_refl. Qed.
Lemma D_13c38 : decode_any W_13c38 = Some (OpImm ALU_ADD 15 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c3c : bv 32 := 0x00048593.
Lemma F_13c3c : fetch_word Plain.M.loaded_segments (0x13d40 : word) = Some W_13c3c.
Proof. vm_refl. Qed.
Lemma D_13c3c : decode_any W_13c3c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c40 : bv 32 := 0x418020ef.
Lemma F_13c40 : fetch_word Plain.M.loaded_segments (0x13d44 : word) = Some W_13c40.
Proof. vm_refl. Qed.
Lemma D_13c40 : decode_any W_13c40 = Some (Jal 1 9240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c44 : bv 32 := 0x00810513.
Lemma F_13c44 : fetch_word Plain.M.loaded_segments (0x13d48 : word) = Some W_13c44.
Proof. vm_refl. Qed.
Lemma D_13c44 : decode_any W_13c44 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c48 : bv 32 := 0x4f0000ef.
Lemma F_13c48 : fetch_word Plain.M.loaded_segments (0x13d4c : word) = Some W_13c48.
Proof. vm_refl. Qed.
Lemma D_13c48 : decode_any W_13c48 = Some (Jal 1 1264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c4c : bv 32 := 0x00010513.
Lemma F_13c4c : fetch_word Plain.M.loaded_segments (0x13d50 : word) = Some W_13c4c.
Proof. vm_refl. Qed.
Lemma D_13c4c : decode_any W_13c4c = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c50 : bv 32 := 0x2fd000ef.
Lemma F_13c50 : fetch_word Plain.M.loaded_segments (0x13d54 : word) = Some W_13c50.
Proof. vm_refl. Qed.
Lemma D_13c50 : decode_any W_13c50 = Some (Jal 1 2812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c54 : bv 32 := 0x00000513.
Lemma F_13c54 : fetch_word Plain.M.loaded_segments (0x13d58 : word) = Some W_13c54.
Proof. vm_refl. Qed.
Lemma D_13c54 : decode_any W_13c54 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c58 : bv 32 := 0x00040593.
Lemma F_13c58 : fetch_word Plain.M.loaded_segments (0x13d5c : word) = Some W_13c58.
Proof. vm_refl. Qed.
Lemma D_13c58 : decode_any W_13c58 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c5c : bv 32 := 0x044010ef.
Lemma F_13c5c : fetch_word Plain.M.loaded_segments (0x13d60 : word) = Some W_13c5c.
Proof. vm_refl. Qed.
Lemma D_13c5c : decode_any W_13c5c = Some (Jal 1 4164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c60 : bv 32 := 0x00a13023.
Lemma F_13c60 : fetch_word Plain.M.loaded_segments (0x13d64 : word) = Some W_13c60.
Proof. vm_refl. Qed.
Lemma D_13c60 : decode_any W_13c60 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c64 : bv 32 := 0x00100613.
Lemma F_13c64 : fetch_word Plain.M.loaded_segments (0x13d68 : word) = Some W_13c64.
Proof. vm_refl. Qed.
Lemma D_13c64 : decode_any W_13c64 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c68 : bv 32 := 0x03200693.
Lemma F_13c68 : fetch_word Plain.M.loaded_segments (0x13d6c : word) = Some W_13c68.
Proof. vm_refl. Qed.
Lemma D_13c68 : decode_any W_13c68 = Some (OpImm ALU_ADD 13 0 50, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c6c : bv 32 := 0x0fa00793.
Lemma F_13c6c : fetch_word Plain.M.loaded_segments (0x13d70 : word) = Some W_13c6c.
Proof. vm_refl. Qed.
Lemma D_13c6c : decode_any W_13c6c = Some (OpImm ALU_ADD 15 0 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c70 : bv 32 := 0x0f900813.
Lemma F_13c70 : fetch_word Plain.M.loaded_segments (0x13d74 : word) = Some W_13c70.
Proof. vm_refl. Qed.
Lemma D_13c70 : decode_any W_13c70 = Some (OpImm ALU_ADD 16 0 249, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c74 : bv 32 := 0x0f800893.
Lemma F_13c74 : fetch_word Plain.M.loaded_segments (0x13d78 : word) = Some W_13c74.
Proof. vm_refl. Qed.
Lemma D_13c74 : decode_any W_13c74 = Some (OpImm ALU_ADD 17 0 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c78 : bv 32 := 0x00000593.
Lemma F_13c78 : fetch_word Plain.M.loaded_segments (0x13d7c : word) = Some W_13c78.
Proof. vm_refl. Qed.
Lemma D_13c78 : decode_any W_13c78 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c7c : bv 32 := 0x00000713.
Lemma F_13c7c : fetch_word Plain.M.loaded_segments (0x13d80 : word) = Some W_13c7c.
Proof. vm_refl. Qed.
Lemma D_13c7c : decode_any W_13c7c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c80 : bv 32 := 0x021020ef.
Lemma F_13c80 : fetch_word Plain.M.loaded_segments (0x13d84 : word) = Some W_13c80.
Proof. vm_refl. Qed.
Lemma D_13c80 : decode_any W_13c80 = Some (Jal 1 10272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c84 : bv 32 := 0x00010513.
Lemma F_13c84 : fetch_word Plain.M.loaded_segments (0x13d88 : word) = Some W_13c84.
Proof. vm_refl. Qed.
Lemma D_13c84 : decode_any W_13c84 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c88 : bv 32 := 0x2c5000ef.
Lemma F_13c88 : fetch_word Plain.M.loaded_segments (0x13d8c : word) = Some W_13c88.
Proof. vm_refl. Qed.
Lemma D_13c88 : decode_any W_13c88 = Some (Jal 1 2756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c8c : bv 32 := 0x01010513.
Lemma F_13c8c : fetch_word Plain.M.loaded_segments (0x13d90 : word) = Some W_13c8c.
Proof. vm_refl. Qed.
Lemma D_13c8c : decode_any W_13c8c = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c90 : bv 32 := 0x2bd000ef.
Lemma F_13c90 : fetch_word Plain.M.loaded_segments (0x13d94 : word) = Some W_13c90.
Proof. vm_refl. Qed.
Lemma D_13c90 : decode_any W_13c90 = Some (Jal 1 2748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c94 : bv 32 := 0x00000513.
Lemma F_13c94 : fetch_word Plain.M.loaded_segments (0x13d98 : word) = Some W_13c94.
Proof. vm_refl. Qed.
Lemma D_13c94 : decode_any W_13c94 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c98 : bv 32 := 0x02813083.
Lemma F_13c98 : fetch_word Plain.M.loaded_segments (0x13d9c : word) = Some W_13c98.
Proof. vm_refl. Qed.
Lemma D_13c98 : decode_any W_13c98 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c9c : bv 32 := 0x02013403.
Lemma F_13c9c : fetch_word Plain.M.loaded_segments (0x13da0 : word) = Some W_13c9c.
Proof. vm_refl. Qed.
Lemma D_13c9c : decode_any W_13c9c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ca0 : bv 32 := 0x01813483.
Lemma F_13ca0 : fetch_word Plain.M.loaded_segments (0x13da4 : word) = Some W_13ca0.
Proof. vm_refl. Qed.
Lemma D_13ca0 : decode_any W_13ca0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ca4 : bv 32 := 0x03010113.
Lemma F_13ca4 : fetch_word Plain.M.loaded_segments (0x13da8 : word) = Some W_13ca4.
Proof. vm_refl. Qed.
Lemma D_13ca4 : decode_any W_13ca4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ca8 : bv 32 := 0x00008067.
Lemma F_13ca8 : fetch_word Plain.M.loaded_segments (0x13dac : word) = Some W_13ca8.
Proof. vm_refl. Qed.
Lemma D_13ca8 : decode_any W_13ca8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cb0 : bv 32 := 0xff010113.
Lemma F_13cb0 : fetch_word Plain.M.loaded_segments (0x13db4 : word) = Some W_13cb0.
Proof. vm_refl. Qed.
Lemma D_13cb0 : decode_any W_13cb0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cb4 : bv 32 := 0x00113423.
Lemma F_13cb4 : fetch_word Plain.M.loaded_segments (0x13db8 : word) = Some W_13cb4.
Proof. vm_refl. Qed.
Lemma D_13cb4 : decode_any W_13cb4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cb8 : bv 32 := 0x00813023.
Lemma F_13cb8 : fetch_word Plain.M.loaded_segments (0x13dbc : word) = Some W_13cb8.
Proof. vm_refl. Qed.
Lemma D_13cb8 : decode_any W_13cb8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cbc : bv 32 := 0x00060413.
Lemma F_13cbc : fetch_word Plain.M.loaded_segments (0x13dc0 : word) = Some W_13cbc.
Proof. vm_refl. Qed.
Lemma D_13cbc : decode_any W_13cbc = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cc0 : bv 32 := 0x00050613.
Lemma F_13cc0 : fetch_word Plain.M.loaded_segments (0x13dc4 : word) = Some W_13cc0.
Proof. vm_refl. Qed.
Lemma D_13cc0 : decode_any W_13cc0 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cc4 : bv 32 := 0xffffd517.
Lemma F_13cc4 : fetch_word Plain.M.loaded_segments (0x13dc8 : word) = Some W_13cc4.
Proof. vm_refl. Qed.
Lemma D_13cc4 : decode_any W_13cc4 = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cc8 : bv 32 := 0xf1d50513.
Lemma F_13cc8 : fetch_word Plain.M.loaded_segments (0x13dcc : word) = Some W_13cc8.
Proof. vm_refl. Qed.
Lemma D_13cc8 : decode_any W_13cc8 = Some (OpImm ALU_ADD 10 10 3869, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ccc : bv 32 := 0x018000ef.
Lemma F_13ccc : fetch_word Plain.M.loaded_segments (0x13dd0 : word) = Some W_13ccc.
Proof. vm_refl. Qed.
Lemma D_13ccc : decode_any W_13ccc = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cd0 : bv 32 := 0x00040513.
Lemma F_13cd0 : fetch_word Plain.M.loaded_segments (0x13dd4 : word) = Some W_13cd0.
Proof. vm_refl. Qed.
Lemma D_13cd0 : decode_any W_13cd0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cd4 : bv 32 := 0x00813083.
Lemma F_13cd4 : fetch_word Plain.M.loaded_segments (0x13dd8 : word) = Some W_13cd4.
Proof. vm_refl. Qed.
Lemma D_13cd4 : decode_any W_13cd4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cd8 : bv 32 := 0x00013403.
Lemma F_13cd8 : fetch_word Plain.M.loaded_segments (0x13ddc : word) = Some W_13cd8.
Proof. vm_refl. Qed.
Lemma D_13cd8 : decode_any W_13cd8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cdc : bv 32 := 0x01010113.
Lemma F_13cdc : fetch_word Plain.M.loaded_segments (0x13de0 : word) = Some W_13cdc.
Proof. vm_refl. Qed.
Lemma D_13cdc : decode_any W_13cdc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ce0 : bv 32 := 0x00008067.
Lemma F_13ce0 : fetch_word Plain.M.loaded_segments (0x13de4 : word) = Some W_13ce0.
Proof. vm_refl. Qed.
Lemma D_13ce0 : decode_any W_13ce0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d80 : bv 32 := 0xff010113.
Lemma F_13d80 : fetch_word Plain.M.loaded_segments (0x13e84 : word) = Some W_13d80.
Proof. vm_refl. Qed.
Lemma D_13d80 : decode_any W_13d80 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d84 : bv 32 := 0x00113423.
Lemma F_13d84 : fetch_word Plain.M.loaded_segments (0x13e88 : word) = Some W_13d84.
Proof. vm_refl. Qed.
Lemma D_13d84 : decode_any W_13d84 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d88 : bv 32 := 0x00813023.
Lemma F_13d88 : fetch_word Plain.M.loaded_segments (0x13e8c : word) = Some W_13d88.
Proof. vm_refl. Qed.
Lemma D_13d88 : decode_any W_13d88 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d8c : bv 32 := 0x00060413.
Lemma F_13d8c : fetch_word Plain.M.loaded_segments (0x13e90 : word) = Some W_13d8c.
Proof. vm_refl. Qed.
Lemma D_13d8c : decode_any W_13d8c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d90 : bv 32 := 0x00050613.
Lemma F_13d90 : fetch_word Plain.M.loaded_segments (0x13e94 : word) = Some W_13d90.
Proof. vm_refl. Qed.
Lemma D_13d90 : decode_any W_13d90 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d94 : bv 32 := 0xffffd517.
Lemma F_13d94 : fetch_word Plain.M.loaded_segments (0x13e98 : word) = Some W_13d94.
Proof. vm_refl. Qed.
Lemma D_13d94 : decode_any W_13d94 = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d98 : bv 32 := 0xe4d50513.
Lemma F_13d98 : fetch_word Plain.M.loaded_segments (0x13e9c : word) = Some W_13d98.
Proof. vm_refl. Qed.
Lemma D_13d98 : decode_any W_13d98 = Some (OpImm ALU_ADD 10 10 3661, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d9c : bv 32 := 0xf49ff0ef.
Lemma F_13d9c : fetch_word Plain.M.loaded_segments (0x13ea0 : word) = Some W_13d9c.
Proof. vm_refl. Qed.
Lemma D_13d9c : decode_any W_13d9c = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13da0 : bv 32 := 0x00040513.
Lemma F_13da0 : fetch_word Plain.M.loaded_segments (0x13ea4 : word) = Some W_13da0.
Proof. vm_refl. Qed.
Lemma D_13da0 : decode_any W_13da0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13da4 : bv 32 := 0x00813083.
Lemma F_13da4 : fetch_word Plain.M.loaded_segments (0x13ea8 : word) = Some W_13da4.
Proof. vm_refl. Qed.
Lemma D_13da4 : decode_any W_13da4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13da8 : bv 32 := 0x00013403.
Lemma F_13da8 : fetch_word Plain.M.loaded_segments (0x13eac : word) = Some W_13da8.
Proof. vm_refl. Qed.
Lemma D_13da8 : decode_any W_13da8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13dac : bv 32 := 0x01010113.
Lemma F_13dac : fetch_word Plain.M.loaded_segments (0x13eb0 : word) = Some W_13dac.
Proof. vm_refl. Qed.
Lemma D_13dac : decode_any W_13dac = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13db0 : bv 32 := 0x00008067.
Lemma F_13db0 : fetch_word Plain.M.loaded_segments (0x13eb4 : word) = Some W_13db0.
Proof. vm_refl. Qed.
Lemma D_13db0 : decode_any W_13db0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13dcc : bv 32 := 0x00051663.
Lemma F_13dcc : fetch_word Plain.M.loaded_segments (0x13ed0 : word) = Some W_13dcc.
Proof. vm_refl. Qed.
Lemma D_13dcc : decode_any W_13dcc = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13dd8 : bv 32 := 0x0000d597.
Lemma F_13dd8 : fetch_word Plain.M.loaded_segments (0x13edc : word) = Some W_13dd8.
Proof. vm_refl. Qed.
Lemma D_13dd8 : decode_any W_13dd8 = Some (Auipc 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ddc : bv 32 := 0x6aa5be23.
Lemma F_13ddc : fetch_word Plain.M.loaded_segments (0x13ee0 : word) = Some W_13ddc.
Proof. vm_refl. Qed.
Lemma D_13ddc : decode_any W_13ddc = Some (Store SZ8 11 10 1724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13de0 : bv 32 := 0x00008067.
Lemma F_13de0 : fetch_word Plain.M.loaded_segments (0x13ee4 : word) = Some W_13de0.
Proof. vm_refl. Qed.
Lemma D_13de0 : decode_any W_13de0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f28 : bv 32 := 0x02050e63.
Lemma F_13f28 : fetch_word Plain.M.loaded_segments (0x1402c : word) = Some W_13f28.
Proof. vm_refl. Qed.
Lemma D_13f28 : decode_any W_13f28 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f2c : bv 32 := 0xfe010113.
Lemma F_13f2c : fetch_word Plain.M.loaded_segments (0x14030 : word) = Some W_13f2c.
Proof. vm_refl. Qed.
Lemma D_13f2c : decode_any W_13f2c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f30 : bv 32 := 0x00113c23.
Lemma F_13f30 : fetch_word Plain.M.loaded_segments (0x14034 : word) = Some W_13f30.
Proof. vm_refl. Qed.
Lemma D_13f30 : decode_any W_13f30 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f34 : bv 32 := 0x00813823.
Lemma F_13f34 : fetch_word Plain.M.loaded_segments (0x14038 : word) = Some W_13f34.
Proof. vm_refl. Qed.
Lemma D_13f34 : decode_any W_13f34 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f38 : bv 32 := 0x00913423.
Lemma F_13f38 : fetch_word Plain.M.loaded_segments (0x1403c : word) = Some W_13f38.
Proof. vm_refl. Qed.
Lemma D_13f38 : decode_any W_13f38 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f3c : bv 32 := 0x00058493.
Lemma F_13f3c : fetch_word Plain.M.loaded_segments (0x14040 : word) = Some W_13f3c.
Proof. vm_refl. Qed.
Lemma D_13f3c : decode_any W_13f3c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f40 : bv 32 := 0x00050413.
Lemma F_13f40 : fetch_word Plain.M.loaded_segments (0x14044 : word) = Some W_13f40.
Proof. vm_refl. Qed.
Lemma D_13f40 : decode_any W_13f40 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f44 : bv 32 := 0x00053503.
Lemma F_13f44 : fetch_word Plain.M.loaded_segments (0x14048 : word) = Some W_13f44.
Proof. vm_refl. Qed.
Lemma D_13f44 : decode_any W_13f44 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f48 : bv 32 := 0x00050463.
Lemma F_13f48 : fetch_word Plain.M.loaded_segments (0x1404c : word) = Some W_13f48.
Proof. vm_refl. Qed.
Lemma D_13f48 : decode_any W_13f48 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f50 : bv 32 := 0x04048063.
Lemma F_13f50 : fetch_word Plain.M.loaded_segments (0x14054 : word) = Some W_13f50.
Proof. vm_refl. Qed.
Lemma D_13f50 : decode_any W_13f50 = Some (Branch BC_EQ 9 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f90 : bv 32 := 0x00000593.
Lemma F_13f90 : fetch_word Plain.M.loaded_segments (0x14094 : word) = Some W_13f90.
Proof. vm_refl. Qed.
Lemma D_13f90 : decode_any W_13f90 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f94 : bv 32 := 0x00000513.
Lemma F_13f94 : fetch_word Plain.M.loaded_segments (0x14098 : word) = Some W_13f94.
Proof. vm_refl. Qed.
Lemma D_13f94 : decode_any W_13f94 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f98 : bv 32 := 0x00b43023.
Lemma F_13f98 : fetch_word Plain.M.loaded_segments (0x1409c : word) = Some W_13f98.
Proof. vm_refl. Qed.
Lemma D_13f98 : decode_any W_13f98 = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f9c : bv 32 := 0x01813083.
Lemma F_13f9c : fetch_word Plain.M.loaded_segments (0x140a0 : word) = Some W_13f9c.
Proof. vm_refl. Qed.
Lemma D_13f9c : decode_any W_13f9c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fa0 : bv 32 := 0x01013403.
Lemma F_13fa0 : fetch_word Plain.M.loaded_segments (0x140a4 : word) = Some W_13fa0.
Proof. vm_refl. Qed.
Lemma D_13fa0 : decode_any W_13fa0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fa4 : bv 32 := 0x00813483.
Lemma F_13fa4 : fetch_word Plain.M.loaded_segments (0x140a8 : word) = Some W_13fa4.
Proof. vm_refl. Qed.
Lemma D_13fa4 : decode_any W_13fa4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fa8 : bv 32 := 0x02010113.
Lemma F_13fa8 : fetch_word Plain.M.loaded_segments (0x140ac : word) = Some W_13fa8.
Proof. vm_refl. Qed.
Lemma D_13fa8 : decode_any W_13fa8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fac : bv 32 := 0x00008067.
Lemma F_13fac : fetch_word Plain.M.loaded_segments (0x140b0 : word) = Some W_13fac.
Proof. vm_refl. Qed.
Lemma D_13fac : decode_any W_13fac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fb8 : bv 32 := 0xfd010113.
Lemma F_13fb8 : fetch_word Plain.M.loaded_segments (0x140bc : word) = Some W_13fb8.
Proof. vm_refl. Qed.
Lemma D_13fb8 : decode_any W_13fb8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fbc : bv 32 := 0x02113423.
Lemma F_13fbc : fetch_word Plain.M.loaded_segments (0x140c0 : word) = Some W_13fbc.
Proof. vm_refl. Qed.
Lemma D_13fbc : decode_any W_13fbc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fc0 : bv 32 := 0x02813023.
Lemma F_13fc0 : fetch_word Plain.M.loaded_segments (0x140c4 : word) = Some W_13fc0.
Proof. vm_refl. Qed.
Lemma D_13fc0 : decode_any W_13fc0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fc4 : bv 32 := 0x00913c23.
Lemma F_13fc4 : fetch_word Plain.M.loaded_segments (0x140c8 : word) = Some W_13fc4.
Proof. vm_refl. Qed.
Lemma D_13fc4 : decode_any W_13fc4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fc8 : bv 32 := 0x01213823.
Lemma F_13fc8 : fetch_word Plain.M.loaded_segments (0x140cc : word) = Some W_13fc8.
Proof. vm_refl. Qed.
Lemma D_13fc8 : decode_any W_13fc8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fcc : bv 32 := 0x01313423.
Lemma F_13fcc : fetch_word Plain.M.loaded_segments (0x140d0 : word) = Some W_13fcc.
Proof. vm_refl. Qed.
Lemma D_13fcc : decode_any W_13fcc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fd0 : bv 32 := 0x00058913.
Lemma F_13fd0 : fetch_word Plain.M.loaded_segments (0x140d4 : word) = Some W_13fd0.
Proof. vm_refl. Qed.
Lemma D_13fd0 : decode_any W_13fd0 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fd4 : bv 32 := 0x00c6e5b3.
Lemma F_13fd4 : fetch_word Plain.M.loaded_segments (0x140d8 : word) = Some W_13fd4.
Proof. vm_refl. Qed.
Lemma D_13fd4 : decode_any W_13fd4 = Some (Op ALU_OR 11 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fd8 : bv 32 := 0x0605c063.
Lemma F_13fd8 : fetch_word Plain.M.loaded_segments (0x140dc : word) = Some W_13fd8.
Proof. vm_refl. Qed.
Lemma D_13fd8 : decode_any W_13fd8 = Some (Branch BC_LT 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fdc : bv 32 := 0x00068413.
Lemma F_13fdc : fetch_word Plain.M.loaded_segments (0x140e0 : word) = Some W_13fdc.
Proof. vm_refl. Qed.
Lemma D_13fdc : decode_any W_13fdc = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fe0 : bv 32 := 0x00060493.
Lemma F_13fe0 : fetch_word Plain.M.loaded_segments (0x140e4 : word) = Some W_13fe0.
Proof. vm_refl. Qed.
Lemma D_13fe0 : decode_any W_13fe0 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fe4 : bv 32 := 0x00050993.
Lemma F_13fe4 : fetch_word Plain.M.loaded_segments (0x140e8 : word) = Some W_13fe4.
Proof. vm_refl. Qed.
Lemma D_13fe4 : decode_any W_13fe4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fe8 : bv 32 := 0x00055863.
Lemma F_13fe8 : fetch_word Plain.M.loaded_segments (0x140ec : word) = Some W_13fe8.
Proof. vm_refl. Qed.
Lemma D_13fe8 : decode_any W_13fe8 = Some (Branch BC_GE 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ff8 : bv 32 := 0x00095863.
Lemma F_13ff8 : fetch_word Plain.M.loaded_segments (0x140fc : word) = Some W_13ff8.
Proof. vm_refl. Qed.
Lemma D_13ff8 : decode_any W_13ff8 = Some (Branch BC_GE 18 0 16, 4%Z).
Proof. vm_refl. Qed.
