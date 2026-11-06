(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5ea24 : bv 32 := 0xfd010113.
Lemma F_5ea24 : fetch_word Asan.M.loaded_segments (0x5ea74 : word) = Some W_5ea24.
Proof. vm_refl. Qed.
Lemma D_5ea24 : decode_any W_5ea24 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea28 : bv 32 := 0x02113423.
Lemma F_5ea28 : fetch_word Asan.M.loaded_segments (0x5ea78 : word) = Some W_5ea28.
Proof. vm_refl. Qed.
Lemma D_5ea28 : decode_any W_5ea28 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea2c : bv 32 := 0x02813023.
Lemma F_5ea2c : fetch_word Asan.M.loaded_segments (0x5ea7c : word) = Some W_5ea2c.
Proof. vm_refl. Qed.
Lemma D_5ea2c : decode_any W_5ea2c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea30 : bv 32 := 0x00913c23.
Lemma F_5ea30 : fetch_word Asan.M.loaded_segments (0x5ea80 : word) = Some W_5ea30.
Proof. vm_refl. Qed.
Lemma D_5ea30 : decode_any W_5ea30 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea34 : bv 32 := 0x01213823.
Lemma F_5ea34 : fetch_word Asan.M.loaded_segments (0x5ea84 : word) = Some W_5ea34.
Proof. vm_refl. Qed.
Lemma D_5ea34 : decode_any W_5ea34 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea38 : bv 32 := 0x01313423.
Lemma F_5ea38 : fetch_word Asan.M.loaded_segments (0x5ea88 : word) = Some W_5ea38.
Proof. vm_refl. Qed.
Lemma D_5ea38 : decode_any W_5ea38 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea3c : bv 32 := 0x01413023.
Lemma F_5ea3c : fetch_word Asan.M.loaded_segments (0x5ea8c : word) = Some W_5ea3c.
Proof. vm_refl. Qed.
Lemma D_5ea3c : decode_any W_5ea3c = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea40 : bv 32 := 0x00058413.
Lemma F_5ea40 : fetch_word Asan.M.loaded_segments (0x5ea90 : word) = Some W_5ea40.
Proof. vm_refl. Qed.
Lemma D_5ea40 : decode_any W_5ea40 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea44 : bv 32 := 0x00058583.
Lemma F_5ea44 : fetch_word Asan.M.loaded_segments (0x5ea94 : word) = Some W_5ea44.
Proof. vm_refl. Qed.
Lemma D_5ea44 : decode_any W_5ea44 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea48 : bv 32 := 0x00300613.
Lemma F_5ea48 : fetch_word Asan.M.loaded_segments (0x5ea98 : word) = Some W_5ea48.
Proof. vm_refl. Qed.
Lemma D_5ea48 : decode_any W_5ea48 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea4c : bv 32 := 0x12c59463.
Lemma F_5ea4c : fetch_word Asan.M.loaded_segments (0x5ea9c : word) = Some W_5ea4c.
Proof. vm_refl. Qed.
Lemma D_5ea4c : decode_any W_5ea4c = Some (Branch BC_NE 11 12 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea50 : bv 32 := 0x00068493.
Lemma F_5ea50 : fetch_word Asan.M.loaded_segments (0x5eaa0 : word) = Some W_5ea50.
Proof. vm_refl. Qed.
Lemma D_5ea50 : decode_any W_5ea50 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea54 : bv 32 := 0x00050913.
Lemma F_5ea54 : fetch_word Asan.M.loaded_segments (0x5eaa4 : word) = Some W_5ea54.
Proof. vm_refl. Qed.
Lemma D_5ea54 : decode_any W_5ea54 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea58 : bv 32 := 0x3e82d0ef.
Lemma F_5ea58 : fetch_word Asan.M.loaded_segments (0x5eaa8 : word) = Some W_5ea58.
Proof. vm_refl. Qed.
Lemma D_5ea58 : decode_any W_5ea58 = Some (Jal 1 185320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea5c : bv 32 := 0x06050c63.
Lemma F_5ea5c : fetch_word Asan.M.loaded_segments (0x5eaac : word) = Some W_5ea5c.
Proof. vm_refl. Qed.
Lemma D_5ea5c : decode_any W_5ea5c = Some (Branch BC_EQ 10 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea60 : bv 32 := 0x00053683.
Lemma F_5ea60 : fetch_word Asan.M.loaded_segments (0x5eab0 : word) = Some W_5ea60.
Proof. vm_refl. Qed.
Lemma D_5ea60 : decode_any W_5ea60 = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea64 : bv 32 := 0x0004b603.
Lemma F_5ea64 : fetch_word Asan.M.loaded_segments (0x5eab4 : word) = Some W_5ea64.
Proof. vm_refl. Qed.
Lemma D_5ea64 : decode_any W_5ea64 = Some (Load SZ8 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea68 : bv 32 := 0x0084b583.
Lemma F_5ea68 : fetch_word Asan.M.loaded_segments (0x5eab8 : word) = Some W_5ea68.
Proof. vm_refl. Qed.
Lemma D_5ea68 : decode_any W_5ea68 = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea6c : bv 32 := 0x0086a983.
Lemma F_5ea6c : fetch_word Asan.M.loaded_segments (0x5eabc : word) = Some W_5ea6c.
Proof. vm_refl. Qed.
Lemma D_5ea6c : decode_any W_5ea6c = Some (Load SZ4 true 19 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea70 : bv 32 := 0x00050a13.
Lemma F_5ea70 : fetch_word Asan.M.loaded_segments (0x5eac0 : word) = Some W_5ea70.
Proof. vm_refl. Qed.
Lemma D_5ea70 : decode_any W_5ea70 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea74 : bv 32 := 0x00060513.
Lemma F_5ea74 : fetch_word Asan.M.loaded_segments (0x5eac4 : word) = Some W_5ea74.
Proof. vm_refl. Qed.
Lemma D_5ea74 : decode_any W_5ea74 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea78 : bv 32 := 0x2a9430ef.
Lemma F_5ea78 : fetch_word Asan.M.loaded_segments (0x5eac8 : word) = Some W_5ea78.
Proof. vm_refl. Qed.
Lemma D_5ea78 : decode_any W_5ea78 = Some (Jal 1 277160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea7c : bv 32 := 0x02099993.
Lemma F_5ea7c : fetch_word Asan.M.loaded_segments (0x5eacc : word) = Some W_5ea7c.
Proof. vm_refl. Qed.
Lemma D_5ea7c : decode_any W_5ea7c = Some (ShiftImm ALU_SLL 19 19 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea80 : bv 32 := 0x02051513.
Lemma F_5ea80 : fetch_word Asan.M.loaded_segments (0x5ead0 : word) = Some W_5ea80.
Proof. vm_refl. Qed.
Lemma D_5ea80 : decode_any W_5ea80 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea84 : bv 32 := 0x02055513.
Lemma F_5ea84 : fetch_word Asan.M.loaded_segments (0x5ead4 : word) = Some W_5ea84.
Proof. vm_refl. Qed.
Lemma D_5ea84 : decode_any W_5ea84 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea88 : bv 32 := 0x00a9e533.
Lemma F_5ea88 : fetch_word Asan.M.loaded_segments (0x5ead8 : word) = Some W_5ea88.
Proof. vm_refl. Qed.
Lemma D_5ea88 : decode_any W_5ea88 = Some (Op ALU_OR 10 19 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea8c : bv 32 := 0x00a43823.
Lemma F_5ea8c : fetch_word Asan.M.loaded_segments (0x5eadc : word) = Some W_5ea8c.
Proof. vm_refl. Qed.
Lemma D_5ea8c : decode_any W_5ea8c = Some (Store SZ8 8 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea90 : bv 32 := 0x050a0593.
Lemma F_5ea90 : fetch_word Asan.M.loaded_segments (0x5eae0 : word) = Some W_5ea90.
Proof. vm_refl. Qed.
Lemma D_5ea90 : decode_any W_5ea90 = Some (OpImm ALU_ADD 11 20 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea94 : bv 32 := 0x00245683.
Lemma F_5ea94 : fetch_word Asan.M.loaded_segments (0x5eae4 : word) = Some W_5ea94.
Proof. vm_refl. Qed.
Lemma D_5ea94 : decode_any W_5ea94 = Some (Load SZ2 false 13 8 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea98 : bv 32 := 0x00446703.
Lemma F_5ea98 : fetch_word Asan.M.loaded_segments (0x5eae8 : word) = Some W_5ea98.
Proof. vm_refl. Qed.
Lemma D_5ea98 : decode_any W_5ea98 = Some (Load SZ4 false 14 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea9c : bv 32 := 0x0d0a0613.
Lemma F_5ea9c : fetch_word Asan.M.loaded_segments (0x5eaec : word) = Some W_5ea9c.
Proof. vm_refl. Qed.
Lemma D_5ea9c : decode_any W_5ea9c = Some (OpImm ALU_ADD 12 20 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eaa0 : bv 32 := 0x2d890513.
Lemma F_5eaa0 : fetch_word Asan.M.loaded_segments (0x5eaf0 : word) = Some W_5eaa0.
Proof. vm_refl. Qed.
Lemma D_5eaa0 : decode_any W_5eaa0 = Some (OpImm ALU_ADD 10 18 728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eaa4 : bv 32 := 0x02069693.
Lemma F_5eaa4 : fetch_word Asan.M.loaded_segments (0x5eaf4 : word) = Some W_5eaa4.
Proof. vm_refl. Qed.
Lemma D_5eaa4 : decode_any W_5eaa4 = Some (ShiftImm ALU_SLL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eaa8 : bv 32 := 0x00e6e7b3.
Lemma F_5eaa8 : fetch_word Asan.M.loaded_segments (0x5eaf8 : word) = Some W_5eaa8.
Proof. vm_refl. Qed.
Lemma D_5eaa8 : decode_any W_5eaa8 = Some (Op ALU_OR 15 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eaac : bv 32 := 0x00048693.
Lemma F_5eaac : fetch_word Asan.M.loaded_segments (0x5eafc : word) = Some W_5eaac.
Proof. vm_refl. Qed.
Lemma D_5eaac : decode_any W_5eaac = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eab0 : bv 32 := 0x00040713.
Lemma F_5eab0 : fetch_word Asan.M.loaded_segments (0x5eb00 : word) = Some W_5eab0.
Proof. vm_refl. Qed.
Lemma D_5eab0 : decode_any W_5eab0 = Some (OpImm ALU_ADD 14 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eab4 : bv 32 := 0x02813083.
Lemma F_5eab4 : fetch_word Asan.M.loaded_segments (0x5eb04 : word) = Some W_5eab4.
Proof. vm_refl. Qed.
Lemma D_5eab4 : decode_any W_5eab4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eab8 : bv 32 := 0x02013403.
Lemma F_5eab8 : fetch_word Asan.M.loaded_segments (0x5eb08 : word) = Some W_5eab8.
Proof. vm_refl. Qed.
Lemma D_5eab8 : decode_any W_5eab8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eabc : bv 32 := 0x01813483.
Lemma F_5eabc : fetch_word Asan.M.loaded_segments (0x5eb0c : word) = Some W_5eabc.
Proof. vm_refl. Qed.
Lemma D_5eabc : decode_any W_5eabc = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eac0 : bv 32 := 0x01013903.
Lemma F_5eac0 : fetch_word Asan.M.loaded_segments (0x5eb10 : word) = Some W_5eac0.
Proof. vm_refl. Qed.
Lemma D_5eac0 : decode_any W_5eac0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eac4 : bv 32 := 0x00813983.
Lemma F_5eac4 : fetch_word Asan.M.loaded_segments (0x5eb14 : word) = Some W_5eac4.
Proof. vm_refl. Qed.
Lemma D_5eac4 : decode_any W_5eac4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eac8 : bv 32 := 0x00013a03.
Lemma F_5eac8 : fetch_word Asan.M.loaded_segments (0x5eb18 : word) = Some W_5eac8.
Proof. vm_refl. Qed.
Lemma D_5eac8 : decode_any W_5eac8 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eacc : bv 32 := 0x03010113.
Lemma F_5eacc : fetch_word Asan.M.loaded_segments (0x5eb1c : word) = Some W_5eacc.
Proof. vm_refl. Qed.
Lemma D_5eacc : decode_any W_5eacc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ead0 : bv 32 := 0x0cc0006f.
Lemma F_5ead0 : fetch_word Asan.M.loaded_segments (0x5eb20 : word) = Some W_5ead0.
Proof. vm_refl. Qed.
Lemma D_5ead0 : decode_any W_5ead0 = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eb9c : bv 32 := 0xfb010113.
Lemma F_5eb9c : fetch_word Asan.M.loaded_segments (0x5ebec : word) = Some W_5eb9c.
Proof. vm_refl. Qed.
Lemma D_5eb9c : decode_any W_5eb9c = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eba0 : bv 32 := 0x04113423.
Lemma F_5eba0 : fetch_word Asan.M.loaded_segments (0x5ebf0 : word) = Some W_5eba0.
Proof. vm_refl. Qed.
Lemma D_5eba0 : decode_any W_5eba0 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eba4 : bv 32 := 0x04813023.
Lemma F_5eba4 : fetch_word Asan.M.loaded_segments (0x5ebf4 : word) = Some W_5eba4.
Proof. vm_refl. Qed.
Lemma D_5eba4 : decode_any W_5eba4 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eba8 : bv 32 := 0x02913c23.
Lemma F_5eba8 : fetch_word Asan.M.loaded_segments (0x5ebf8 : word) = Some W_5eba8.
Proof. vm_refl. Qed.
Lemma D_5eba8 : decode_any W_5eba8 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebac : bv 32 := 0x03213823.
Lemma F_5ebac : fetch_word Asan.M.loaded_segments (0x5ebfc : word) = Some W_5ebac.
Proof. vm_refl. Qed.
Lemma D_5ebac : decode_any W_5ebac = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebb0 : bv 32 := 0x03313423.
Lemma F_5ebb0 : fetch_word Asan.M.loaded_segments (0x5ec00 : word) = Some W_5ebb0.
Proof. vm_refl. Qed.
Lemma D_5ebb0 : decode_any W_5ebb0 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebb4 : bv 32 := 0x03413023.
Lemma F_5ebb4 : fetch_word Asan.M.loaded_segments (0x5ec04 : word) = Some W_5ebb4.
Proof. vm_refl. Qed.
Lemma D_5ebb4 : decode_any W_5ebb4 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebb8 : bv 32 := 0x01513c23.
Lemma F_5ebb8 : fetch_word Asan.M.loaded_segments (0x5ec08 : word) = Some W_5ebb8.
Proof. vm_refl. Qed.
Lemma D_5ebb8 : decode_any W_5ebb8 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebbc : bv 32 := 0x01613823.
Lemma F_5ebbc : fetch_word Asan.M.loaded_segments (0x5ec0c : word) = Some W_5ebbc.
Proof. vm_refl. Qed.
Lemma D_5ebbc : decode_any W_5ebbc = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebc0 : bv 32 := 0x00050413.
Lemma F_5ebc0 : fetch_word Asan.M.loaded_segments (0x5ec10 : word) = Some W_5ebc0.
Proof. vm_refl. Qed.
Lemma D_5ebc0 : decode_any W_5ebc0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebc4 : bv 32 := 0x00c13023.
Lemma F_5ebc4 : fetch_word Asan.M.loaded_segments (0x5ec14 : word) = Some W_5ebc4.
Proof. vm_refl. Qed.
Lemma D_5ebc4 : decode_any W_5ebc4 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebc8 : bv 32 := 0x00d13423.
Lemma F_5ebc8 : fetch_word Asan.M.loaded_segments (0x5ec18 : word) = Some W_5ebc8.
Proof. vm_refl. Qed.
Lemma D_5ebc8 : decode_any W_5ebc8 = Some (Store SZ8 2 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebcc : bv 32 := 0x05053b03.
Lemma F_5ebcc : fetch_word Asan.M.loaded_segments (0x5ec1c : word) = Some W_5ebcc.
Proof. vm_refl. Qed.
Lemma D_5ebcc : decode_any W_5ebcc = Some (Load SZ8 true 22 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebd0 : bv 32 := 0x00058493.
Lemma F_5ebd0 : fetch_word Asan.M.loaded_segments (0x5ec20 : word) = Some W_5ebd0.
Proof. vm_refl. Qed.
Lemma D_5ebd0 : decode_any W_5ebd0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebd4 : bv 32 := 0x000b0663.
Lemma F_5ebd4 : fetch_word Asan.M.loaded_segments (0x5ec24 : word) = Some W_5ebd4.
Proof. vm_refl. Qed.
Lemma D_5ebd4 : decode_any W_5ebd4 = Some (Branch BC_EQ 22 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebd8 : bv 32 := 0x04043503.
Lemma F_5ebd8 : fetch_word Asan.M.loaded_segments (0x5ec28 : word) = Some W_5ebd8.
Proof. vm_refl. Qed.
Lemma D_5ebd8 : decode_any W_5ebd8 = Some (Load SZ8 true 10 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebdc : bv 32 := 0x0cf57263.
Lemma F_5ebdc : fetch_word Asan.M.loaded_segments (0x5ec2c : word) = Some W_5ebdc.
Proof. vm_refl. Qed.
Lemma D_5ebdc : decode_any W_5ebdc = Some (Branch BC_GEU 10 15 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec64 : bv 32 := 0x00013603.
Lemma F_5ec64 : fetch_word Asan.M.loaded_segments (0x5ecb4 : word) = Some W_5ec64.
Proof. vm_refl. Qed.
Lemma D_5ec64 : decode_any W_5ec64 = Some (Load SZ8 true 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec68 : bv 32 := 0x00813683.
Lemma F_5ec68 : fetch_word Asan.M.loaded_segments (0x5ecb8 : word) = Some W_5ec68.
Proof. vm_refl. Qed.
Lemma D_5ec68 : decode_any W_5ec68 = Some (Load SZ8 true 13 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec6c : bv 32 := 0x00040513.
Lemma F_5ec6c : fetch_word Asan.M.loaded_segments (0x5ecbc : word) = Some W_5ec6c.
Proof. vm_refl. Qed.
Lemma D_5ec6c : decode_any W_5ec6c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec70 : bv 32 := 0x00048593.
Lemma F_5ec70 : fetch_word Asan.M.loaded_segments (0x5ecc0 : word) = Some W_5ec70.
Proof. vm_refl. Qed.
Lemma D_5ec70 : decode_any W_5ec70 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec74 : bv 32 := 0x831fd0ef.
Lemma F_5ec74 : fetch_word Asan.M.loaded_segments (0x5ecc4 : word) = Some W_5ec74.
Proof. vm_refl. Qed.
Lemma D_5ec74 : decode_any W_5ec74 = Some (Jal 1 2086960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec78 : bv 32 := 0x04813083.
Lemma F_5ec78 : fetch_word Asan.M.loaded_segments (0x5ecc8 : word) = Some W_5ec78.
Proof. vm_refl. Qed.
Lemma D_5ec78 : decode_any W_5ec78 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec7c : bv 32 := 0x04013403.
Lemma F_5ec7c : fetch_word Asan.M.loaded_segments (0x5eccc : word) = Some W_5ec7c.
Proof. vm_refl. Qed.
Lemma D_5ec7c : decode_any W_5ec7c = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec80 : bv 32 := 0x03813483.
Lemma F_5ec80 : fetch_word Asan.M.loaded_segments (0x5ecd0 : word) = Some W_5ec80.
Proof. vm_refl. Qed.
Lemma D_5ec80 : decode_any W_5ec80 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec84 : bv 32 := 0x03013903.
Lemma F_5ec84 : fetch_word Asan.M.loaded_segments (0x5ecd4 : word) = Some W_5ec84.
Proof. vm_refl. Qed.
Lemma D_5ec84 : decode_any W_5ec84 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec88 : bv 32 := 0x02813983.
Lemma F_5ec88 : fetch_word Asan.M.loaded_segments (0x5ecd8 : word) = Some W_5ec88.
Proof. vm_refl. Qed.
Lemma D_5ec88 : decode_any W_5ec88 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec8c : bv 32 := 0x02013a03.
Lemma F_5ec8c : fetch_word Asan.M.loaded_segments (0x5ecdc : word) = Some W_5ec8c.
Proof. vm_refl. Qed.
Lemma D_5ec8c : decode_any W_5ec8c = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec90 : bv 32 := 0x01813a83.
Lemma F_5ec90 : fetch_word Asan.M.loaded_segments (0x5ece0 : word) = Some W_5ec90.
Proof. vm_refl. Qed.
Lemma D_5ec90 : decode_any W_5ec90 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec94 : bv 32 := 0x01013b03.
Lemma F_5ec94 : fetch_word Asan.M.loaded_segments (0x5ece4 : word) = Some W_5ec94.
Proof. vm_refl. Qed.
Lemma D_5ec94 : decode_any W_5ec94 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec98 : bv 32 := 0x05010113.
Lemma F_5ec98 : fetch_word Asan.M.loaded_segments (0x5ece8 : word) = Some W_5ec98.
Proof. vm_refl. Qed.
Lemma D_5ec98 : decode_any W_5ec98 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec9c : bv 32 := 0x00008067.
Lemma F_5ec9c : fetch_word Asan.M.loaded_segments (0x5ecec : word) = Some W_5ec9c.
Proof. vm_refl. Qed.
Lemma D_5ec9c : decode_any W_5ec9c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eca0 : bv 32 := 0x00060a13.
Lemma F_5eca0 : fetch_word Asan.M.loaded_segments (0x5ecf0 : word) = Some W_5eca0.
Proof. vm_refl. Qed.
Lemma D_5eca0 : decode_any W_5eca0 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eca4 : bv 32 := 0x00068993.
Lemma F_5eca4 : fetch_word Asan.M.loaded_segments (0x5ecf4 : word) = Some W_5eca4.
Proof. vm_refl. Qed.
Lemma D_5eca4 : decode_any W_5eca4 = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eca8 : bv 32 := 0x00078913.
Lemma F_5eca8 : fetch_word Asan.M.loaded_segments (0x5ecf8 : word) = Some W_5eca8.
Proof. vm_refl. Qed.
Lemma D_5eca8 : decode_any W_5eca8 = Some (OpImm ALU_ADD 18 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecac : bv 32 := 0x00102517.
Lemma F_5ecac : fetch_word Asan.M.loaded_segments (0x5ecfc : word) = Some W_5ecac.
Proof. vm_refl. Qed.
Lemma D_5ecac : decode_any W_5ecac = Some (Auipc 10 258, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecb0 : bv 32 := 0xf1453583.
Lemma F_5ecb0 : fetch_word Asan.M.loaded_segments (0x5ed00 : word) = Some W_5ecb0.
Proof. vm_refl. Qed.
Lemma D_5ecb0 : decode_any W_5ecb0 = Some (Load SZ8 true 11 10 3860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecb4 : bv 32 := 0x0305a683.
Lemma F_5ecb4 : fetch_word Asan.M.loaded_segments (0x5ed04 : word) = Some W_5ecb4.
Proof. vm_refl. Qed.
Lemma D_5ecb4 : decode_any W_5ecb4 = Some (Load SZ4 true 13 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecb8 : bv 32 := 0x04d05463.
Lemma F_5ecb8 : fetch_word Asan.M.loaded_segments (0x5ed08 : word) = Some W_5ecb8.
Proof. vm_refl. Qed.
Lemma D_5ecb8 : decode_any W_5ecb8 = Some (Branch BC_GE 0 13 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed00 : bv 32 := 0x00275583.
Lemma F_5ed00 : fetch_word Asan.M.loaded_segments (0x5ed50 : word) = Some W_5ed00.
Proof. vm_refl. Qed.
Lemma D_5ed00 : decode_any W_5ed00 = Some (Load SZ2 false 11 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed04 : bv 32 := 0x00476603.
Lemma F_5ed04 : fetch_word Asan.M.loaded_segments (0x5ed54 : word) = Some W_5ed04.
Proof. vm_refl. Qed.
Lemma D_5ed04 : decode_any W_5ed04 = Some (Load SZ4 false 12 14 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed08 : bv 32 := 0x01070513.
Lemma F_5ed08 : fetch_word Asan.M.loaded_segments (0x5ed58 : word) = Some W_5ed08.
Proof. vm_refl. Qed.
Lemma D_5ed08 : decode_any W_5ed08 = Some (OpImm ALU_ADD 10 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed0c : bv 32 := 0x02059593.
Lemma F_5ed0c : fetch_word Asan.M.loaded_segments (0x5ed5c : word) = Some W_5ed0c.
Proof. vm_refl. Qed.
Lemma D_5ed0c : decode_any W_5ed0c = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed10 : bv 32 := 0x00c5e5b3.
Lemma F_5ed10 : fetch_word Asan.M.loaded_segments (0x5ed60 : word) = Some W_5ed10.
Proof. vm_refl. Qed.
Lemma D_5ed10 : decode_any W_5ed10 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed14 : bv 32 := 0x00758593.
Lemma F_5ed14 : fetch_word Asan.M.loaded_segments (0x5ed64 : word) = Some W_5ed14.
Proof. vm_refl. Qed.
Lemma D_5ed14 : decode_any W_5ed14 = Some (OpImm ALU_ADD 11 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed18 : bv 32 := 0xff85f593.
Lemma F_5ed18 : fetch_word Asan.M.loaded_segments (0x5ed68 : word) = Some W_5ed18.
Proof. vm_refl. Qed.
Lemma D_5ed18 : decode_any W_5ed18 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed1c : bv 32 := 0x0fd00613.
Lemma F_5ed1c : fetch_word Asan.M.loaded_segments (0x5ed6c : word) = Some W_5ed1c.
Proof. vm_refl. Qed.
Lemma D_5ed1c : decode_any W_5ed1c = Some (OpImm ALU_ADD 12 0 253, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed20 : bv 32 := 0x00070a93.
Lemma F_5ed20 : fetch_word Asan.M.loaded_segments (0x5ed70 : word) = Some W_5ed20.
Proof. vm_refl. Qed.
Lemma D_5ed20 : decode_any W_5ed20 = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed24 : bv 32 := 0x370240ef.
Lemma F_5ed24 : fetch_word Asan.M.loaded_segments (0x5ed74 : word) = Some W_5ed24.
Proof. vm_refl. Qed.
Lemma D_5ed24 : decode_any W_5ed24 = Some (Jal 1 148336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed28 : bv 32 := 0x00048513.
Lemma F_5ed28 : fetch_word Asan.M.loaded_segments (0x5ed78 : word) = Some W_5ed28.
Proof. vm_refl. Qed.
Lemma D_5ed28 : decode_any W_5ed28 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed2c : bv 32 := 0x000a0593.
Lemma F_5ed2c : fetch_word Asan.M.loaded_segments (0x5ed7c : word) = Some W_5ed2c.
Proof. vm_refl. Qed.
Lemma D_5ed2c : decode_any W_5ed2c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed30 : bv 32 := 0x00098613.
Lemma F_5ed30 : fetch_word Asan.M.loaded_segments (0x5ed80 : word) = Some W_5ed30.
Proof. vm_refl. Qed.
Lemma D_5ed30 : decode_any W_5ed30 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed34 : bv 32 := 0x000a8693.
Lemma F_5ed34 : fetch_word Asan.M.loaded_segments (0x5ed84 : word) = Some W_5ed34.
Proof. vm_refl. Qed.
Lemma D_5ed34 : decode_any W_5ed34 = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed38 : bv 32 := 0x00090713.
Lemma F_5ed38 : fetch_word Asan.M.loaded_segments (0x5ed88 : word) = Some W_5ed38.
Proof. vm_refl. Qed.
Lemma D_5ed38 : decode_any W_5ed38 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed3c : bv 32 := 0x010000ef.
Lemma F_5ed3c : fetch_word Asan.M.loaded_segments (0x5ed8c : word) = Some W_5ed3c.
Proof. vm_refl. Qed.
Lemma D_5ed3c : decode_any W_5ed3c = Some (Jal 1 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed40 : bv 32 := 0x0184b503.
Lemma F_5ed40 : fetch_word Asan.M.loaded_segments (0x5ed90 : word) = Some W_5ed40.
Proof. vm_refl. Qed.
Lemma D_5ed40 : decode_any W_5ed40 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed44 : bv 32 := 0xf2ab60e3.
Lemma F_5ed44 : fetch_word Asan.M.loaded_segments (0x5ed94 : word) = Some W_5ed44.
Proof. vm_refl. Qed.
Lemma D_5ed44 : decode_any W_5ed44 = Some (Branch BC_LTU 22 10 7968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed48 : bv 32 := 0xf31ff06f.
Lemma F_5ed48 : fetch_word Asan.M.loaded_segments (0x5ed98 : word) = Some W_5ed48.
Proof. vm_refl. Qed.
Lemma D_5ed48 : decode_any W_5ed48 = Some (Jal 0 2096944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed4c : bv 32 := 0xfc010113.
Lemma F_5ed4c : fetch_word Asan.M.loaded_segments (0x5ed9c : word) = Some W_5ed4c.
Proof. vm_refl. Qed.
Lemma D_5ed4c : decode_any W_5ed4c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed50 : bv 32 := 0x02113c23.
Lemma F_5ed50 : fetch_word Asan.M.loaded_segments (0x5eda0 : word) = Some W_5ed50.
Proof. vm_refl. Qed.
Lemma D_5ed50 : decode_any W_5ed50 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed54 : bv 32 := 0x02813823.
Lemma F_5ed54 : fetch_word Asan.M.loaded_segments (0x5eda4 : word) = Some W_5ed54.
Proof. vm_refl. Qed.
Lemma D_5ed54 : decode_any W_5ed54 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed58 : bv 32 := 0x02913423.
Lemma F_5ed58 : fetch_word Asan.M.loaded_segments (0x5eda8 : word) = Some W_5ed58.
Proof. vm_refl. Qed.
Lemma D_5ed58 : decode_any W_5ed58 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed5c : bv 32 := 0x03213023.
Lemma F_5ed5c : fetch_word Asan.M.loaded_segments (0x5edac : word) = Some W_5ed5c.
Proof. vm_refl. Qed.
Lemma D_5ed5c : decode_any W_5ed5c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed60 : bv 32 := 0x01313c23.
Lemma F_5ed60 : fetch_word Asan.M.loaded_segments (0x5edb0 : word) = Some W_5ed60.
Proof. vm_refl. Qed.
Lemma D_5ed60 : decode_any W_5ed60 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed64 : bv 32 := 0x01413823.
Lemma F_5ed64 : fetch_word Asan.M.loaded_segments (0x5edb4 : word) = Some W_5ed64.
Proof. vm_refl. Qed.
Lemma D_5ed64 : decode_any W_5ed64 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed68 : bv 32 := 0x01513423.
Lemma F_5ed68 : fetch_word Asan.M.loaded_segments (0x5edb8 : word) = Some W_5ed68.
Proof. vm_refl. Qed.
Lemma D_5ed68 : decode_any W_5ed68 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed6c : bv 32 := 0x00053783.
Lemma F_5ed6c : fetch_word Asan.M.loaded_segments (0x5edbc : word) = Some W_5ed6c.
Proof. vm_refl. Qed.
Lemma D_5ed6c : decode_any W_5ed6c = Some (Load SZ8 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed70 : bv 32 := 0x00078a63.
Lemma F_5ed70 : fetch_word Asan.M.loaded_segments (0x5edc0 : word) = Some W_5ed70.
Proof. vm_refl. Qed.
Lemma D_5ed70 : decode_any W_5ed70 = Some (Branch BC_EQ 15 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed74 : bv 32 := 0x01053803.
Lemma F_5ed74 : fetch_word Asan.M.loaded_segments (0x5edc4 : word) = Some W_5ed74.
Proof. vm_refl. Qed.
Lemma D_5ed74 : decode_any W_5ed74 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed78 : bv 32 := 0x01083783.
Lemma F_5ed78 : fetch_word Asan.M.loaded_segments (0x5edc8 : word) = Some W_5ed78.
Proof. vm_refl. Qed.
Lemma D_5ed78 : decode_any W_5ed78 = Some (Load SZ8 true 15 16 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed7c : bv 32 := 0x3fd00893.
Lemma F_5ed7c : fetch_word Asan.M.loaded_segments (0x5edcc : word) = Some W_5ed7c.
Proof. vm_refl. Qed.
Lemma D_5ed7c : decode_any W_5ed7c = Some (OpImm ALU_ADD 17 0 1021, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed80 : bv 32 := 0x09179463.
Lemma F_5ed80 : fetch_word Asan.M.loaded_segments (0x5edd0 : word) = Some W_5ed80.
Proof. vm_refl. Qed.
Lemma D_5ed80 : decode_any W_5ed80 = Some (Branch BC_NE 15 17 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed84 : bv 32 := 0x7805a783.
Lemma F_5ed84 : fetch_word Asan.M.loaded_segments (0x5edd4 : word) = Some W_5ed84.
Proof. vm_refl. Qed.
Lemma D_5ed84 : decode_any W_5ed84 = Some (Load SZ4 true 15 11 1920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed88 : bv 32 := 0x0e078263.
Lemma F_5ed88 : fetch_word Asan.M.loaded_segments (0x5edd8 : word) = Some W_5ed88.
Proof. vm_refl. Qed.
Lemma D_5ed88 : decode_any W_5ed88 = Some (Branch BC_EQ 15 0 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed8c : bv 32 := 0xfff78793.
Lemma F_5ed8c : fetch_word Asan.M.loaded_segments (0x5eddc : word) = Some W_5ed8c.
Proof. vm_refl. Qed.
Lemma D_5ed8c : decode_any W_5ed8c = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed90 : bv 32 := 0x02079813.
Lemma F_5ed90 : fetch_word Asan.M.loaded_segments (0x5ede0 : word) = Some W_5ed90.
Proof. vm_refl. Qed.
Lemma D_5ed90 : decode_any W_5ed90 = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed94 : bv 32 := 0x78f5a023.
Lemma F_5ed94 : fetch_word Asan.M.loaded_segments (0x5ede4 : word) = Some W_5ed94.
Proof. vm_refl. Qed.
Lemma D_5ed94 : decode_any W_5ed94 = Some (Store SZ4 11 15 1920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed98 : bv 32 := 0x01e85793.
Lemma F_5ed98 : fetch_word Asan.M.loaded_segments (0x5ede8 : word) = Some W_5ed98.
Proof. vm_refl. Qed.
Lemma D_5ed98 : decode_any W_5ed98 = Some (ShiftImm ALU_SRL 15 16 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed9c : bv 32 := 0x00f587b3.
Lemma F_5ed9c : fetch_word Asan.M.loaded_segments (0x5edec : word) = Some W_5ed9c.
Proof. vm_refl. Qed.
Lemma D_5ed9c : decode_any W_5ed9c = Some (Op ALU_ADD 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eda0 : bv 32 := 0x7885b803.
Lemma F_5eda0 : fetch_word Asan.M.loaded_segments (0x5edf0 : word) = Some W_5eda0.
Proof. vm_refl. Qed.
Lemma D_5eda0 : decode_any W_5eda0 = Some (Load SZ8 true 16 11 1928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eda4 : bv 32 := 0x7ff58593.
Lemma F_5eda4 : fetch_word Asan.M.loaded_segments (0x5edf4 : word) = Some W_5eda4.
Proof. vm_refl. Qed.
Lemma D_5eda4 : decode_any W_5eda4 = Some (OpImm ALU_ADD 11 11 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eda8 : bv 32 := 0x21158593.
Lemma F_5eda8 : fetch_word Asan.M.loaded_segments (0x5edf8 : word) = Some W_5eda8.
Proof. vm_refl. Qed.
Lemma D_5eda8 : decode_any W_5eda8 = Some (OpImm ALU_ADD 11 11 529, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edac : bv 32 := 0x7907e783.
Lemma F_5edac : fetch_word Asan.M.loaded_segments (0x5edfc : word) = Some W_5edac.
Proof. vm_refl. Qed.
Lemma D_5edac : decode_any W_5edac = Some (Load SZ4 false 15 15 1936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edb0 : bv 32 := 0x0105b02f.
Lemma F_5edb0 : fetch_word Asan.M.loaded_segments (0x5ee00 : word) = Some W_5edb0.
Proof. vm_refl. Qed.
Lemma D_5edb0 : decode_any W_5edb0 = Some (Amo AMO_ADD AD false false 0 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edb4 : bv 32 := 0x00108597.
Lemma F_5edb4 : fetch_word Asan.M.loaded_segments (0x5ee04 : word) = Some W_5edb4.
Proof. vm_refl. Qed.
Lemma D_5edb4 : decode_any W_5edb4 = Some (Auipc 11 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edb8 : bv 32 := 0xab45b583.
Lemma F_5edb8 : fetch_word Asan.M.loaded_segments (0x5ee08 : word) = Some W_5edb8.
Proof. vm_refl. Qed.
Lemma D_5edb8 : decode_any W_5edb8 = Some (Load SZ8 true 11 11 2740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edbc : bv 32 := 0x00300813.
Lemma F_5edbc : fetch_word Asan.M.loaded_segments (0x5ee0c : word) = Some W_5edbc.
Proof. vm_refl. Qed.
Lemma D_5edbc : decode_any W_5edbc = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edc0 : bv 32 := 0x00479793.
Lemma F_5edc0 : fetch_word Asan.M.loaded_segments (0x5ee10 : word) = Some W_5edc0.
Proof. vm_refl. Qed.
Lemma D_5edc0 : decode_any W_5edc0 = Some (ShiftImm ALU_SLL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edc4 : bv 32 := 0x02381813.
Lemma F_5edc4 : fetch_word Asan.M.loaded_segments (0x5ee14 : word) = Some W_5edc4.
Proof. vm_refl. Qed.
Lemma D_5edc4 : decode_any W_5edc4 = Some (ShiftImm ALU_SLL 16 16 35, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edc8 : bv 32 := 0x010585b3.
Lemma F_5edc8 : fetch_word Asan.M.loaded_segments (0x5ee18 : word) = Some W_5edc8.
Proof. vm_refl. Qed.
Lemma D_5edc8 : decode_any W_5edc8 = Some (Op ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edcc : bv 32 := 0x00b785b3.
Lemma F_5edcc : fetch_word Asan.M.loaded_segments (0x5ee1c : word) = Some W_5edcc.
Proof. vm_refl. Qed.
Lemma D_5edcc : decode_any W_5edcc = Some (Op ALU_ADD 11 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edd0 : bv 32 := 0x0e058863.
Lemma F_5edd0 : fetch_word Asan.M.loaded_segments (0x5ee20 : word) = Some W_5edd0.
Proof. vm_refl. Qed.
Lemma D_5edd0 : decode_any W_5edd0 = Some (Branch BC_EQ 11 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edd4 : bv 32 := 0x00100613.
Lemma F_5edd4 : fetch_word Asan.M.loaded_segments (0x5ee24 : word) = Some W_5edd4.
Proof. vm_refl. Qed.
Lemma D_5edd4 : decode_any W_5edd4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edd8 : bv 32 := 0x000027b7.
Lemma F_5edd8 : fetch_word Asan.M.loaded_segments (0x5ee28 : word) = Some W_5edd8.
Proof. vm_refl. Qed.
Lemma D_5edd8 : decode_any W_5edd8 = Some (Lui 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eddc : bv 32 := 0x00f70733.
Lemma F_5eddc : fetch_word Asan.M.loaded_segments (0x5ee2c : word) = Some W_5eddc.
Proof. vm_refl. Qed.
Lemma D_5eddc : decode_any W_5eddc = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ede0 : bv 32 := 0x00053783.
Lemma F_5ede0 : fetch_word Asan.M.loaded_segments (0x5ee30 : word) = Some W_5ede0.
Proof. vm_refl. Qed.
Lemma D_5ede0 : decode_any W_5ede0 = Some (Load SZ8 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ede4 : bv 32 := 0x0005b023.
Lemma F_5ede4 : fetch_word Asan.M.loaded_segments (0x5ee34 : word) = Some W_5ede4.
Proof. vm_refl. Qed.
Lemma D_5ede4 : decode_any W_5ede4 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ede8 : bv 32 := 0x00e5b423.
Lemma F_5ede8 : fetch_word Asan.M.loaded_segments (0x5ee38 : word) = Some W_5ede8.
Proof. vm_refl. Qed.
Lemma D_5ede8 : decode_any W_5ede8 = Some (Store SZ8 11 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edec : bv 32 := 0x00c5b823.
Lemma F_5edec : fetch_word Asan.M.loaded_segments (0x5ee3c : word) = Some W_5edec.
Proof. vm_refl. Qed.
Lemma D_5edec : decode_any W_5edec = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edf0 : bv 32 := 0x00d5bc23.
Lemma F_5edf0 : fetch_word Asan.M.loaded_segments (0x5ee40 : word) = Some W_5edf0.
Proof. vm_refl. Qed.
Lemma D_5edf0 : decode_any W_5edf0 = Some (Store SZ8 11 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edf4 : bv 32 := 0x02078e63.
Lemma F_5edf4 : fetch_word Asan.M.loaded_segments (0x5ee44 : word) = Some W_5edf4.
Proof. vm_refl. Qed.
Lemma D_5edf4 : decode_any W_5edf4 = Some (Branch BC_EQ 15 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edf8 : bv 32 := 0x01053603.
Lemma F_5edf8 : fetch_word Asan.M.loaded_segments (0x5ee48 : word) = Some W_5edf8.
Proof. vm_refl. Qed.
Lemma D_5edf8 : decode_any W_5edf8 = Some (Load SZ8 true 12 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edfc : bv 32 := 0x00b63023.
Lemma F_5edfc : fetch_word Asan.M.loaded_segments (0x5ee4c : word) = Some W_5edfc.
Proof. vm_refl. Qed.
Lemma D_5edfc : decode_any W_5edfc = Some (Store SZ8 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee00 : bv 32 := 0x00178613.
Lemma F_5ee00 : fetch_word Asan.M.loaded_segments (0x5ee50 : word) = Some W_5ee00.
Proof. vm_refl. Qed.
Lemma D_5ee00 : decode_any W_5ee00 = Some (OpImm ALU_ADD 12 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee04 : bv 32 := 0x0300006f.
Lemma F_5ee04 : fetch_word Asan.M.loaded_segments (0x5ee54 : word) = Some W_5ee04.
Proof. vm_refl. Qed.
Lemma D_5ee04 : decode_any W_5ee04 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee08 : bv 32 := 0x0d17fc63.
Lemma F_5ee08 : fetch_word Asan.M.loaded_segments (0x5ee58 : word) = Some W_5ee08.
Proof. vm_refl. Qed.
Lemma D_5ee08 : decode_any W_5ee08 = Some (Branch BC_GEU 15 17 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee0c : bv 32 := 0x00883583.
Lemma F_5ee0c : fetch_word Asan.M.loaded_segments (0x5ee5c : word) = Some W_5ee0c.
Proof. vm_refl. Qed.
Lemma D_5ee0c : decode_any W_5ee0c = Some (Load SZ8 true 11 16 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee10 : bv 32 := 0x00379613.
Lemma F_5ee10 : fetch_word Asan.M.loaded_segments (0x5ee60 : word) = Some W_5ee10.
Proof. vm_refl. Qed.
Lemma D_5ee10 : decode_any W_5ee10 = Some (ShiftImm ALU_SLL 12 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee14 : bv 32 := 0x00178793.
Lemma F_5ee14 : fetch_word Asan.M.loaded_segments (0x5ee64 : word) = Some W_5ee14.
Proof. vm_refl. Qed.
Lemma D_5ee14 : decode_any W_5ee14 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee18 : bv 32 := 0x00c80633.
Lemma F_5ee18 : fetch_word Asan.M.loaded_segments (0x5ee68 : word) = Some W_5ee18.
Proof. vm_refl. Qed.
Lemma D_5ee18 : decode_any W_5ee18 = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee1c : bv 32 := 0x00e585b3.
Lemma F_5ee1c : fetch_word Asan.M.loaded_segments (0x5ee6c : word) = Some W_5ee1c.
Proof. vm_refl. Qed.
Lemma D_5ee1c : decode_any W_5ee1c = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee20 : bv 32 := 0x00b83423.
Lemma F_5ee20 : fetch_word Asan.M.loaded_segments (0x5ee70 : word) = Some W_5ee20.
Proof. vm_refl. Qed.
Lemma D_5ee20 : decode_any W_5ee20 = Some (Store SZ8 16 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee24 : bv 32 := 0x00f83823.
Lemma F_5ee24 : fetch_word Asan.M.loaded_segments (0x5ee74 : word) = Some W_5ee24.
Proof. vm_refl. Qed.
Lemma D_5ee24 : decode_any W_5ee24 = Some (Store SZ8 16 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee28 : bv 32 := 0x00d63c23.
Lemma F_5ee28 : fetch_word Asan.M.loaded_segments (0x5ee78 : word) = Some W_5ee28.
Proof. vm_refl. Qed.
Lemma D_5ee28 : decode_any W_5ee28 = Some (Store SZ8 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee2c : bv 32 := 0x0100006f.
Lemma F_5ee2c : fetch_word Asan.M.loaded_segments (0x5ee7c : word) = Some W_5ee2c.
Proof. vm_refl. Qed.
Lemma D_5ee2c : decode_any W_5ee2c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee30 : bv 32 := 0x00b53423.
Lemma F_5ee30 : fetch_word Asan.M.loaded_segments (0x5ee80 : word) = Some W_5ee30.
Proof. vm_refl. Qed.
Lemma D_5ee30 : decode_any W_5ee30 = Some (Store SZ8 10 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee34 : bv 32 := 0x00c53023.
Lemma F_5ee34 : fetch_word Asan.M.loaded_segments (0x5ee84 : word) = Some W_5ee34.
Proof. vm_refl. Qed.
Lemma D_5ee34 : decode_any W_5ee34 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee38 : bv 32 := 0x00b53823.
Lemma F_5ee38 : fetch_word Asan.M.loaded_segments (0x5ee88 : word) = Some W_5ee38.
Proof. vm_refl. Qed.
Lemma D_5ee38 : decode_any W_5ee38 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee3c : bv 32 := 0x01853583.
Lemma F_5ee3c : fetch_word Asan.M.loaded_segments (0x5ee8c : word) = Some W_5ee3c.
Proof. vm_refl. Qed.
Lemma D_5ee3c : decode_any W_5ee3c = Some (Load SZ8 true 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee40 : bv 32 := 0x00e585b3.
Lemma F_5ee40 : fetch_word Asan.M.loaded_segments (0x5ee90 : word) = Some W_5ee40.
Proof. vm_refl. Qed.
Lemma D_5ee40 : decode_any W_5ee40 = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee44 : bv 32 := 0x00b53c23.
Lemma F_5ee44 : fetch_word Asan.M.loaded_segments (0x5ee94 : word) = Some W_5ee44.
Proof. vm_refl. Qed.
Lemma D_5ee44 : decode_any W_5ee44 = Some (Store SZ8 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee48 : bv 32 := 0x03813083.
Lemma F_5ee48 : fetch_word Asan.M.loaded_segments (0x5ee98 : word) = Some W_5ee48.
Proof. vm_refl. Qed.
Lemma D_5ee48 : decode_any W_5ee48 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee4c : bv 32 := 0x03013403.
Lemma F_5ee4c : fetch_word Asan.M.loaded_segments (0x5ee9c : word) = Some W_5ee4c.
Proof. vm_refl. Qed.
Lemma D_5ee4c : decode_any W_5ee4c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee50 : bv 32 := 0x02813483.
Lemma F_5ee50 : fetch_word Asan.M.loaded_segments (0x5eea0 : word) = Some W_5ee50.
Proof. vm_refl. Qed.
Lemma D_5ee50 : decode_any W_5ee50 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee54 : bv 32 := 0x02013903.
Lemma F_5ee54 : fetch_word Asan.M.loaded_segments (0x5eea4 : word) = Some W_5ee54.
Proof. vm_refl. Qed.
Lemma D_5ee54 : decode_any W_5ee54 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee58 : bv 32 := 0x01813983.
Lemma F_5ee58 : fetch_word Asan.M.loaded_segments (0x5eea8 : word) = Some W_5ee58.
Proof. vm_refl. Qed.
Lemma D_5ee58 : decode_any W_5ee58 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee5c : bv 32 := 0x01013a03.
Lemma F_5ee5c : fetch_word Asan.M.loaded_segments (0x5eeac : word) = Some W_5ee5c.
Proof. vm_refl. Qed.
Lemma D_5ee5c : decode_any W_5ee5c = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee60 : bv 32 := 0x00813a83.
Lemma F_5ee60 : fetch_word Asan.M.loaded_segments (0x5eeb0 : word) = Some W_5ee60.
Proof. vm_refl. Qed.
Lemma D_5ee60 : decode_any W_5ee60 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee64 : bv 32 := 0x04010113.
Lemma F_5ee64 : fetch_word Asan.M.loaded_segments (0x5eeb4 : word) = Some W_5ee64.
Proof. vm_refl. Qed.
Lemma D_5ee64 : decode_any W_5ee64 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee68 : bv 32 := 0x00008067.
Lemma F_5ee68 : fetch_word Asan.M.loaded_segments (0x5eeb8 : word) = Some W_5ee68.
Proof. vm_refl. Qed.
Lemma D_5ee68 : decode_any W_5ee68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee6c : bv 32 := 0x78058413.
Lemma F_5ee6c : fetch_word Asan.M.loaded_segments (0x5eebc : word) = Some W_5ee6c.
Proof. vm_refl. Qed.
Lemma D_5ee6c : decode_any W_5ee6c = Some (OpImm ALU_ADD 8 11 1920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee70 : bv 32 := 0x00108797.
Lemma F_5ee70 : fetch_word Asan.M.loaded_segments (0x5eec0 : word) = Some W_5ee70.
Proof. vm_refl. Qed.
Lemma D_5ee70 : decode_any W_5ee70 = Some (Auipc 15 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee74 : bv 32 := 0x9d878793.
Lemma F_5ee74 : fetch_word Asan.M.loaded_segments (0x5eec4 : word) = Some W_5ee74.
Proof. vm_refl. Qed.
Lemma D_5ee74 : decode_any W_5ee74 = Some (OpImm ALU_ADD 15 15 2520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee78 : bv 32 := 0x00068913.
Lemma F_5ee78 : fetch_word Asan.M.loaded_segments (0x5eec8 : word) = Some W_5ee78.
Proof. vm_refl. Qed.
Lemma D_5ee78 : decode_any W_5ee78 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee7c : bv 32 := 0x01800693.
Lemma F_5ee7c : fetch_word Asan.M.loaded_segments (0x5eecc : word) = Some W_5ee7c.
Proof. vm_refl. Qed.
Lemma D_5ee7c : decode_any W_5ee7c = Some (OpImm ALU_ADD 13 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee80 : bv 32 := 0x00050993.
Lemma F_5ee80 : fetch_word Asan.M.loaded_segments (0x5eed0 : word) = Some W_5ee80.
Proof. vm_refl. Qed.
Lemma D_5ee80 : decode_any W_5ee80 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee84 : bv 32 := 0x00058493.
Lemma F_5ee84 : fetch_word Asan.M.loaded_segments (0x5eed4 : word) = Some W_5ee84.
Proof. vm_refl. Qed.
Lemma D_5ee84 : decode_any W_5ee84 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee88 : bv 32 := 0x00058513.
Lemma F_5ee88 : fetch_word Asan.M.loaded_segments (0x5eed8 : word) = Some W_5ee88.
Proof. vm_refl. Qed.
Lemma D_5ee88 : decode_any W_5ee88 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee8c : bv 32 := 0x00040593.
Lemma F_5ee8c : fetch_word Asan.M.loaded_segments (0x5eedc : word) = Some W_5ee8c.
Proof. vm_refl. Qed.
Lemma D_5ee8c : decode_any W_5ee8c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee90 : bv 32 := 0x00060a13.
Lemma F_5ee90 : fetch_word Asan.M.loaded_segments (0x5eee0 : word) = Some W_5ee90.
Proof. vm_refl. Qed.
Lemma D_5ee90 : decode_any W_5ee90 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee94 : bv 32 := 0x00078613.
Lemma F_5ee94 : fetch_word Asan.M.loaded_segments (0x5eee4 : word) = Some W_5ee94.
Proof. vm_refl. Qed.
Lemma D_5ee94 : decode_any W_5ee94 = Some (OpImm ALU_ADD 12 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee98 : bv 32 := 0x00070a93.
Lemma F_5ee98 : fetch_word Asan.M.loaded_segments (0x5eee8 : word) = Some W_5ee98.
Proof. vm_refl. Qed.
Lemma D_5ee98 : decode_any W_5ee98 = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee9c : bv 32 := 0x7e4000ef.
Lemma F_5ee9c : fetch_word Asan.M.loaded_segments (0x5eeec : word) = Some W_5ee9c.
Proof. vm_refl. Qed.
Lemma D_5ee9c : decode_any W_5ee9c = Some (Jal 1 2020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eea0 : bv 32 := 0x000a0613.
Lemma F_5eea0 : fetch_word Asan.M.loaded_segments (0x5eef0 : word) = Some W_5eea0.
Proof. vm_refl. Qed.
Lemma D_5eea0 : decode_any W_5eea0 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eea4 : bv 32 := 0x00050e63.
Lemma F_5eea4 : fetch_word Asan.M.loaded_segments (0x5eef4 : word) = Some W_5eea4.
Proof. vm_refl. Qed.
Lemma D_5eea4 : decode_any W_5eea4 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eea8 : bv 32 := 0x00090693.
Lemma F_5eea8 : fetch_word Asan.M.loaded_segments (0x5eef8 : word) = Some W_5eea8.
Proof. vm_refl. Qed.
Lemma D_5eea8 : decode_any W_5eea8 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eeac : bv 32 := 0x000a8713.
Lemma F_5eeac : fetch_word Asan.M.loaded_segments (0x5eefc : word) = Some W_5eeac.
Proof. vm_refl. Qed.
Lemma D_5eeac : decode_any W_5eeac = Some (OpImm ALU_ADD 14 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eeb0 : bv 32 := 0x00098513.
Lemma F_5eeb0 : fetch_word Asan.M.loaded_segments (0x5ef00 : word) = Some W_5eeb0.
Proof. vm_refl. Qed.
Lemma D_5eeb0 : decode_any W_5eeb0 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eeb4 : bv 32 := 0x00042783.
Lemma F_5eeb4 : fetch_word Asan.M.loaded_segments (0x5ef04 : word) = Some W_5eeb4.
Proof. vm_refl. Qed.
Lemma D_5eeb4 : decode_any W_5eeb4 = Some (Load SZ4 true 15 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eeb8 : bv 32 := 0x00048593.
Lemma F_5eeb8 : fetch_word Asan.M.loaded_segments (0x5ef08 : word) = Some W_5eeb8.
Proof. vm_refl. Qed.
Lemma D_5eeb8 : decode_any W_5eeb8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eebc : bv 32 := 0xed1ff06f.
Lemma F_5eebc : fetch_word Asan.M.loaded_segments (0x5ef0c : word) = Some W_5eebc.
Proof. vm_refl. Qed.
Lemma D_5eebc : decode_any W_5eebc = Some (Jal 0 2096848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ef30 : bv 32 := 0xfd010113.
Lemma F_5ef30 : fetch_word Asan.M.loaded_segments (0x5ef80 : word) = Some W_5ef30.
Proof. vm_refl. Qed.
Lemma D_5ef30 : decode_any W_5ef30 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ef34 : bv 32 := 0x02113423.
Lemma F_5ef34 : fetch_word Asan.M.loaded_segments (0x5ef84 : word) = Some W_5ef34.
Proof. vm_refl. Qed.
Lemma D_5ef34 : decode_any W_5ef34 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ef38 : bv 32 := 0x02813023.
Lemma F_5ef38 : fetch_word Asan.M.loaded_segments (0x5ef88 : word) = Some W_5ef38.
Proof. vm_refl. Qed.
Lemma D_5ef38 : decode_any W_5ef38 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ef3c : bv 32 := 0x00913c23.
Lemma F_5ef3c : fetch_word Asan.M.loaded_segments (0x5ef8c : word) = Some W_5ef3c.
Proof. vm_refl. Qed.
Lemma D_5ef3c : decode_any W_5ef3c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ef40 : bv 32 := 0x01213823.
Lemma F_5ef40 : fetch_word Asan.M.loaded_segments (0x5ef90 : word) = Some W_5ef40.
Proof. vm_refl. Qed.
Lemma D_5ef40 : decode_any W_5ef40 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ef44 : bv 32 := 0x01313423.
Lemma F_5ef44 : fetch_word Asan.M.loaded_segments (0x5ef94 : word) = Some W_5ef44.
Proof. vm_refl. Qed.
Lemma D_5ef44 : decode_any W_5ef44 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ef48 : bv 32 := 0x01413023.
Lemma F_5ef48 : fetch_word Asan.M.loaded_segments (0x5ef98 : word) = Some W_5ef48.
Proof. vm_refl. Qed.
Lemma D_5ef48 : decode_any W_5ef48 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ef4c : bv 32 := 0x00163713.
Lemma F_5ef4c : fetch_word Asan.M.loaded_segments (0x5ef9c : word) = Some W_5ef4c.
Proof. vm_refl. Qed.
Lemma D_5ef4c : decode_any W_5ef4c = Some (OpImm ALU_SLTU 14 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ef50 : bv 32 := 0x00e60633.
Lemma F_5ef50 : fetch_word Asan.M.loaded_segments (0x5efa0 : word) = Some W_5ef50.
Proof. vm_refl. Qed.
Lemma D_5ef50 : decode_any W_5ef50 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ef54 : bv 32 := 0xfff64713.
Lemma F_5ef54 : fetch_word Asan.M.loaded_segments (0x5efa4 : word) = Some W_5ef54.
Proof. vm_refl. Qed.
Lemma D_5ef54 : decode_any W_5ef54 = Some (OpImm ALU_XOR 14 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ef58 : bv 32 := 0x02d77263.
Lemma F_5ef58 : fetch_word Asan.M.loaded_segments (0x5efa8 : word) = Some W_5ef58.
Proof. vm_refl. Qed.
Lemma D_5ef58 : decode_any W_5ef58 = Some (Branch BC_GEU 14 13 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ef7c : bv 32 := 0x00900793.
Lemma F_5ef7c : fetch_word Asan.M.loaded_segments (0x5efcc : word) = Some W_5ef7c.
Proof. vm_refl. Qed.
Lemma D_5ef7c : decode_any W_5ef7c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ef80 : bv 32 := 0x00060713.
Lemma F_5ef80 : fetch_word Asan.M.loaded_segments (0x5efd0 : word) = Some W_5ef80.
Proof. vm_refl. Qed.
Lemma D_5ef80 : decode_any W_5ef80 = Some (OpImm ALU_ADD 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ef84 : bv 32 := 0x02f6e063.
Lemma F_5ef84 : fetch_word Asan.M.loaded_segments (0x5efd4 : word) = Some W_5ef84.
Proof. vm_refl. Qed.
Lemma D_5ef84 : decode_any W_5ef84 = Some (Branch BC_LTU 13 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efa4 : bv 32 := 0x000107b7.
Lemma F_5efa4 : fetch_word Asan.M.loaded_segments (0x5eff4 : word) = Some W_5efa4.
Proof. vm_refl. Qed.
Lemma D_5efa4 : decode_any W_5efa4 = Some (Lui 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efa8 : bv 32 := 0x00d7ee63.
Lemma F_5efa8 : fetch_word Asan.M.loaded_segments (0x5eff8 : word) = Some W_5efa8.
Proof. vm_refl. Qed.
Lemma D_5efa8 : decode_any W_5efa8 = Some (Branch BC_LTU 15 13 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efac : bv 32 := 0x00e7ec63.
Lemma F_5efac : fetch_word Asan.M.loaded_segments (0x5effc : word) = Some W_5efac.
Proof. vm_refl. Qed.
Lemma D_5efac : decode_any W_5efac = Some (Branch BC_LTU 15 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efb0 : bv 32 := 0x20000613.
Lemma F_5efb0 : fetch_word Asan.M.loaded_segments (0x5f000 : word) = Some W_5efb0.
Proof. vm_refl. Qed.
Lemma D_5efb0 : decode_any W_5efb0 = Some (OpImm ALU_ADD 12 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efb4 : bv 32 := 0x02e66a63.
Lemma F_5efb4 : fetch_word Asan.M.loaded_segments (0x5f004 : word) = Some W_5efb4.
Proof. vm_refl. Qed.
Lemma D_5efb4 : decode_any W_5efb4 = Some (Branch BC_LTU 12 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efb8 : bv 32 := 0x01f70713.
Lemma F_5efb8 : fetch_word Asan.M.loaded_segments (0x5f008 : word) = Some W_5efb8.
Proof. vm_refl. Qed.
Lemma D_5efb8 : decode_any W_5efb8 = Some (OpImm ALU_ADD 14 14 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efbc : bv 32 := 0x00575413.
Lemma F_5efbc : fetch_word Asan.M.loaded_segments (0x5f00c : word) = Some W_5efbc.
Proof. vm_refl. Qed.
Lemma D_5efbc : decode_any W_5efbc = Some (ShiftImm ALU_SRL 8 14 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efc0 : bv 32 := 0x1040006f.
Lemma F_5efc0 : fetch_word Asan.M.loaded_segments (0x5f010 : word) = Some W_5efc0.
Proof. vm_refl. Qed.
Lemma D_5efc0 : decode_any W_5efc0 = Some (Jal 0 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efc4 : bv 32 := 0x04050713.
Lemma F_5efc4 : fetch_word Asan.M.loaded_segments (0x5f014 : word) = Some W_5efc4.
Proof. vm_refl. Qed.
Lemma D_5efc4 : decode_any W_5efc4 = Some (OpImm ALU_ADD 14 10 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efc8 : bv 32 := 0x2b050593.
Lemma F_5efc8 : fetch_word Asan.M.loaded_segments (0x5f018 : word) = Some W_5efc8.
Proof. vm_refl. Qed.
Lemma D_5efc8 : decode_any W_5efc8 = Some (OpImm ALU_ADD 11 10 688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efcc : bv 32 := 0x00070513.
Lemma F_5efcc : fetch_word Asan.M.loaded_segments (0x5f01c : word) = Some W_5efcc.
Proof. vm_refl. Qed.
Lemma D_5efcc : decode_any W_5efcc = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efd0 : bv 32 := 0x00068413.
Lemma F_5efd0 : fetch_word Asan.M.loaded_segments (0x5f020 : word) = Some W_5efd0.
Proof. vm_refl. Qed.
Lemma D_5efd0 : decode_any W_5efd0 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efd4 : bv 32 := 0x234000ef.
Lemma F_5efd4 : fetch_word Asan.M.loaded_segments (0x5f024 : word) = Some W_5efd4.
Proof. vm_refl. Qed.
Lemma D_5efd4 : decode_any W_5efd4 = Some (Jal 1 564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efd8 : bv 32 := 0x00040693.
Lemma F_5efd8 : fetch_word Asan.M.loaded_segments (0x5f028 : word) = Some W_5efd8.
Proof. vm_refl. Qed.
Lemma D_5efd8 : decode_any W_5efd8 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efdc : bv 32 := 0x00900593.
Lemma F_5efdc : fetch_word Asan.M.loaded_segments (0x5f02c : word) = Some W_5efdc.
Proof. vm_refl. Qed.
Lemma D_5efdc : decode_any W_5efdc = Some (OpImm ALU_ADD 11 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efe0 : bv 32 := 0x14b47463.
Lemma F_5efe0 : fetch_word Asan.M.loaded_segments (0x5f030 : word) = Some W_5efe0.
Proof. vm_refl. Qed.
Lemma D_5efe0 : decode_any W_5efe0 = Some (Branch BC_GEU 8 11 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efe4 : bv 32 := 0x1500006f.
Lemma F_5efe4 : fetch_word Asan.M.loaded_segments (0x5f034 : word) = Some W_5efe4.
Proof. vm_refl. Qed.
Lemma D_5efe4 : decode_any W_5efe4 = Some (Jal 0 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efe8 : bv 32 := 0x00175613.
Lemma F_5efe8 : fetch_word Asan.M.loaded_segments (0x5f038 : word) = Some W_5efe8.
Proof. vm_refl. Qed.
Lemma D_5efe8 : decode_any W_5efe8 = Some (ShiftImm ALU_SRL 12 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5efec : bv 32 := 0x555557b7.
Lemma F_5efec : fetch_word Asan.M.loaded_segments (0x5f03c : word) = Some W_5efec.
Proof. vm_refl. Qed.
Lemma D_5efec : decode_any W_5efec = Some (Lui 15 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eff0 : bv 32 := 0x33333837.
Lemma F_5eff0 : fetch_word Asan.M.loaded_segments (0x5f040 : word) = Some W_5eff0.
Proof. vm_refl. Qed.
Lemma D_5eff0 : decode_any W_5eff0 = Some (Lui 16 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eff4 : bv 32 := 0x0f0f18b7.
Lemma F_5eff4 : fetch_word Asan.M.loaded_segments (0x5f044 : word) = Some W_5eff4.
Proof. vm_refl. Qed.
Lemma D_5eff4 : decode_any W_5eff4 = Some (Lui 17 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eff8 : bv 32 := 0x010102b7.
Lemma F_5eff8 : fetch_word Asan.M.loaded_segments (0x5f048 : word) = Some W_5eff8.
Proof. vm_refl. Qed.
Lemma D_5eff8 : decode_any W_5eff8 = Some (Lui 5 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5effc : bv 32 := 0x00c76633.
Lemma F_5effc : fetch_word Asan.M.loaded_segments (0x5f04c : word) = Some W_5effc.
Proof. vm_refl. Qed.
Lemma D_5effc : decode_any W_5effc = Some (Op ALU_OR 12 14 12, 4%Z).
Proof. vm_refl. Qed.

