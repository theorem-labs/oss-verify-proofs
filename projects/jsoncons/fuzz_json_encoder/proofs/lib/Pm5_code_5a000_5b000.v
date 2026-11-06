(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5ad74 : bv 32 := 0x00060793.
Lemma F_5ad74 : fetch_word AsanUbsan.M.loaded_segments (0x5adbc : word) = Some W_5ad74.
Proof. vm_refl. Qed.
Lemma D_5ad74 : decode_any W_5ad74 = Some (OpImm ALU_ADD 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad78 : bv 32 := 0x00058713.
Lemma F_5ad78 : fetch_word AsanUbsan.M.loaded_segments (0x5adc0 : word) = Some W_5ad78.
Proof. vm_refl. Qed.
Lemma D_5ad78 : decode_any W_5ad78 = Some (OpImm ALU_ADD 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad7c : bv 32 := 0x0010f597.
Lemma F_5ad7c : fetch_word AsanUbsan.M.loaded_segments (0x5adc4 : word) = Some W_5ad7c.
Proof. vm_refl. Qed.
Lemma D_5ad7c : decode_any W_5ad7c = Some (Auipc 11 271, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad80 : bv 32 := 0x39458593.
Lemma F_5ad80 : fetch_word AsanUbsan.M.loaded_segments (0x5adc8 : word) = Some W_5ad80.
Proof. vm_refl. Qed.
Lemma D_5ad80 : decode_any W_5ad80 = Some (OpImm ALU_ADD 11 11 916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad84 : bv 32 := 0x00050613.
Lemma F_5ad84 : fetch_word AsanUbsan.M.loaded_segments (0x5adcc : word) = Some W_5ad84.
Proof. vm_refl. Qed.
Lemma D_5ad84 : decode_any W_5ad84 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad88 : bv 32 := 0x00058513.
Lemma F_5ad88 : fetch_word AsanUbsan.M.loaded_segments (0x5add0 : word) = Some W_5ad88.
Proof. vm_refl. Qed.
Lemma D_5ad88 : decode_any W_5ad88 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad8c : bv 32 := 0x00060593.
Lemma F_5ad8c : fetch_word AsanUbsan.M.loaded_segments (0x5add4 : word) = Some W_5ad8c.
Proof. vm_refl. Qed.
Lemma D_5ad8c : decode_any W_5ad8c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad90 : bv 32 := 0x00000613.
Lemma F_5ad90 : fetch_word AsanUbsan.M.loaded_segments (0x5add8 : word) = Some W_5ad90.
Proof. vm_refl. Qed.
Lemma D_5ad90 : decode_any W_5ad90 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad94 : bv 32 := 0x00000693.
Lemma F_5ad94 : fetch_word AsanUbsan.M.loaded_segments (0x5addc : word) = Some W_5ad94.
Proof. vm_refl. Qed.
Lemma D_5ad94 : decode_any W_5ad94 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad98 : bv 32 := 0x0040006f.
Lemma F_5ad98 : fetch_word AsanUbsan.M.loaded_segments (0x5ade0 : word) = Some W_5ad98.
Proof. vm_refl. Qed.
Lemma D_5ad98 : decode_any W_5ad98 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad9c : bv 32 := 0xfc010113.
Lemma F_5ad9c : fetch_word AsanUbsan.M.loaded_segments (0x5ade4 : word) = Some W_5ad9c.
Proof. vm_refl. Qed.
Lemma D_5ad9c : decode_any W_5ad9c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ada0 : bv 32 := 0x02113c23.
Lemma F_5ada0 : fetch_word AsanUbsan.M.loaded_segments (0x5ade8 : word) = Some W_5ada0.
Proof. vm_refl. Qed.
Lemma D_5ada0 : decode_any W_5ada0 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ada4 : bv 32 := 0x02813823.
Lemma F_5ada4 : fetch_word AsanUbsan.M.loaded_segments (0x5adec : word) = Some W_5ada4.
Proof. vm_refl. Qed.
Lemma D_5ada4 : decode_any W_5ada4 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ada8 : bv 32 := 0x02913423.
Lemma F_5ada8 : fetch_word AsanUbsan.M.loaded_segments (0x5adf0 : word) = Some W_5ada8.
Proof. vm_refl. Qed.
Lemma D_5ada8 : decode_any W_5ada8 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adac : bv 32 := 0x03213023.
Lemma F_5adac : fetch_word AsanUbsan.M.loaded_segments (0x5adf4 : word) = Some W_5adac.
Proof. vm_refl. Qed.
Lemma D_5adac : decode_any W_5adac = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adb0 : bv 32 := 0x01313c23.
Lemma F_5adb0 : fetch_word AsanUbsan.M.loaded_segments (0x5adf8 : word) = Some W_5adb0.
Proof. vm_refl. Qed.
Lemma D_5adb0 : decode_any W_5adb0 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adb4 : bv 32 := 0x01413823.
Lemma F_5adb4 : fetch_word AsanUbsan.M.loaded_segments (0x5adfc : word) = Some W_5adb4.
Proof. vm_refl. Qed.
Lemma D_5adb4 : decode_any W_5adb4 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adb8 : bv 32 := 0x01513423.
Lemma F_5adb8 : fetch_word AsanUbsan.M.loaded_segments (0x5ae00 : word) = Some W_5adb8.
Proof. vm_refl. Qed.
Lemma D_5adb8 : decode_any W_5adb8 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adbc : bv 32 := 0x01613023.
Lemma F_5adbc : fetch_word AsanUbsan.M.loaded_segments (0x5ae04 : word) = Some W_5adbc.
Proof. vm_refl. Qed.
Lemma D_5adbc : decode_any W_5adbc = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adc0 : bv 32 := 0x02058e63.
Lemma F_5adc0 : fetch_word AsanUbsan.M.loaded_segments (0x5ae08 : word) = Some W_5adc0.
Proof. vm_refl. Qed.
Lemma D_5adc0 : decode_any W_5adc0 = Some (Branch BC_EQ 11 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adc4 : bv 32 := 0x00078a13.
Lemma F_5adc4 : fetch_word AsanUbsan.M.loaded_segments (0x5ae0c : word) = Some W_5adc4.
Proof. vm_refl. Qed.
Lemma D_5adc4 : decode_any W_5adc4 = Some (OpImm ALU_ADD 20 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adc8 : bv 32 := 0x00070413.
Lemma F_5adc8 : fetch_word AsanUbsan.M.loaded_segments (0x5ae10 : word) = Some W_5adc8.
Proof. vm_refl. Qed.
Lemma D_5adc8 : decode_any W_5adc8 = Some (OpImm ALU_ADD 8 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adcc : bv 32 := 0x00058493.
Lemma F_5adcc : fetch_word AsanUbsan.M.loaded_segments (0x5ae14 : word) = Some W_5adcc.
Proof. vm_refl. Qed.
Lemma D_5adcc : decode_any W_5adcc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5add0 : bv 32 := 0x00050993.
Lemma F_5add0 : fetch_word AsanUbsan.M.loaded_segments (0x5ae18 : word) = Some W_5add0.
Proof. vm_refl. Qed.
Lemma D_5add0 : decode_any W_5add0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5add4 : bv 32 := 0x00060a93.
Lemma F_5add4 : fetch_word AsanUbsan.M.loaded_segments (0x5ae1c : word) = Some W_5add4.
Proof. vm_refl. Qed.
Lemma D_5add4 : decode_any W_5add4 = Some (OpImm ALU_ADD 21 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5add8 : bv 32 := 0x00068b13.
Lemma F_5add8 : fetch_word AsanUbsan.M.loaded_segments (0x5ae20 : word) = Some W_5add8.
Proof. vm_refl. Qed.
Lemma D_5add8 : decode_any W_5add8 = Some (OpImm ALU_ADD 22 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5addc : bv 32 := 0xff058913.
Lemma F_5addc : fetch_word AsanUbsan.M.loaded_segments (0x5ae24 : word) = Some W_5addc.
Proof. vm_refl. Qed.
Lemma D_5addc : decode_any W_5addc = Some (OpImm ALU_ADD 18 11 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ade0 : bv 32 := 0x00058513.
Lemma F_5ade0 : fetch_word AsanUbsan.M.loaded_segments (0x5ae28 : word) = Some W_5ade0.
Proof. vm_refl. Qed.
Lemma D_5ade0 : decode_any W_5ade0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ade4 : bv 32 := 0x1c4360ef.
Lemma F_5ade4 : fetch_word AsanUbsan.M.loaded_segments (0x5ae2c : word) = Some W_5ade4.
Proof. vm_refl. Qed.
Lemma D_5ade4 : decode_any W_5ade4 = Some (Jal 1 221636, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ade8 : bv 32 := 0x02050e63.
Lemma F_5ade8 : fetch_word AsanUbsan.M.loaded_segments (0x5ae30 : word) = Some W_5ade8.
Proof. vm_refl. Qed.
Lemma D_5ade8 : decode_any W_5ade8 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adfc : bv 32 := 0x03813083.
Lemma F_5adfc : fetch_word AsanUbsan.M.loaded_segments (0x5ae44 : word) = Some W_5adfc.
Proof. vm_refl. Qed.
Lemma D_5adfc : decode_any W_5adfc = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae00 : bv 32 := 0x03013403.
Lemma F_5ae00 : fetch_word AsanUbsan.M.loaded_segments (0x5ae48 : word) = Some W_5ae00.
Proof. vm_refl. Qed.
Lemma D_5ae00 : decode_any W_5ae00 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae04 : bv 32 := 0x02813483.
Lemma F_5ae04 : fetch_word AsanUbsan.M.loaded_segments (0x5ae4c : word) = Some W_5ae04.
Proof. vm_refl. Qed.
Lemma D_5ae04 : decode_any W_5ae04 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae08 : bv 32 := 0x02013903.
Lemma F_5ae08 : fetch_word AsanUbsan.M.loaded_segments (0x5ae50 : word) = Some W_5ae08.
Proof. vm_refl. Qed.
Lemma D_5ae08 : decode_any W_5ae08 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae0c : bv 32 := 0x01813983.
Lemma F_5ae0c : fetch_word AsanUbsan.M.loaded_segments (0x5ae54 : word) = Some W_5ae0c.
Proof. vm_refl. Qed.
Lemma D_5ae0c : decode_any W_5ae0c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae10 : bv 32 := 0x01013a03.
Lemma F_5ae10 : fetch_word AsanUbsan.M.loaded_segments (0x5ae58 : word) = Some W_5ae10.
Proof. vm_refl. Qed.
Lemma D_5ae10 : decode_any W_5ae10 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae14 : bv 32 := 0x00813a83.
Lemma F_5ae14 : fetch_word AsanUbsan.M.loaded_segments (0x5ae5c : word) = Some W_5ae14.
Proof. vm_refl. Qed.
Lemma D_5ae14 : decode_any W_5ae14 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae18 : bv 32 := 0x00013b03.
Lemma F_5ae18 : fetch_word AsanUbsan.M.loaded_segments (0x5ae60 : word) = Some W_5ae18.
Proof. vm_refl. Qed.
Lemma D_5ae18 : decode_any W_5ae18 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae1c : bv 32 := 0x04010113.
Lemma F_5ae1c : fetch_word AsanUbsan.M.loaded_segments (0x5ae64 : word) = Some W_5ae1c.
Proof. vm_refl. Qed.
Lemma D_5ae1c : decode_any W_5ae1c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae20 : bv 32 := 0x00008067.
Lemma F_5ae20 : fetch_word AsanUbsan.M.loaded_segments (0x5ae68 : word) = Some W_5ae20.
Proof. vm_refl. Qed.
Lemma D_5ae20 : decode_any W_5ae20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae24 : bv 32 := 0xffc97693.
Lemma F_5ae24 : fetch_word AsanUbsan.M.loaded_segments (0x5ae6c : word) = Some W_5ae24.
Proof. vm_refl. Qed.
Lemma D_5ae24 : decode_any W_5ae24 = Some (OpImm ALU_AND 13 18 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae28 : bv 32 := 0x00391513.
Lemma F_5ae28 : fetch_word AsanUbsan.M.loaded_segments (0x5ae70 : word) = Some W_5ae28.
Proof. vm_refl. Qed.
Lemma D_5ae28 : decode_any W_5ae28 = Some (ShiftImm ALU_SLL 10 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae2c : bv 32 := 0x0ff00613.
Lemma F_5ae2c : fetch_word AsanUbsan.M.loaded_segments (0x5ae74 : word) = Some W_5ae2c.
Proof. vm_refl. Qed.
Lemma D_5ae2c : decode_any W_5ae2c = Some (OpImm ALU_ADD 12 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae30 : bv 32 := 0x00200713.
Lemma F_5ae30 : fetch_word AsanUbsan.M.loaded_segments (0x5ae78 : word) = Some W_5ae30.
Proof. vm_refl. Qed.
Lemma D_5ae30 : decode_any W_5ae30 = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae34 : bv 32 := 0x00300593.
Lemma F_5ae34 : fetch_word AsanUbsan.M.loaded_segments (0x5ae7c : word) = Some W_5ae34.
Proof. vm_refl. Qed.
Lemma D_5ae34 : decode_any W_5ae34 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae38 : bv 32 := 0x00a617bb.
Lemma F_5ae38 : fetch_word AsanUbsan.M.loaded_segments (0x5ae80 : word) = Some W_5ae38.
Proof. vm_refl. Qed.
Lemma D_5ae38 : decode_any W_5ae38 = Some (Op32 ALU_SLL 15 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae3c : bv 32 := 0x00a7173b.
Lemma F_5ae3c : fetch_word AsanUbsan.M.loaded_segments (0x5ae84 : word) = Some W_5ae3c.
Proof. vm_refl. Qed.
Lemma D_5ae3c : decode_any W_5ae3c = Some (Op32 ALU_SLL 14 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae40 : bv 32 := 0x00a5983b.
Lemma F_5ae40 : fetch_word AsanUbsan.M.loaded_segments (0x5ae88 : word) = Some W_5ae40.
Proof. vm_refl. Qed.
Lemma D_5ae40 : decode_any W_5ae40 = Some (Op32 ALU_SLL 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae44 : bv 32 := 0x1606a62f.
Lemma F_5ae44 : fetch_word AsanUbsan.M.loaded_segments (0x5ae8c : word) = Some W_5ae44.
Proof. vm_refl. Qed.
Lemma D_5ae44 : decode_any W_5ae44 = Some (Lr AW true true 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae48 : bv 32 := 0x00f678b3.
Lemma F_5ae48 : fetch_word AsanUbsan.M.loaded_segments (0x5ae90 : word) = Some W_5ae48.
Proof. vm_refl. Qed.
Lemma D_5ae48 : decode_any W_5ae48 = Some (Op ALU_AND 17 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae4c : bv 32 := 0x08e89063.
Lemma F_5ae4c : fetch_word AsanUbsan.M.loaded_segments (0x5ae94 : word) = Some W_5ae4c.
Proof. vm_refl. Qed.
Lemma D_5ae4c : decode_any W_5ae4c = Some (Branch BC_NE 17 14 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae50 : bv 32 := 0x010648b3.
Lemma F_5ae50 : fetch_word AsanUbsan.M.loaded_segments (0x5ae98 : word) = Some W_5ae50.
Proof. vm_refl. Qed.
Lemma D_5ae50 : decode_any W_5ae50 = Some (Op ALU_XOR 17 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae54 : bv 32 := 0x00f8f8b3.
Lemma F_5ae54 : fetch_word AsanUbsan.M.loaded_segments (0x5ae9c : word) = Some W_5ae54.
Proof. vm_refl. Qed.
Lemma D_5ae54 : decode_any W_5ae54 = Some (Op ALU_AND 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae58 : bv 32 := 0x011648b3.
Lemma F_5ae58 : fetch_word AsanUbsan.M.loaded_segments (0x5aea0 : word) = Some W_5ae58.
Proof. vm_refl. Qed.
Lemma D_5ae58 : decode_any W_5ae58 = Some (Op ALU_XOR 17 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae5c : bv 32 := 0x1b16a8af.
Lemma F_5ae5c : fetch_word AsanUbsan.M.loaded_segments (0x5aea4 : word) = Some W_5ae5c.
Proof. vm_refl. Qed.
Lemma D_5ae5c : decode_any W_5ae5c = Some (Sc AW false true 17 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae60 : bv 32 := 0xfe0892e3.
Lemma F_5ae60 : fetch_word AsanUbsan.M.loaded_segments (0x5aea8 : word) = Some W_5ae60.
Proof. vm_refl. Qed.
Lemma D_5ae60 : decode_any W_5ae60 = Some (Branch BC_NE 17 0 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae64 : bv 32 := 0xfff00513.
Lemma F_5ae64 : fetch_word AsanUbsan.M.loaded_segments (0x5aeac : word) = Some W_5ae64.
Proof. vm_refl. Qed.
Lemma D_5ae64 : decode_any W_5ae64 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae68 : bv 32 := 0x02051513.
Lemma F_5ae68 : fetch_word AsanUbsan.M.loaded_segments (0x5aeb0 : word) = Some W_5ae68.
Proof. vm_refl. Qed.
Lemma D_5ae68 : decode_any W_5ae68 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae6c : bv 32 := 0x00a93823.
Lemma F_5ae6c : fetch_word AsanUbsan.M.loaded_segments (0x5aeb4 : word) = Some W_5ae6c.
Proof. vm_refl. Qed.
Lemma D_5ae6c : decode_any W_5ae6c = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae70 : bv 32 := 0x00194503.
Lemma F_5ae70 : fetch_word AsanUbsan.M.loaded_segments (0x5aeb8 : word) = Some W_5ae70.
Proof. vm_refl. Qed.
Lemma D_5ae70 : decode_any W_5ae70 = Some (Load SZ1 false 10 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae74 : bv 32 := 0x00357593.
Lemma F_5ae74 : fetch_word AsanUbsan.M.loaded_segments (0x5aebc : word) = Some W_5ae74.
Proof. vm_refl. Qed.
Lemma D_5ae74 : decode_any W_5ae74 = Some (OpImm ALU_AND 11 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae78 : bv 32 := 0x08ba1863.
Lemma F_5ae78 : fetch_word AsanUbsan.M.loaded_segments (0x5aec0 : word) = Some W_5ae78.
Proof. vm_refl. Qed.
Lemma D_5ae78 : decode_any W_5ae78 = Some (Branch BC_NE 20 11 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae7c : bv 32 := 0xffea7693.
Lemma F_5ae7c : fetch_word AsanUbsan.M.loaded_segments (0x5aec4 : word) = Some W_5ae7c.
Proof. vm_refl. Qed.
Lemma D_5ae7c : decode_any W_5ae7c = Some (OpImm ALU_AND 13 20 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae80 : bv 32 := 0x00200713.
Lemma F_5ae80 : fetch_word AsanUbsan.M.loaded_segments (0x5aec8 : word) = Some W_5ae80.
Proof. vm_refl. Qed.
Lemma D_5ae80 : decode_any W_5ae80 = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae84 : bv 32 := 0x14e69663.
Lemma F_5ae84 : fetch_word AsanUbsan.M.loaded_segments (0x5aecc : word) = Some W_5ae84.
Proof. vm_refl. Qed.
Lemma D_5ae84 : decode_any W_5ae84 = Some (Branch BC_NE 13 14 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5afd0 : bv 32 := 0x115300ef.
Lemma F_5afd0 : fetch_word AsanUbsan.M.loaded_segments (0x5b018 : word) = Some W_5afd0.
Proof. vm_refl. Qed.
Lemma D_5afd0 : decode_any W_5afd0 = Some (Jal 1 198932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5afd4 : bv 32 := 0xff24d583.
Lemma F_5afd4 : fetch_word AsanUbsan.M.loaded_segments (0x5b01c : word) = Some W_5afd4.
Proof. vm_refl. Qed.
Lemma D_5afd4 : decode_any W_5afd4 = Some (Load SZ2 false 11 9 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5afd8 : bv 32 := 0xff44e603.
Lemma F_5afd8 : fetch_word AsanUbsan.M.loaded_segments (0x5b020 : word) = Some W_5afd8.
Proof. vm_refl. Qed.
Lemma D_5afd8 : decode_any W_5afd8 = Some (Load SZ4 false 12 9 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5afdc : bv 32 := 0x02053683.
Lemma F_5afdc : fetch_word AsanUbsan.M.loaded_segments (0x5b024 : word) = Some W_5afdc.
Proof. vm_refl. Qed.
Lemma D_5afdc : decode_any W_5afdc = Some (Load SZ8 true 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5afe0 : bv 32 := 0x01853703.
Lemma F_5afe0 : fetch_word AsanUbsan.M.loaded_segments (0x5b028 : word) = Some W_5afe0.
Proof. vm_refl. Qed.
Lemma D_5afe0 : decode_any W_5afe0 = Some (Load SZ8 true 14 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5afe4 : bv 32 := 0x02059593.
Lemma F_5afe4 : fetch_word AsanUbsan.M.loaded_segments (0x5b02c : word) = Some W_5afe4.
Proof. vm_refl. Qed.
Lemma D_5afe4 : decode_any W_5afe4 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5afe8 : bv 32 := 0x00c5e5b3.
Lemma F_5afe8 : fetch_word AsanUbsan.M.loaded_segments (0x5b030 : word) = Some W_5afe8.
Proof. vm_refl. Qed.
Lemma D_5afe8 : decode_any W_5afe8 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5afec : bv 32 := 0x00d585b3.
Lemma F_5afec : fetch_word AsanUbsan.M.loaded_segments (0x5b034 : word) = Some W_5afec.
Proof. vm_refl. Qed.
Lemma D_5afec : decode_any W_5afec = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aff0 : bv 32 := 0x00170713.
Lemma F_5aff0 : fetch_word AsanUbsan.M.loaded_segments (0x5b038 : word) = Some W_5aff0.
Proof. vm_refl. Qed.
Lemma D_5aff0 : decode_any W_5aff0 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aff4 : bv 32 := 0x00e53c23.
Lemma F_5aff4 : fetch_word AsanUbsan.M.loaded_segments (0x5b03c : word) = Some W_5aff4.
Proof. vm_refl. Qed.
Lemma D_5aff4 : decode_any W_5aff4 = Some (Store SZ8 10 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aff8 : bv 32 := 0x02b53023.
Lemma F_5aff8 : fetch_word AsanUbsan.M.loaded_segments (0x5b040 : word) = Some W_5aff8.
Proof. vm_refl. Qed.
Lemma D_5aff8 : decode_any W_5aff8 = Some (Store SZ8 10 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5affc : bv 32 := 0x00098513.
Lemma F_5affc : fetch_word AsanUbsan.M.loaded_segments (0x5b044 : word) = Some W_5affc.
Proof. vm_refl. Qed.
Lemma D_5affc : decode_any W_5affc = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

