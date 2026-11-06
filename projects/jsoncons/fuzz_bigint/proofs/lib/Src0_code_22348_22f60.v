(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_22348 : bv 32 := 0x00008067.
Lemma F_22348 : fetch_word Plain.M.loaded_segments (0x22348 : word) = Some W_22348.
Proof. vm_refl. Qed.
Lemma D_22348 : decode_any W_22348 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_224cc : bv 32 := 0x00054c63.
Lemma F_224cc : fetch_word Plain.M.loaded_segments (0x224cc : word) = Some W_224cc.
Proof. vm_refl. Qed.
Lemma D_224cc : decode_any W_224cc = Some (Branch BC_LT 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_224d0 : bv 32 := 0x00000593.
Lemma F_224d0 : fetch_word Plain.M.loaded_segments (0x224d0 : word) = Some W_224d0.
Proof. vm_refl. Qed.
Lemma D_224d0 : decode_any W_224d0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_224d4 : bv 32 := 0x00151513.
Lemma F_224d4 : fetch_word Plain.M.loaded_segments (0x224d4 : word) = Some W_224d4.
Proof. vm_refl. Qed.
Lemma D_224d4 : decode_any W_224d4 = Some (ShiftImm ALU_SLL 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_224d8 : bv 32 := 0x0015859b.
Lemma F_224d8 : fetch_word Plain.M.loaded_segments (0x224d8 : word) = Some W_224d8.
Proof. vm_refl. Qed.
Lemma D_224d8 : decode_any W_224d8 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_224dc : bv 32 := 0xfe055ce3.
Lemma F_224dc : fetch_word Plain.M.loaded_segments (0x224dc : word) = Some W_224dc.
Proof. vm_refl. Qed.
Lemma D_224dc : decode_any W_224dc = Some (Branch BC_GE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_22500 : bv 32 := 0x040b0663.
Lemma F_22500 : fetch_word Plain.M.loaded_segments (0x22500 : word) = Some W_22500.
Proof. vm_refl. Qed.
Lemma D_22500 : decode_any W_22500 = Some (Branch BC_EQ 22 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_22528 : bv 32 := 0x02b57263.
Lemma F_22528 : fetch_word Plain.M.loaded_segments (0x22528 : word) = Some W_22528.
Proof. vm_refl. Qed.
Lemma D_22528 : decode_any W_22528 = Some (Branch BC_GEU 10 11 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_22574 : bv 32 := 0x00008067.
Lemma F_22574 : fetch_word Plain.M.loaded_segments (0x22574 : word) = Some W_22574.
Proof. vm_refl. Qed.
Lemma D_22574 : decode_any W_22574 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_225bc : bv 32 := 0x01176663.
Lemma F_225bc : fetch_word Plain.M.loaded_segments (0x225bc : word) = Some W_225bc.
Proof. vm_refl. Qed.
Lemma D_225bc : decode_any W_225bc = Some (Branch BC_LTU 14 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_225c0 : bv 32 := 0x02e89463.
Lemma F_225c0 : fetch_word Plain.M.loaded_segments (0x225c0 : word) = Some W_225c0.
Proof. vm_refl. Qed.
Lemma D_225c0 : decode_any W_225c0 = Some (Branch BC_NE 17 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_225c4 : bv 32 := 0x0255e263.
Lemma F_225c4 : fetch_word Plain.M.loaded_segments (0x225c4 : word) = Some W_225c4.
Proof. vm_refl. Qed.
Lemma D_225c4 : decode_any W_225c4 = Some (Branch BC_LTU 11 5 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_225e0 : bv 32 := 0xff1764e3.
Lemma F_225e0 : fetch_word Plain.M.loaded_segments (0x225e0 : word) = Some W_225e0.
Proof. vm_refl. Qed.
Lemma D_225e0 : decode_any W_225e0 = Some (Branch BC_LTU 14 17 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_225e4 : bv 32 := 0xfddff06f.
Lemma F_225e4 : fetch_word Plain.M.loaded_segments (0x225e4 : word) = Some W_225e4.
Proof. vm_refl. Qed.
Lemma D_225e4 : decode_any W_225e4 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

Definition W_22634 : bv 32 := 0x00071463.
Lemma F_22634 : fetch_word Plain.M.loaded_segments (0x22634 : word) = Some W_22634.
Proof. vm_refl. Qed.
Lemma D_22634 : decode_any W_22634 = Some (Branch BC_NE 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_22638 : bv 32 := 0x02d7ea63.
Lemma F_22638 : fetch_word Plain.M.loaded_segments (0x22638 : word) = Some W_22638.
Proof. vm_refl. Qed.
Lemma D_22638 : decode_any W_22638 = Some (Branch BC_LTU 15 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_22664 : bv 32 := 0xfe0714e3.
Lemma F_22664 : fetch_word Plain.M.loaded_segments (0x22664 : word) = Some W_22664.
Proof. vm_refl. Qed.
Lemma D_22664 : decode_any W_22664 = Some (Branch BC_NE 14 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_22668 : bv 32 := 0xfed872e3.
Lemma F_22668 : fetch_word Plain.M.loaded_segments (0x22668 : word) = Some W_22668.
Proof. vm_refl. Qed.
Lemma D_22668 : decode_any W_22668 = Some (Branch BC_GEU 16 13 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_22670 : bv 32 := 0x00008067.
Lemma F_22670 : fetch_word Plain.M.loaded_segments (0x22670 : word) = Some W_22670.
Proof. vm_refl. Qed.
Lemma D_22670 : decode_any W_22670 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_22730 : bv 32 := 0x05c3f863.
Lemma F_22730 : fetch_word Plain.M.loaded_segments (0x22730 : word) = Some W_22730.
Proof. vm_refl. Qed.
Lemma D_22730 : decode_any W_22730 = Some (Branch BC_GEU 7 28 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_2278c : bv 32 := 0x00008067.
Lemma F_2278c : fetch_word Plain.M.loaded_segments (0x2278c : word) = Some W_2278c.
Proof. vm_refl. Qed.
Lemma D_2278c : decode_any W_2278c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_22818 : bv 32 := 0x00008067.
Lemma F_22818 : fetch_word Plain.M.loaded_segments (0x22818 : word) = Some W_22818.
Proof. vm_refl. Qed.
Lemma D_22818 : decode_any W_22818 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_229e0 : bv 32 := 0x00008067.
Lemma F_229e0 : fetch_word Plain.M.loaded_segments (0x229e0 : word) = Some W_229e0.
Proof. vm_refl. Qed.
Lemma D_229e0 : decode_any W_229e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_22b04 : bv 32 := 0x00008067.
Lemma F_22b04 : fetch_word Plain.M.loaded_segments (0x22b04 : word) = Some W_22b04.
Proof. vm_refl. Qed.
Lemma D_22b04 : decode_any W_22b04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_22b68 : bv 32 := 0x00008067.
Lemma F_22b68 : fetch_word Plain.M.loaded_segments (0x22b68 : word) = Some W_22b68.
Proof. vm_refl. Qed.
Lemma D_22b68 : decode_any W_22b68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_22ca0 : bv 32 := 0x00008067.
Lemma F_22ca0 : fetch_word Plain.M.loaded_segments (0x22ca0 : word) = Some W_22ca0.
Proof. vm_refl. Qed.
Lemma D_22ca0 : decode_any W_22ca0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_22eb0 : bv 32 := 0x7e113423.
Lemma F_22eb0 : fetch_word Plain.M.loaded_segments (0x22eb0 : word) = Some W_22eb0.
Proof. vm_refl. Qed.
Lemma D_22eb0 : decode_any W_22eb0 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_22eb4 : bv 32 := 0x7e813023.
Lemma F_22eb4 : fetch_word Plain.M.loaded_segments (0x22eb4 : word) = Some W_22eb4.
Proof. vm_refl. Qed.
Lemma D_22eb4 : decode_any W_22eb4 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_22eb8 : bv 32 := 0x7c913c23.
Lemma F_22eb8 : fetch_word Plain.M.loaded_segments (0x22eb8 : word) = Some W_22eb8.
Proof. vm_refl. Qed.
Lemma D_22eb8 : decode_any W_22eb8 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_22ed4 : bv 32 := 0x7b813023.
Lemma F_22ed4 : fetch_word Plain.M.loaded_segments (0x22ed4 : word) = Some W_22ed4.
Proof. vm_refl. Qed.
Lemma D_22ed4 : decode_any W_22ed4 = Some (Store SZ8 2 24 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_22ed8 : bv 32 := 0x79913c23.
Lemma F_22ed8 : fetch_word Plain.M.loaded_segments (0x22ed8 : word) = Some W_22ed8.
Proof. vm_refl. Qed.
Lemma D_22ed8 : decode_any W_22ed8 = Some (Store SZ8 2 25 1944, 4%Z).
Proof. vm_refl. Qed.

Definition W_22f28 : bv 32 := 0x00aa8533.
Lemma F_22f28 : fetch_word Plain.M.loaded_segments (0x22f28 : word) = Some W_22f28.
Proof. vm_refl. Qed.
Lemma D_22f28 : decode_any W_22f28 = Some (Op ALU_ADD 10 21 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_22f2c : bv 32 := 0x06810413.
Lemma F_22f2c : fetch_word Plain.M.loaded_segments (0x22f2c : word) = Some W_22f2c.
Proof. vm_refl. Qed.
Lemma D_22f2c : decode_any W_22f2c = Some (OpImm ALU_ADD 8 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_22f58 : bv 32 := 0x18010493.
Lemma F_22f58 : fetch_word Plain.M.loaded_segments (0x22f58 : word) = Some W_22f58.
Proof. vm_refl. Qed.
Lemma D_22f58 : decode_any W_22f58 = Some (OpImm ALU_ADD 9 2 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_22f5c : bv 32 := 0x28010513.
Lemma F_22f5c : fetch_word Plain.M.loaded_segments (0x22f5c : word) = Some W_22f5c.
Proof. vm_refl. Qed.
Lemma D_22f5c : decode_any W_22f5c = Some (OpImm ALU_ADD 10 2 640, 4%Z).
Proof. vm_refl. Qed.
