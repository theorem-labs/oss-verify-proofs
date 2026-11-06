(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.H Require GcFlushS14.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_18890 : bv 32 := 0xfe010113.
Lemma F_18890 : fetch_word Plain.M.loaded_segments (0x1898c : word) = Some W_18890.
Proof. vm_refl. Qed.
Lemma D_18890 : decode_any W_18890 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18894 : bv 32 := 0x00113c23.
Lemma F_18894 : fetch_word Plain.M.loaded_segments (0x18990 : word) = Some W_18894.
Proof. vm_refl. Qed.
Lemma D_18894 : decode_any W_18894 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18898 : bv 32 := 0x00813823.
Lemma F_18898 : fetch_word Plain.M.loaded_segments (0x18994 : word) = Some W_18898.
Proof. vm_refl. Qed.
Lemma D_18898 : decode_any W_18898 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1889c : bv 32 := 0x00913423.
Lemma F_1889c : fetch_word Plain.M.loaded_segments (0x18998 : word) = Some W_1889c.
Proof. vm_refl. Qed.
Lemma D_1889c : decode_any W_1889c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188a0 : bv 32 := 0x06050463.
Lemma F_188a0 : fetch_word Plain.M.loaded_segments (0x1899c : word) = Some W_188a0.
Proof. vm_refl. Qed.
Lemma D_188a0 : decode_any W_188a0 = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188a4 : bv 32 := 0x00050413.
Lemma F_188a4 : fetch_word Plain.M.loaded_segments (0x189a0 : word) = Some W_188a4.
Proof. vm_refl. Qed.
Lemma D_188a4 : decode_any W_188a4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188a8 : bv 32 := 0x00410613.
Lemma F_188a8 : fetch_word Plain.M.loaded_segments (0x189a4 : word) = Some W_188a8.
Proof. vm_refl. Qed.
Lemma D_188a8 : decode_any W_188a8 = Some (OpImm ALU_ADD 12 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188ac : bv 32 := 0x00000593.
Lemma F_188ac : fetch_word Plain.M.loaded_segments (0x189a8 : word) = Some W_188ac.
Proof. vm_refl. Qed.
Lemma D_188ac : decode_any W_188ac = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188b0 : bv 32 := 0x0dc000ef.
Lemma F_188b0 : fetch_word Plain.M.loaded_segments (0x189ac : word) = Some W_188b0.
Proof. vm_refl. Qed.
Lemma D_188b0 : decode_any W_188b0 = Some (Jal 1 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188b4 : bv 32 := 0x00412503.
Lemma F_188b4 : fetch_word Plain.M.loaded_segments (0x189b0 : word) = Some W_188b4.
Proof. vm_refl. Qed.
Lemma D_188b4 : decode_any W_188b4 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188b8 : bv 32 := 0x08050663.
Lemma F_188b8 : fetch_word Plain.M.loaded_segments (0x189b4 : word) = Some W_188b8.
Proof. vm_refl. Qed.
Lemma D_188b8 : decode_any W_188b8 = Some (Branch BC_EQ 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188bc : bv 32 := 0x00100513.
Lemma F_188bc : fetch_word Plain.M.loaded_segments (0x189b8 : word) = Some W_188bc.
Proof. vm_refl. Qed.
Lemma D_188bc : decode_any W_188bc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188c0 : bv 32 := 0x01800593.
Lemma F_188c0 : fetch_word Plain.M.loaded_segments (0x189bc : word) = Some W_188c0.
Proof. vm_refl. Qed.
Lemma D_188c0 : decode_any W_188c0 = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188c4 : bv 32 := 0x3fc090ef.
Lemma F_188c4 : fetch_word Plain.M.loaded_segments (0x189c0 : word) = Some W_188c4.
Proof. vm_refl. Qed.
Lemma D_188c4 : decode_any W_188c4 = Some (Jal 1 37884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188c8 : bv 32 := 0x00050493.
Lemma F_188c8 : fetch_word Plain.M.loaded_segments (0x189c4 : word) = Some W_188c8.
Proof. vm_refl. Qed.
Lemma D_188c8 : decode_any W_188c8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188cc : bv 32 := 0x00c42503.
Lemma F_188cc : fetch_word Plain.M.loaded_segments (0x189c8 : word) = Some W_188cc.
Proof. vm_refl. Qed.
Lemma D_188cc : decode_any W_188cc = Some (Load SZ4 true 10 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188d0 : bv 32 := 0x0025159b.
Lemma F_188d0 : fetch_word Plain.M.loaded_segments (0x189cc : word) = Some W_188d0.
Proof. vm_refl. Qed.
Lemma D_188d0 : decode_any W_188d0 = Some (ShiftImm32 ALU_SLL 11 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188d4 : bv 32 := 0x00100513.
Lemma F_188d4 : fetch_word Plain.M.loaded_segments (0x189d0 : word) = Some W_188d4.
Proof. vm_refl. Qed.
Lemma D_188d4 : decode_any W_188d4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188d8 : bv 32 := 0x3e8090ef.
Lemma F_188d8 : fetch_word Plain.M.loaded_segments (0x189d4 : word) = Some W_188d8.
Proof. vm_refl. Qed.
Lemma D_188d8 : decode_any W_188d8 = Some (Jal 1 37864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188dc : bv 32 := 0x00a4b023.
Lemma F_188dc : fetch_word Plain.M.loaded_segments (0x189d8 : word) = Some W_188dc.
Proof. vm_refl. Qed.
Lemma D_188dc : decode_any W_188dc = Some (Store SZ8 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188e0 : bv 32 := 0x01042603.
Lemma F_188e0 : fetch_word Plain.M.loaded_segments (0x189dc : word) = Some W_188e0.
Proof. vm_refl. Qed.
Lemma D_188e0 : decode_any W_188e0 = Some (Load SZ4 true 12 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188e4 : bv 32 := 0x00043583.
Lemma F_188e4 : fetch_word Plain.M.loaded_segments (0x189e0 : word) = Some W_188e4.
Proof. vm_refl. Qed.
Lemma D_188e4 : decode_any W_188e4 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188e8 : bv 32 := 0x00261613.
Lemma F_188e8 : fetch_word Plain.M.loaded_segments (0x189e4 : word) = Some W_188e8.
Proof. vm_refl. Qed.
Lemma D_188e8 : decode_any W_188e8 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188ec : bv 32 := 0x640100ef.
Lemma F_188ec : fetch_word Plain.M.loaded_segments (0x189e8 : word) = Some W_188ec.
Proof. vm_refl. Qed.
Lemma D_188ec : decode_any W_188ec = Some (Jal 1 67136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188f0 : bv 32 := 0x00048513.
Lemma F_188f0 : fetch_word Plain.M.loaded_segments (0x189ec : word) = Some W_188f0.
Proof. vm_refl. Qed.
Lemma D_188f0 : decode_any W_188f0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188f4 : bv 32 := 0x01042583.
Lemma F_188f4 : fetch_word Plain.M.loaded_segments (0x189f0 : word) = Some W_188f4.
Proof. vm_refl. Qed.
Lemma D_188f4 : decode_any W_188f4 = Some (Load SZ4 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188f8 : bv 32 := 0x00b4a823.
Lemma F_188f8 : fetch_word Plain.M.loaded_segments (0x189f4 : word) = Some W_188f8.
Proof. vm_refl. Qed.
Lemma D_188f8 : decode_any W_188f8 = Some (Store SZ4 9 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188fc : bv 32 := 0x00843583.
Lemma F_188fc : fetch_word Plain.M.loaded_segments (0x189f8 : word) = Some W_188fc.
Proof. vm_refl. Qed.
Lemma D_188fc : decode_any W_188fc = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18900 : bv 32 := 0x00b4b423.
Lemma F_18900 : fetch_word Plain.M.loaded_segments (0x189fc : word) = Some W_18900.
Proof. vm_refl. Qed.
Lemma D_18900 : decode_any W_18900 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18904 : bv 32 := 0x0740006f.
Lemma F_18904 : fetch_word Plain.M.loaded_segments (0x18a00 : word) = Some W_18904.
Proof. vm_refl. Qed.
Lemma D_18904 : decode_any W_18904 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18978 : bv 32 := 0x01813083.
Lemma F_18978 : fetch_word Plain.M.loaded_segments (0x18a74 : word) = Some W_18978.
Proof. vm_refl. Qed.
Lemma D_18978 : decode_any W_18978 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1897c : bv 32 := 0x01013403.
Lemma F_1897c : fetch_word Plain.M.loaded_segments (0x18a78 : word) = Some W_1897c.
Proof. vm_refl. Qed.
Lemma D_1897c : decode_any W_1897c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18980 : bv 32 := 0x00813483.
Lemma F_18980 : fetch_word Plain.M.loaded_segments (0x18a7c : word) = Some W_18980.
Proof. vm_refl. Qed.
Lemma D_18980 : decode_any W_18980 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18984 : bv 32 := 0x02010113.
Lemma F_18984 : fetch_word Plain.M.loaded_segments (0x18a80 : word) = Some W_18984.
Proof. vm_refl. Qed.
Lemma D_18984 : decode_any W_18984 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18988 : bv 32 := 0x00008067.
Lemma F_18988 : fetch_word Plain.M.loaded_segments (0x18a84 : word) = Some W_18988.
Proof. vm_refl. Qed.
Lemma D_18988 : decode_any W_18988 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
