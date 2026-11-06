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
Definition W_170cc : bv 32 := 0xfd010113.
Lemma F_170cc : fetch_word Plain.M.loaded_segments (0x171c8 : word) = Some W_170cc.
Proof. vm_refl. Qed.
Lemma D_170cc : decode_any W_170cc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170d0 : bv 32 := 0x02113423.
Lemma F_170d0 : fetch_word Plain.M.loaded_segments (0x171cc : word) = Some W_170d0.
Proof. vm_refl. Qed.
Lemma D_170d0 : decode_any W_170d0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170d4 : bv 32 := 0x02813023.
Lemma F_170d4 : fetch_word Plain.M.loaded_segments (0x171d0 : word) = Some W_170d4.
Proof. vm_refl. Qed.
Lemma D_170d4 : decode_any W_170d4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170d8 : bv 32 := 0x00913c23.
Lemma F_170d8 : fetch_word Plain.M.loaded_segments (0x171d4 : word) = Some W_170d8.
Proof. vm_refl. Qed.
Lemma D_170d8 : decode_any W_170d8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170dc : bv 32 := 0x01213823.
Lemma F_170dc : fetch_word Plain.M.loaded_segments (0x171d8 : word) = Some W_170dc.
Proof. vm_refl. Qed.
Lemma D_170dc : decode_any W_170dc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170e0 : bv 32 := 0x06050063.
Lemma F_170e0 : fetch_word Plain.M.loaded_segments (0x171dc : word) = Some W_170e0.
Proof. vm_refl. Qed.
Lemma D_170e0 : decode_any W_170e0 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170e4 : bv 32 := 0x00050493.
Lemma F_170e4 : fetch_word Plain.M.loaded_segments (0x171e0 : word) = Some W_170e4.
Proof. vm_refl. Qed.
Lemma D_170e4 : decode_any W_170e4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170e8 : bv 32 := 0x00058913.
Lemma F_170e8 : fetch_word Plain.M.loaded_segments (0x171e4 : word) = Some W_170e8.
Proof. vm_refl. Qed.
Lemma D_170e8 : decode_any W_170e8 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170ec : bv 32 := 0x00c10593.
Lemma F_170ec : fetch_word Plain.M.loaded_segments (0x171e8 : word) = Some W_170ec.
Proof. vm_refl. Qed.
Lemma D_170ec : decode_any W_170ec = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170f0 : bv 32 := 0x00810613.
Lemma F_170f0 : fetch_word Plain.M.loaded_segments (0x171ec : word) = Some W_170f0.
Proof. vm_refl. Qed.
Lemma D_170f0 : decode_any W_170f0 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170f4 : bv 32 := 0x00410693.
Lemma F_170f4 : fetch_word Plain.M.loaded_segments (0x171f0 : word) = Some W_170f4.
Proof. vm_refl. Qed.
Lemma D_170f4 : decode_any W_170f4 = Some (OpImm ALU_ADD 13 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170f8 : bv 32 := 0xc41fe0ef.
Lemma F_170f8 : fetch_word Plain.M.loaded_segments (0x171f4 : word) = Some W_170f8.
Proof. vm_refl. Qed.
Lemma D_170f8 : decode_any W_170f8 = Some (Jal 1 2092096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170fc : bv 32 := 0x00412503.
Lemma F_170fc : fetch_word Plain.M.loaded_segments (0x171f8 : word) = Some W_170fc.
Proof. vm_refl. Qed.
Lemma D_170fc : decode_any W_170fc = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17100 : bv 32 := 0x02000593.
Lemma F_17100 : fetch_word Plain.M.loaded_segments (0x171fc : word) = Some W_17100.
Proof. vm_refl. Qed.
Lemma D_17100 : decode_any W_17100 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17104 : bv 32 := 0x12b50463.
Lemma F_17104 : fetch_word Plain.M.loaded_segments (0x17200 : word) = Some W_17104.
Proof. vm_refl. Qed.
Lemma D_17104 : decode_any W_17104 = Some (Branch BC_EQ 10 11 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1722c : bv 32 := 0x00000513.
Lemma F_1722c : fetch_word Plain.M.loaded_segments (0x17328 : word) = Some W_1722c.
Proof. vm_refl. Qed.
Lemma D_1722c : decode_any W_1722c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17230 : bv 32 := 0x02813083.
Lemma F_17230 : fetch_word Plain.M.loaded_segments (0x1732c : word) = Some W_17230.
Proof. vm_refl. Qed.
Lemma D_17230 : decode_any W_17230 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17234 : bv 32 := 0x02013403.
Lemma F_17234 : fetch_word Plain.M.loaded_segments (0x17330 : word) = Some W_17234.
Proof. vm_refl. Qed.
Lemma D_17234 : decode_any W_17234 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17238 : bv 32 := 0x01813483.
Lemma F_17238 : fetch_word Plain.M.loaded_segments (0x17334 : word) = Some W_17238.
Proof. vm_refl. Qed.
Lemma D_17238 : decode_any W_17238 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1723c : bv 32 := 0x01013903.
Lemma F_1723c : fetch_word Plain.M.loaded_segments (0x17338 : word) = Some W_1723c.
Proof. vm_refl. Qed.
Lemma D_1723c : decode_any W_1723c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17240 : bv 32 := 0x03010113.
Lemma F_17240 : fetch_word Plain.M.loaded_segments (0x1733c : word) = Some W_17240.
Proof. vm_refl. Qed.
Lemma D_17240 : decode_any W_17240 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17244 : bv 32 := 0x00008067.
Lemma F_17244 : fetch_word Plain.M.loaded_segments (0x17340 : word) = Some W_17244.
Proof. vm_refl. Qed.
Lemma D_17244 : decode_any W_17244 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
