(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.H Require GcFlushU14.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_17810 : bv 32 := 0xfd010113.
Lemma F_17810 : fetch_word Ubsan.M.loaded_segments (0x1790c : word) = Some W_17810.
Proof. vm_refl. Qed.
Lemma D_17810 : decode_any W_17810 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17814 : bv 32 := 0x02113423.
Lemma F_17814 : fetch_word Ubsan.M.loaded_segments (0x17910 : word) = Some W_17814.
Proof. vm_refl. Qed.
Lemma D_17814 : decode_any W_17814 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17818 : bv 32 := 0x02813023.
Lemma F_17818 : fetch_word Ubsan.M.loaded_segments (0x17914 : word) = Some W_17818.
Proof. vm_refl. Qed.
Lemma D_17818 : decode_any W_17818 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1781c : bv 32 := 0x00913c23.
Lemma F_1781c : fetch_word Ubsan.M.loaded_segments (0x17918 : word) = Some W_1781c.
Proof. vm_refl. Qed.
Lemma D_1781c : decode_any W_1781c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17820 : bv 32 := 0x01213823.
Lemma F_17820 : fetch_word Ubsan.M.loaded_segments (0x1791c : word) = Some W_17820.
Proof. vm_refl. Qed.
Lemma D_17820 : decode_any W_17820 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17824 : bv 32 := 0x06050063.
Lemma F_17824 : fetch_word Ubsan.M.loaded_segments (0x17920 : word) = Some W_17824.
Proof. vm_refl. Qed.
Lemma D_17824 : decode_any W_17824 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17828 : bv 32 := 0x00058413.
Lemma F_17828 : fetch_word Ubsan.M.loaded_segments (0x17924 : word) = Some W_17828.
Proof. vm_refl. Qed.
Lemma D_17828 : decode_any W_17828 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1782c : bv 32 := 0x00050913.
Lemma F_1782c : fetch_word Ubsan.M.loaded_segments (0x17928 : word) = Some W_1782c.
Proof. vm_refl. Qed.
Lemma D_1782c : decode_any W_1782c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17830 : bv 32 := 0x00c10593.
Lemma F_17830 : fetch_word Ubsan.M.loaded_segments (0x1792c : word) = Some W_17830.
Proof. vm_refl. Qed.
Lemma D_17830 : decode_any W_17830 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17834 : bv 32 := 0x00810613.
Lemma F_17834 : fetch_word Ubsan.M.loaded_segments (0x17930 : word) = Some W_17834.
Proof. vm_refl. Qed.
Lemma D_17834 : decode_any W_17834 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17838 : bv 32 := 0x00410693.
Lemma F_17838 : fetch_word Ubsan.M.loaded_segments (0x17934 : word) = Some W_17838.
Proof. vm_refl. Qed.
Lemma D_17838 : decode_any W_17838 = Some (OpImm ALU_ADD 13 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1783c : bv 32 := 0xec8fe0ef.
Lemma F_1783c : fetch_word Ubsan.M.loaded_segments (0x17938 : word) = Some W_1783c.
Proof. vm_refl. Qed.
Lemma D_1783c : decode_any W_1783c = Some (Jal 1 2090696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17840 : bv 32 := 0x00412503.
Lemma F_17840 : fetch_word Ubsan.M.loaded_segments (0x1793c : word) = Some W_17840.
Proof. vm_refl. Qed.
Lemma D_17840 : decode_any W_17840 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17844 : bv 32 := 0x02000593.
Lemma F_17844 : fetch_word Ubsan.M.loaded_segments (0x17940 : word) = Some W_17844.
Proof. vm_refl. Qed.
Lemma D_17844 : decode_any W_17844 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17848 : bv 32 := 0x18b50c63.
Lemma F_17848 : fetch_word Ubsan.M.loaded_segments (0x17944 : word) = Some W_17848.
Proof. vm_refl. Qed.
Lemma D_17848 : decode_any W_17848 = Some (Branch BC_EQ 10 11 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179e0 : bv 32 := 0x00000513.
Lemma F_179e0 : fetch_word Ubsan.M.loaded_segments (0x17adc : word) = Some W_179e0.
Proof. vm_refl. Qed.
Lemma D_179e0 : decode_any W_179e0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179e4 : bv 32 := 0x02813083.
Lemma F_179e4 : fetch_word Ubsan.M.loaded_segments (0x17ae0 : word) = Some W_179e4.
Proof. vm_refl. Qed.
Lemma D_179e4 : decode_any W_179e4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179e8 : bv 32 := 0x02013403.
Lemma F_179e8 : fetch_word Ubsan.M.loaded_segments (0x17ae4 : word) = Some W_179e8.
Proof. vm_refl. Qed.
Lemma D_179e8 : decode_any W_179e8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179ec : bv 32 := 0x01813483.
Lemma F_179ec : fetch_word Ubsan.M.loaded_segments (0x17ae8 : word) = Some W_179ec.
Proof. vm_refl. Qed.
Lemma D_179ec : decode_any W_179ec = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179f0 : bv 32 := 0x01013903.
Lemma F_179f0 : fetch_word Ubsan.M.loaded_segments (0x17aec : word) = Some W_179f0.
Proof. vm_refl. Qed.
Lemma D_179f0 : decode_any W_179f0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179f4 : bv 32 := 0x03010113.
Lemma F_179f4 : fetch_word Ubsan.M.loaded_segments (0x17af0 : word) = Some W_179f4.
Proof. vm_refl. Qed.
Lemma D_179f4 : decode_any W_179f4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179f8 : bv 32 := 0x00008067.
Lemma F_179f8 : fetch_word Ubsan.M.loaded_segments (0x17af4 : word) = Some W_179f8.
Proof. vm_refl. Qed.
Lemma D_179f8 : decode_any W_179f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
