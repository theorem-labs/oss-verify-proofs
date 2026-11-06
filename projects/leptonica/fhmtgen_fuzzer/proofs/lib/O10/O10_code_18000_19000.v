(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.H Require GcFlushS10.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_18810 : bv 32 := 0xfe010113.
Lemma F_18810 : fetch_word Plain.M.loaded_segments (0x1890c : word) = Some W_18810.
Proof. vm_refl. Qed.
Lemma D_18810 : decode_any W_18810 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18814 : bv 32 := 0x00113c23.
Lemma F_18814 : fetch_word Plain.M.loaded_segments (0x18910 : word) = Some W_18814.
Proof. vm_refl. Qed.
Lemma D_18814 : decode_any W_18814 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18818 : bv 32 := 0x00813823.
Lemma F_18818 : fetch_word Plain.M.loaded_segments (0x18914 : word) = Some W_18818.
Proof. vm_refl. Qed.
Lemma D_18818 : decode_any W_18818 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1881c : bv 32 := 0x00913423.
Lemma F_1881c : fetch_word Plain.M.loaded_segments (0x18918 : word) = Some W_1881c.
Proof. vm_refl. Qed.
Lemma D_1881c : decode_any W_1881c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18820 : bv 32 := 0x06050463.
Lemma F_18820 : fetch_word Plain.M.loaded_segments (0x1891c : word) = Some W_18820.
Proof. vm_refl. Qed.
Lemma D_18820 : decode_any W_18820 = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18824 : bv 32 := 0x00050413.
Lemma F_18824 : fetch_word Plain.M.loaded_segments (0x18920 : word) = Some W_18824.
Proof. vm_refl. Qed.
Lemma D_18824 : decode_any W_18824 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18828 : bv 32 := 0x00410613.
Lemma F_18828 : fetch_word Plain.M.loaded_segments (0x18924 : word) = Some W_18828.
Proof. vm_refl. Qed.
Lemma D_18828 : decode_any W_18828 = Some (OpImm ALU_ADD 12 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1882c : bv 32 := 0x00000593.
Lemma F_1882c : fetch_word Plain.M.loaded_segments (0x18928 : word) = Some W_1882c.
Proof. vm_refl. Qed.
Lemma D_1882c : decode_any W_1882c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18830 : bv 32 := 0x0dc000ef.
Lemma F_18830 : fetch_word Plain.M.loaded_segments (0x1892c : word) = Some W_18830.
Proof. vm_refl. Qed.
Lemma D_18830 : decode_any W_18830 = Some (Jal 1 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18834 : bv 32 := 0x00412503.
Lemma F_18834 : fetch_word Plain.M.loaded_segments (0x18930 : word) = Some W_18834.
Proof. vm_refl. Qed.
Lemma D_18834 : decode_any W_18834 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18838 : bv 32 := 0x08050663.
Lemma F_18838 : fetch_word Plain.M.loaded_segments (0x18934 : word) = Some W_18838.
Proof. vm_refl. Qed.
Lemma D_18838 : decode_any W_18838 = Some (Branch BC_EQ 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1883c : bv 32 := 0x00100513.
Lemma F_1883c : fetch_word Plain.M.loaded_segments (0x18938 : word) = Some W_1883c.
Proof. vm_refl. Qed.
Lemma D_1883c : decode_any W_1883c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18840 : bv 32 := 0x01800593.
Lemma F_18840 : fetch_word Plain.M.loaded_segments (0x1893c : word) = Some W_18840.
Proof. vm_refl. Qed.
Lemma D_18840 : decode_any W_18840 = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18844 : bv 32 := 0x41c0a0ef.
Lemma F_18844 : fetch_word Plain.M.loaded_segments (0x18940 : word) = Some W_18844.
Proof. vm_refl. Qed.
Lemma D_18844 : decode_any W_18844 = Some (Jal 1 42012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18848 : bv 32 := 0x00050493.
Lemma F_18848 : fetch_word Plain.M.loaded_segments (0x18944 : word) = Some W_18848.
Proof. vm_refl. Qed.
Lemma D_18848 : decode_any W_18848 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1884c : bv 32 := 0x00c42503.
Lemma F_1884c : fetch_word Plain.M.loaded_segments (0x18948 : word) = Some W_1884c.
Proof. vm_refl. Qed.
Lemma D_1884c : decode_any W_1884c = Some (Load SZ4 true 10 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18850 : bv 32 := 0x0025159b.
Lemma F_18850 : fetch_word Plain.M.loaded_segments (0x1894c : word) = Some W_18850.
Proof. vm_refl. Qed.
Lemma D_18850 : decode_any W_18850 = Some (ShiftImm32 ALU_SLL 11 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18854 : bv 32 := 0x00100513.
Lemma F_18854 : fetch_word Plain.M.loaded_segments (0x18950 : word) = Some W_18854.
Proof. vm_refl. Qed.
Lemma D_18854 : decode_any W_18854 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18858 : bv 32 := 0x4080a0ef.
Lemma F_18858 : fetch_word Plain.M.loaded_segments (0x18954 : word) = Some W_18858.
Proof. vm_refl. Qed.
Lemma D_18858 : decode_any W_18858 = Some (Jal 1 41992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1885c : bv 32 := 0x00a4b023.
Lemma F_1885c : fetch_word Plain.M.loaded_segments (0x18958 : word) = Some W_1885c.
Proof. vm_refl. Qed.
Lemma D_1885c : decode_any W_1885c = Some (Store SZ8 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18860 : bv 32 := 0x01042603.
Lemma F_18860 : fetch_word Plain.M.loaded_segments (0x1895c : word) = Some W_18860.
Proof. vm_refl. Qed.
Lemma D_18860 : decode_any W_18860 = Some (Load SZ4 true 12 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18864 : bv 32 := 0x00043583.
Lemma F_18864 : fetch_word Plain.M.loaded_segments (0x18960 : word) = Some W_18864.
Proof. vm_refl. Qed.
Lemma D_18864 : decode_any W_18864 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18868 : bv 32 := 0x00261613.
Lemma F_18868 : fetch_word Plain.M.loaded_segments (0x18964 : word) = Some W_18868.
Proof. vm_refl. Qed.
Lemma D_18868 : decode_any W_18868 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1886c : bv 32 := 0x660110ef.
Lemma F_1886c : fetch_word Plain.M.loaded_segments (0x18968 : word) = Some W_1886c.
Proof. vm_refl. Qed.
Lemma D_1886c : decode_any W_1886c = Some (Jal 1 71264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18870 : bv 32 := 0x00048513.
Lemma F_18870 : fetch_word Plain.M.loaded_segments (0x1896c : word) = Some W_18870.
Proof. vm_refl. Qed.
Lemma D_18870 : decode_any W_18870 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18874 : bv 32 := 0x01042583.
Lemma F_18874 : fetch_word Plain.M.loaded_segments (0x18970 : word) = Some W_18874.
Proof. vm_refl. Qed.
Lemma D_18874 : decode_any W_18874 = Some (Load SZ4 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18878 : bv 32 := 0x00b4a823.
Lemma F_18878 : fetch_word Plain.M.loaded_segments (0x18974 : word) = Some W_18878.
Proof. vm_refl. Qed.
Lemma D_18878 : decode_any W_18878 = Some (Store SZ4 9 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1887c : bv 32 := 0x00843583.
Lemma F_1887c : fetch_word Plain.M.loaded_segments (0x18978 : word) = Some W_1887c.
Proof. vm_refl. Qed.
Lemma D_1887c : decode_any W_1887c = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18880 : bv 32 := 0x00b4b423.
Lemma F_18880 : fetch_word Plain.M.loaded_segments (0x1897c : word) = Some W_18880.
Proof. vm_refl. Qed.
Lemma D_18880 : decode_any W_18880 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18884 : bv 32 := 0x0740006f.
Lemma F_18884 : fetch_word Plain.M.loaded_segments (0x18980 : word) = Some W_18884.
Proof. vm_refl. Qed.
Lemma D_18884 : decode_any W_18884 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188f8 : bv 32 := 0x01813083.
Lemma F_188f8 : fetch_word Plain.M.loaded_segments (0x189f4 : word) = Some W_188f8.
Proof. vm_refl. Qed.
Lemma D_188f8 : decode_any W_188f8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_188fc : bv 32 := 0x01013403.
Lemma F_188fc : fetch_word Plain.M.loaded_segments (0x189f8 : word) = Some W_188fc.
Proof. vm_refl. Qed.
Lemma D_188fc : decode_any W_188fc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18900 : bv 32 := 0x00813483.
Lemma F_18900 : fetch_word Plain.M.loaded_segments (0x189fc : word) = Some W_18900.
Proof. vm_refl. Qed.
Lemma D_18900 : decode_any W_18900 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18904 : bv 32 := 0x02010113.
Lemma F_18904 : fetch_word Plain.M.loaded_segments (0x18a00 : word) = Some W_18904.
Proof. vm_refl. Qed.
Lemma D_18904 : decode_any W_18904 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18908 : bv 32 := 0x00008067.
Lemma F_18908 : fetch_word Plain.M.loaded_segments (0x18a04 : word) = Some W_18908.
Proof. vm_refl. Qed.
Lemma D_18908 : decode_any W_18908 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
