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
Definition W_19738 : bv 32 := 0xfe010113.
Lemma F_19738 : fetch_word Ubsan.M.loaded_segments (0x19834 : word) = Some W_19738.
Proof. vm_refl. Qed.
Lemma D_19738 : decode_any W_19738 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1973c : bv 32 := 0x00113c23.
Lemma F_1973c : fetch_word Ubsan.M.loaded_segments (0x19838 : word) = Some W_1973c.
Proof. vm_refl. Qed.
Lemma D_1973c : decode_any W_1973c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19740 : bv 32 := 0x00813823.
Lemma F_19740 : fetch_word Ubsan.M.loaded_segments (0x1983c : word) = Some W_19740.
Proof. vm_refl. Qed.
Lemma D_19740 : decode_any W_19740 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19744 : bv 32 := 0x00913423.
Lemma F_19744 : fetch_word Ubsan.M.loaded_segments (0x19840 : word) = Some W_19744.
Proof. vm_refl. Qed.
Lemma D_19744 : decode_any W_19744 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19748 : bv 32 := 0x06050c63.
Lemma F_19748 : fetch_word Ubsan.M.loaded_segments (0x19844 : word) = Some W_19748.
Proof. vm_refl. Qed.
Lemma D_19748 : decode_any W_19748 = Some (Branch BC_EQ 10 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1974c : bv 32 := 0x00050413.
Lemma F_1974c : fetch_word Ubsan.M.loaded_segments (0x19848 : word) = Some W_1974c.
Proof. vm_refl. Qed.
Lemma D_1974c : decode_any W_1974c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19750 : bv 32 := 0x00410613.
Lemma F_19750 : fetch_word Ubsan.M.loaded_segments (0x1984c : word) = Some W_19750.
Proof. vm_refl. Qed.
Lemma D_19750 : decode_any W_19750 = Some (OpImm ALU_ADD 12 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19754 : bv 32 := 0x00000593.
Lemma F_19754 : fetch_word Ubsan.M.loaded_segments (0x19850 : word) = Some W_19754.
Proof. vm_refl. Qed.
Lemma D_19754 : decode_any W_19754 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19758 : bv 32 := 0x0f8000ef.
Lemma F_19758 : fetch_word Ubsan.M.loaded_segments (0x19854 : word) = Some W_19758.
Proof. vm_refl. Qed.
Lemma D_19758 : decode_any W_19758 = Some (Jal 1 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1975c : bv 32 := 0x00412503.
Lemma F_1975c : fetch_word Ubsan.M.loaded_segments (0x19858 : word) = Some W_1975c.
Proof. vm_refl. Qed.
Lemma D_1975c : decode_any W_1975c = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19760 : bv 32 := 0x08050e63.
Lemma F_19760 : fetch_word Ubsan.M.loaded_segments (0x1985c : word) = Some W_19760.
Proof. vm_refl. Qed.
Lemma D_19760 : decode_any W_19760 = Some (Branch BC_EQ 10 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19764 : bv 32 := 0x00100513.
Lemma F_19764 : fetch_word Ubsan.M.loaded_segments (0x19860 : word) = Some W_19764.
Proof. vm_refl. Qed.
Lemma D_19764 : decode_any W_19764 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19768 : bv 32 := 0x01800593.
Lemma F_19768 : fetch_word Ubsan.M.loaded_segments (0x19864 : word) = Some W_19768.
Proof. vm_refl. Qed.
Lemma D_19768 : decode_any W_19768 = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1976c : bv 32 := 0x081100ef.
Lemma F_1976c : fetch_word Ubsan.M.loaded_segments (0x19868 : word) = Some W_1976c.
Proof. vm_refl. Qed.
Lemma D_1976c : decode_any W_1976c = Some (Jal 1 67712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19770 : bv 32 := 0x00747593.
Lemma F_19770 : fetch_word Ubsan.M.loaded_segments (0x1986c : word) = Some W_19770.
Proof. vm_refl. Qed.
Lemma D_19770 : decode_any W_19770 = Some (OpImm ALU_AND 11 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19774 : bv 32 := 0x0c059c63.
Lemma F_19774 : fetch_word Ubsan.M.loaded_segments (0x19870 : word) = Some W_19774.
Proof. vm_refl. Qed.
Lemma D_19774 : decode_any W_19774 = Some (Branch BC_NE 11 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19778 : bv 32 := 0x00050493.
Lemma F_19778 : fetch_word Ubsan.M.loaded_segments (0x19874 : word) = Some W_19778.
Proof. vm_refl. Qed.
Lemma D_19778 : decode_any W_19778 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1977c : bv 32 := 0x00c42503.
Lemma F_1977c : fetch_word Ubsan.M.loaded_segments (0x19878 : word) = Some W_1977c.
Proof. vm_refl. Qed.
Lemma D_1977c : decode_any W_1977c = Some (Load SZ4 true 10 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19780 : bv 32 := 0x0025159b.
Lemma F_19780 : fetch_word Ubsan.M.loaded_segments (0x1987c : word) = Some W_19780.
Proof. vm_refl. Qed.
Lemma D_19780 : decode_any W_19780 = Some (ShiftImm32 ALU_SLL 11 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19784 : bv 32 := 0x00100513.
Lemma F_19784 : fetch_word Ubsan.M.loaded_segments (0x19880 : word) = Some W_19784.
Proof. vm_refl. Qed.
Lemma D_19784 : decode_any W_19784 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19788 : bv 32 := 0x065100ef.
Lemma F_19788 : fetch_word Ubsan.M.loaded_segments (0x19884 : word) = Some W_19788.
Proof. vm_refl. Qed.
Lemma D_19788 : decode_any W_19788 = Some (Jal 1 67684, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1978c : bv 32 := 0x0c048063.
Lemma F_1978c : fetch_word Ubsan.M.loaded_segments (0x19888 : word) = Some W_1978c.
Proof. vm_refl. Qed.
Lemma D_1978c : decode_any W_1978c = Some (Branch BC_EQ 9 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19790 : bv 32 := 0x0074f593.
Lemma F_19790 : fetch_word Ubsan.M.loaded_segments (0x1988c : word) = Some W_19790.
Proof. vm_refl. Qed.
Lemma D_19790 : decode_any W_19790 = Some (OpImm ALU_AND 11 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19794 : bv 32 := 0x0a059c63.
Lemma F_19794 : fetch_word Ubsan.M.loaded_segments (0x19890 : word) = Some W_19794.
Proof. vm_refl. Qed.
Lemma D_19794 : decode_any W_19794 = Some (Branch BC_NE 11 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19798 : bv 32 := 0x00a4b023.
Lemma F_19798 : fetch_word Ubsan.M.loaded_segments (0x19894 : word) = Some W_19798.
Proof. vm_refl. Qed.
Lemma D_19798 : decode_any W_19798 = Some (Store SZ8 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1979c : bv 32 := 0x01042603.
Lemma F_1979c : fetch_word Ubsan.M.loaded_segments (0x19898 : word) = Some W_1979c.
Proof. vm_refl. Qed.
Lemma D_1979c : decode_any W_1979c = Some (Load SZ4 true 12 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197a0 : bv 32 := 0x00043583.
Lemma F_197a0 : fetch_word Ubsan.M.loaded_segments (0x1989c : word) = Some W_197a0.
Proof. vm_refl. Qed.
Lemma D_197a0 : decode_any W_197a0 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197a4 : bv 32 := 0x00261613.
Lemma F_197a4 : fetch_word Ubsan.M.loaded_segments (0x198a0 : word) = Some W_197a4.
Proof. vm_refl. Qed.
Lemma D_197a4 : decode_any W_197a4 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197a8 : bv 32 := 0x2b1170ef.
Lemma F_197a8 : fetch_word Ubsan.M.loaded_segments (0x198a4 : word) = Some W_197a8.
Proof. vm_refl. Qed.
Lemma D_197a8 : decode_any W_197a8 = Some (Jal 1 96944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197ac : bv 32 := 0x01042503.
Lemma F_197ac : fetch_word Ubsan.M.loaded_segments (0x198a8 : word) = Some W_197ac.
Proof. vm_refl. Qed.
Lemma D_197ac : decode_any W_197ac = Some (Load SZ4 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197b0 : bv 32 := 0x00a4a823.
Lemma F_197b0 : fetch_word Ubsan.M.loaded_segments (0x198ac : word) = Some W_197b0.
Proof. vm_refl. Qed.
Lemma D_197b0 : decode_any W_197b0 = Some (Store SZ4 9 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197b4 : bv 32 := 0x00843503.
Lemma F_197b4 : fetch_word Ubsan.M.loaded_segments (0x198b0 : word) = Some W_197b4.
Proof. vm_refl. Qed.
Lemma D_197b4 : decode_any W_197b4 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197b8 : bv 32 := 0x00a4b423.
Lemma F_197b8 : fetch_word Ubsan.M.loaded_segments (0x198b4 : word) = Some W_197b8.
Proof. vm_refl. Qed.
Lemma D_197b8 : decode_any W_197b8 = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197bc : bv 32 := 0x0780006f.
Lemma F_197bc : fetch_word Ubsan.M.loaded_segments (0x198b8 : word) = Some W_197bc.
Proof. vm_refl. Qed.
Lemma D_197bc : decode_any W_197bc = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19834 : bv 32 := 0x00048513.
Lemma F_19834 : fetch_word Ubsan.M.loaded_segments (0x19930 : word) = Some W_19834.
Proof. vm_refl. Qed.
Lemma D_19834 : decode_any W_19834 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19838 : bv 32 := 0x01813083.
Lemma F_19838 : fetch_word Ubsan.M.loaded_segments (0x19934 : word) = Some W_19838.
Proof. vm_refl. Qed.
Lemma D_19838 : decode_any W_19838 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1983c : bv 32 := 0x01013403.
Lemma F_1983c : fetch_word Ubsan.M.loaded_segments (0x19938 : word) = Some W_1983c.
Proof. vm_refl. Qed.
Lemma D_1983c : decode_any W_1983c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19840 : bv 32 := 0x00813483.
Lemma F_19840 : fetch_word Ubsan.M.loaded_segments (0x1993c : word) = Some W_19840.
Proof. vm_refl. Qed.
Lemma D_19840 : decode_any W_19840 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19844 : bv 32 := 0x02010113.
Lemma F_19844 : fetch_word Ubsan.M.loaded_segments (0x19940 : word) = Some W_19844.
Proof. vm_refl. Qed.
Lemma D_19844 : decode_any W_19844 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19848 : bv 32 := 0x00008067.
Lemma F_19848 : fetch_word Ubsan.M.loaded_segments (0x19944 : word) = Some W_19848.
Proof. vm_refl. Qed.
Lemma D_19848 : decode_any W_19848 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
