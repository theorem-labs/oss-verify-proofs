(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_994c4 : bv 32 := 0x00050593.
Lemma F_994c4 : fetch_word Plain.M.loaded_segments (0x99510 : word) = Some W_994c4.
Proof. vm_refl. Qed.
Lemma D_994c4 : decode_any W_994c4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_994c8 : bv 32 := 0x05e00893.
Lemma F_994c8 : fetch_word Plain.M.loaded_segments (0x99514 : word) = Some W_994c8.
Proof. vm_refl. Qed.
Lemma D_994c8 : decode_any W_994c8 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_994cc : bv 32 := 0x00000073.
Lemma F_994cc : fetch_word Plain.M.loaded_segments (0x99518 : word) = Some W_994cc.
Proof. vm_refl. Qed.
Lemma D_994cc : decode_any W_994cc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_994cc : is_ecall W_994cc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_99770 : bv 32 := 0xfe010113.
Lemma F_99770 : fetch_word Plain.M.loaded_segments (0x997bc : word) = Some W_99770.
Proof. vm_refl. Qed.
Lemma D_99770 : decode_any W_99770 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99774 : bv 32 := 0x00113c23.
Lemma F_99774 : fetch_word Plain.M.loaded_segments (0x997c0 : word) = Some W_99774.
Proof. vm_refl. Qed.
Lemma D_99774 : decode_any W_99774 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99778 : bv 32 := 0x00813823.
Lemma F_99778 : fetch_word Plain.M.loaded_segments (0x997c4 : word) = Some W_99778.
Proof. vm_refl. Qed.
Lemma D_99778 : decode_any W_99778 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9977c : bv 32 := 0x00913423.
Lemma F_9977c : fetch_word Plain.M.loaded_segments (0x997c8 : word) = Some W_9977c.
Proof. vm_refl. Qed.
Lemma D_9977c : decode_any W_9977c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99780 : bv 32 := 0x0001c517.
Lemma F_99780 : fetch_word Plain.M.loaded_segments (0x997cc : word) = Some W_99780.
Proof. vm_refl. Qed.
Lemma D_99780 : decode_any W_99780 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99784 : bv 32 := 0x0001c597.
Lemma F_99784 : fetch_word Plain.M.loaded_segments (0x997d0 : word) = Some W_99784.
Proof. vm_refl. Qed.
Lemma D_99784 : decode_any W_99784 = Some (Auipc 11 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99788 : bv 32 := 0x43c53503.
Lemma F_99788 : fetch_word Plain.M.loaded_segments (0x997d4 : word) = Some W_99788.
Proof. vm_refl. Qed.
Lemma D_99788 : decode_any W_99788 = Some (Load SZ8 true 10 10 1084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9978c : bv 32 := 0x4405b403.
Lemma F_9978c : fetch_word Plain.M.loaded_segments (0x997d8 : word) = Some W_9978c.
Proof. vm_refl. Qed.
Lemma D_9978c : decode_any W_9978c = Some (Load SZ8 true 8 11 1088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99790 : bv 32 := 0x00a47c63.
Lemma F_99790 : fetch_word Plain.M.loaded_segments (0x997dc : word) = Some W_99790.
Proof. vm_refl. Qed.
Lemma D_99790 : decode_any W_99790 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99794 : bv 32 := 0xff853583.
Lemma F_99794 : fetch_word Plain.M.loaded_segments (0x997e0 : word) = Some W_99794.
Proof. vm_refl. Qed.
Lemma D_99794 : decode_any W_99794 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99798 : bv 32 := 0xff850493.
Lemma F_99798 : fetch_word Plain.M.loaded_segments (0x997e4 : word) = Some W_99798.
Proof. vm_refl. Qed.
Lemma D_99798 : decode_any W_99798 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9979c : bv 32 := 0x000580e7.
Lemma F_9979c : fetch_word Plain.M.loaded_segments (0x997e8 : word) = Some W_9979c.
Proof. vm_refl. Qed.
Lemma D_9979c : decode_any W_9979c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997a0 : bv 32 := 0x00048513.
Lemma F_997a0 : fetch_word Plain.M.loaded_segments (0x997ec : word) = Some W_997a0.
Proof. vm_refl. Qed.
Lemma D_997a0 : decode_any W_997a0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997a4 : bv 32 := 0xfe9468e3.
Lemma F_997a4 : fetch_word Plain.M.loaded_segments (0x997f0 : word) = Some W_997a4.
Proof. vm_refl. Qed.
Lemma D_997a4 : decode_any W_997a4 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997a8 : bv 32 := 0x01813083.
Lemma F_997a8 : fetch_word Plain.M.loaded_segments (0x997f4 : word) = Some W_997a8.
Proof. vm_refl. Qed.
Lemma D_997a8 : decode_any W_997a8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997ac : bv 32 := 0x01013403.
Lemma F_997ac : fetch_word Plain.M.loaded_segments (0x997f8 : word) = Some W_997ac.
Proof. vm_refl. Qed.
Lemma D_997ac : decode_any W_997ac = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997b0 : bv 32 := 0x00813483.
Lemma F_997b0 : fetch_word Plain.M.loaded_segments (0x997fc : word) = Some W_997b0.
Proof. vm_refl. Qed.
Lemma D_997b0 : decode_any W_997b0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997b4 : bv 32 := 0x02010113.
Lemma F_997b4 : fetch_word Plain.M.loaded_segments (0x99800 : word) = Some W_997b4.
Proof. vm_refl. Qed.
Lemma D_997b4 : decode_any W_997b4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997b8 : bv 32 := 0xfb5ff06f.
Lemma F_997b8 : fetch_word Plain.M.loaded_segments (0x99804 : word) = Some W_997b8.
Proof. vm_refl. Qed.
Lemma D_997b8 : decode_any W_997b8 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997bc : bv 32 := 0xff010113.
Lemma F_997bc : fetch_word Plain.M.loaded_segments (0x99808 : word) = Some W_997bc.
Proof. vm_refl. Qed.
Lemma D_997bc : decode_any W_997bc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997c0 : bv 32 := 0x00113423.
Lemma F_997c0 : fetch_word Plain.M.loaded_segments (0x9980c : word) = Some W_997c0.
Proof. vm_refl. Qed.
Lemma D_997c0 : decode_any W_997c0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997c4 : bv 32 := 0x00813023.
Lemma F_997c4 : fetch_word Plain.M.loaded_segments (0x99810 : word) = Some W_997c4.
Proof. vm_refl. Qed.
Lemma D_997c4 : decode_any W_997c4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997c8 : bv 32 := 0x00000593.
Lemma F_997c8 : fetch_word Plain.M.loaded_segments (0x99814 : word) = Some W_997c8.
Proof. vm_refl. Qed.
Lemma D_997c8 : decode_any W_997c8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997cc : bv 32 := 0x00020613.
Lemma F_997cc : fetch_word Plain.M.loaded_segments (0x99818 : word) = Some W_997cc.
Proof. vm_refl. Qed.
Lemma D_997cc : decode_any W_997cc = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997d0 : bv 32 := 0xf5862603.
Lemma F_997d0 : fetch_word Plain.M.loaded_segments (0x9981c : word) = Some W_997d0.
Proof. vm_refl. Qed.
Lemma D_997d0 : decode_any W_997d0 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997d4 : bv 32 := 0x0004f697.
Lemma F_997d4 : fetch_word Plain.M.loaded_segments (0x99820 : word) = Some W_997d4.
Proof. vm_refl. Qed.
Lemma D_997d4 : decode_any W_997d4 = Some (Auipc 13 79, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997d8 : bv 32 := 0x42868693.
Lemma F_997d8 : fetch_word Plain.M.loaded_segments (0x99824 : word) = Some W_997d8.
Proof. vm_refl. Qed.
Lemma D_997d8 : decode_any W_997d8 = Some (OpImm ALU_ADD 13 13 1064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997dc : bv 32 := 0x1606a72f.
Lemma F_997dc : fetch_word Plain.M.loaded_segments (0x99828 : word) = Some W_997dc.
Proof. vm_refl. Qed.
Lemma D_997dc : decode_any W_997dc = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997e0 : bv 32 := 0x00b71663.
Lemma F_997e0 : fetch_word Plain.M.loaded_segments (0x9982c : word) = Some W_997e0.
Proof. vm_refl. Qed.
Lemma D_997e0 : decode_any W_997e0 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997e4 : bv 32 := 0x1ec6a7af.
Lemma F_997e4 : fetch_word Plain.M.loaded_segments (0x99830 : word) = Some W_997e4.
Proof. vm_refl. Qed.
Lemma D_997e4 : decode_any W_997e4 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997e8 : bv 32 := 0xfe079ae3.
Lemma F_997e8 : fetch_word Plain.M.loaded_segments (0x99834 : word) = Some W_997e8.
Proof. vm_refl. Qed.
Lemma D_997e8 : decode_any W_997e8 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997ec : bv 32 := 0x0007059b.
Lemma F_997ec : fetch_word Plain.M.loaded_segments (0x99838 : word) = Some W_997ec.
Proof. vm_refl. Qed.
Lemma D_997ec : decode_any W_997ec = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997f0 : bv 32 := 0x02c58263.
Lemma F_997f0 : fetch_word Plain.M.loaded_segments (0x9983c : word) = Some W_997f0.
Proof. vm_refl. Qed.
Lemma D_997f0 : decode_any W_997f0 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_997f4 : bv 32 := 0x02058263.
Lemma F_997f4 : fetch_word Plain.M.loaded_segments (0x99840 : word) = Some W_997f4.
Proof. vm_refl. Qed.
Lemma D_997f4 : decode_any W_997f4 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99818 : bv 32 := 0x00050413.
Lemma F_99818 : fetch_word Plain.M.loaded_segments (0x99864 : word) = Some W_99818.
Proof. vm_refl. Qed.
Lemma D_99818 : decode_any W_99818 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9981c : bv 32 := 0xcf5ff0ef.
Lemma F_9981c : fetch_word Plain.M.loaded_segments (0x99868 : word) = Some W_9981c.
Proof. vm_refl. Qed.
Lemma D_9981c : decode_any W_9981c = Some (Jal 1 2096372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99820 : bv 32 := 0xf51ff0ef.
Lemma F_99820 : fetch_word Plain.M.loaded_segments (0x9986c : word) = Some W_99820.
Proof. vm_refl. Qed.
Lemma D_99820 : decode_any W_99820 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99824 : bv 32 := 0x5a0050ef.
Lemma F_99824 : fetch_word Plain.M.loaded_segments (0x99870 : word) = Some W_99824.
Proof. vm_refl. Qed.
Lemma D_99824 : decode_any W_99824 = Some (Jal 1 21920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99828 : bv 32 := 0x00040513.
Lemma F_99828 : fetch_word Plain.M.loaded_segments (0x99874 : word) = Some W_99828.
Proof. vm_refl. Qed.
Lemma D_99828 : decode_any W_99828 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9982c : bv 32 := 0xc99ff0ef.
Lemma F_9982c : fetch_word Plain.M.loaded_segments (0x99878 : word) = Some W_9982c.
Proof. vm_refl. Qed.
Lemma D_9982c : decode_any W_9982c = Some (Jal 1 2096280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99914 : bv 32 := 0xff010113.
Lemma F_99914 : fetch_word Plain.M.loaded_segments (0x99960 : word) = Some W_99914.
Proof. vm_refl. Qed.
Lemma D_99914 : decode_any W_99914 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99918 : bv 32 := 0x00113423.
Lemma F_99918 : fetch_word Plain.M.loaded_segments (0x99964 : word) = Some W_99918.
Proof. vm_refl. Qed.
Lemma D_99918 : decode_any W_99918 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9991c : bv 32 := 0x00050e63.
Lemma F_9991c : fetch_word Plain.M.loaded_segments (0x99968 : word) = Some W_9991c.
Proof. vm_refl. Qed.
Lemma D_9991c : decode_any W_9991c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99920 : bv 32 := 0x00050593.
Lemma F_99920 : fetch_word Plain.M.loaded_segments (0x9996c : word) = Some W_99920.
Proof. vm_refl. Qed.
Lemma D_99920 : decode_any W_99920 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99924 : bv 32 := 0x0001c517.
Lemma F_99924 : fetch_word Plain.M.loaded_segments (0x99970 : word) = Some W_99924.
Proof. vm_refl. Qed.
Lemma D_99924 : decode_any W_99924 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99928 : bv 32 := 0x29053503.
Lemma F_99928 : fetch_word Plain.M.loaded_segments (0x99974 : word) = Some W_99928.
Proof. vm_refl. Qed.
Lemma D_99928 : decode_any W_99928 = Some (Load SZ8 true 10 10 656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9992c : bv 32 := 0x00800613.
Lemma F_9992c : fetch_word Plain.M.loaded_segments (0x99978 : word) = Some W_9992c.
Proof. vm_refl. Qed.
Lemma D_9992c : decode_any W_9992c = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99930 : bv 32 := 0x51c100ef.
Lemma F_99930 : fetch_word Plain.M.loaded_segments (0x9997c : word) = Some W_99930.
Proof. vm_refl. Qed.
Lemma D_99930 : decode_any W_99930 = Some (Jal 1 66844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99934 : bv 32 := 0x01c0006f.
Lemma F_99934 : fetch_word Plain.M.loaded_segments (0x99980 : word) = Some W_99934.
Proof. vm_refl. Qed.
Lemma D_99934 : decode_any W_99934 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99950 : bv 32 := 0x0001c517.
Lemma F_99950 : fetch_word Plain.M.loaded_segments (0x9999c : word) = Some W_99950.
Proof. vm_refl. Qed.
Lemma D_99950 : decode_any W_99950 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99954 : bv 32 := 0x26453503.
Lemma F_99954 : fetch_word Plain.M.loaded_segments (0x999a0 : word) = Some W_99954.
Proof. vm_refl. Qed.
Lemma D_99954 : decode_any W_99954 = Some (Load SZ8 true 10 10 612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99958 : bv 32 := 0x000500a3.
Lemma F_99958 : fetch_word Plain.M.loaded_segments (0x999a4 : word) = Some W_99958.
Proof. vm_refl. Qed.
Lemma D_99958 : decode_any W_99958 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9995c : bv 32 := 0x00053503.
Lemma F_9995c : fetch_word Plain.M.loaded_segments (0x999a8 : word) = Some W_9995c.
Proof. vm_refl. Qed.
Lemma D_9995c : decode_any W_9995c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99960 : bv 32 := 0x00020593.
Lemma F_99960 : fetch_word Plain.M.loaded_segments (0x999ac : word) = Some W_99960.
Proof. vm_refl. Qed.
Lemma D_99960 : decode_any W_99960 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99964 : bv 32 := 0xfea5b823.
Lemma F_99964 : fetch_word Plain.M.loaded_segments (0x999b0 : word) = Some W_99964.
Proof. vm_refl. Qed.
Lemma D_99964 : decode_any W_99964 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99968 : bv 32 := 0x00813083.
Lemma F_99968 : fetch_word Plain.M.loaded_segments (0x999b4 : word) = Some W_99968.
Proof. vm_refl. Qed.
Lemma D_99968 : decode_any W_99968 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9996c : bv 32 := 0x01010113.
Lemma F_9996c : fetch_word Plain.M.loaded_segments (0x999b8 : word) = Some W_9996c.
Proof. vm_refl. Qed.
Lemma D_9996c : decode_any W_9996c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99970 : bv 32 := 0x00008067.
Lemma F_99970 : fetch_word Plain.M.loaded_segments (0x999bc : word) = Some W_99970.
Proof. vm_refl. Qed.
Lemma D_99970 : decode_any W_99970 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9997c : bv 32 := 0xfffff5b7.
Lemma F_9997c : fetch_word Plain.M.loaded_segments (0x999c8 : word) = Some W_9997c.
Proof. vm_refl. Qed.
Lemma D_9997c : decode_any W_9997c = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99980 : bv 32 := 0x0015859b.
Lemma F_99980 : fetch_word Plain.M.loaded_segments (0x999cc : word) = Some W_99980.
Proof. vm_refl. Qed.
Lemma D_99980 : decode_any W_99980 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99984 : bv 32 := 0x02b56663.
Lemma F_99984 : fetch_word Plain.M.loaded_segments (0x999d0 : word) = Some W_99984.
Proof. vm_refl. Qed.
Lemma D_99984 : decode_any W_99984 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999b0 : bv 32 := 0x00008067.
Lemma F_999b0 : fetch_word Plain.M.loaded_segments (0x999fc : word) = Some W_999b0.
Proof. vm_refl. Qed.
Lemma D_999b0 : decode_any W_999b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
