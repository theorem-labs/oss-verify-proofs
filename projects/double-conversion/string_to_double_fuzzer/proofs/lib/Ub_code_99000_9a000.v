(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation USEGS := ImgU.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_99890 : bv 32 := 0x00062703.
Lemma F_99890 : fetch_word USEGS (0x99890 : word) = Some W_99890.
Proof. vm_refl. Qed.
Lemma D_99890 : decode_any W_99890 = Some (Load SZ4 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99894 : bv 32 := 0x00d777b3.
Lemma F_99894 : fetch_word USEGS (0x99894 : word) = Some W_99894.
Proof. vm_refl. Qed.
Lemma D_99894 : decode_any W_99894 = Some (Op ALU_AND 15 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99898 : bv 32 := 0x1606282f.
Lemma F_99898 : fetch_word USEGS (0x99898 : word) = Some W_99898.
Proof. vm_refl. Qed.
Lemma D_99898 : decode_any W_99898 = Some (Lr AW true true 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9989c : bv 32 := 0x00e81663.
Lemma F_9989c : fetch_word USEGS (0x9989c : word) = Some W_9989c.
Proof. vm_refl. Qed.
Lemma D_9989c : decode_any W_9989c = Some (Branch BC_NE 16 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998a0 : bv 32 := 0x1ef628af.
Lemma F_998a0 : fetch_word USEGS (0x998a0 : word) = Some W_998a0.
Proof. vm_refl. Qed.
Lemma D_998a0 : decode_any W_998a0 = Some (Sc AW true true 17 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998a4 : bv 32 := 0xfe089ae3.
Lemma F_998a4 : fetch_word USEGS (0x998a4 : word) = Some W_998a4.
Proof. vm_refl. Qed.
Lemma D_998a4 : decode_any W_998a4 = Some (Branch BC_NE 17 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998a8 : bv 32 := 0x0008081b.
Lemma F_998a8 : fetch_word USEGS (0x998a8 : word) = Some W_998a8.
Proof. vm_refl. Qed.
Lemma D_998a8 : decode_any W_998a8 = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998ac : bv 32 := 0xfee812e3.
Lemma F_998ac : fetch_word USEGS (0x998ac : word) = Some W_998ac.
Proof. vm_refl. Qed.
Lemma D_998ac : decode_any W_998ac = Some (Branch BC_NE 16 14 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998fc : bv 32 := 0x00d52c23.
Lemma F_998fc : fetch_word USEGS (0x998fc : word) = Some W_998fc.
Proof. vm_refl. Qed.
Lemma D_998fc : decode_any W_998fc = Some (Store SZ4 10 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99900 : bv 32 := 0x02060863.
Lemma F_99900 : fetch_word USEGS (0x99900 : word) = Some W_99900.
Proof. vm_refl. Qed.
Lemma D_99900 : decode_any W_99900 = Some (Branch BC_EQ 12 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99904 : bv 32 := 0x40b0053b.
Lemma F_99904 : fetch_word USEGS (0x99904 : word) = Some W_99904.
Proof. vm_refl. Qed.
Lemma D_99904 : decode_any W_99904 = Some (Op32 ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99908 : bv 32 := 0x00a5f533.
Lemma F_99908 : fetch_word USEGS (0x99908 : word) = Some W_99908.
Proof. vm_refl. Qed.
Lemma D_99908 : decode_any W_99908 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9990c : bv 32 := 0x077cb5b7.
Lemma F_9990c : fetch_word USEGS (0x9990c : word) = Some W_9990c.
Proof. vm_refl. Qed.
Lemma D_9990c : decode_any W_9990c = Some (Lui 11 30667, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99910 : bv 32 := 0x53158593.
Lemma F_99910 : fetch_word USEGS (0x99910 : word) = Some W_99910.
Proof. vm_refl. Qed.
Lemma D_99910 : decode_any W_99910 = Some (OpImm ALU_ADD 11 11 1329, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99914 : bv 32 := 0x02b50533.
Lemma F_99914 : fetch_word USEGS (0x99914 : word) = Some W_99914.
Proof. vm_refl. Qed.
Lemma D_99914 : decode_any W_99914 = Some (Mul M_MUL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99918 : bv 32 := 0xfff81597.
Lemma F_99918 : fetch_word USEGS (0x99918 : word) = Some W_99918.
Proof. vm_refl. Qed.
Lemma D_99918 : decode_any W_99918 = Some (Auipc 11 1048449, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9991c : bv 32 := 0x01b5551b.
Lemma F_9991c : fetch_word USEGS (0x9991c : word) = Some W_9991c.
Proof. vm_refl. Qed.
Lemma D_9991c : decode_any W_9991c = Some (ShiftImm32 ALU_SRL 10 10 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99920 : bv 32 := 0x29058593.
Lemma F_99920 : fetch_word USEGS (0x99920 : word) = Some W_99920.
Proof. vm_refl. Qed.
Lemma D_99920 : decode_any W_99920 = Some (OpImm ALU_ADD 11 11 656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99924 : bv 32 := 0x00a58533.
Lemma F_99924 : fetch_word USEGS (0x99924 : word) = Some W_99924.
Proof. vm_refl. Qed.
Lemma D_99924 : decode_any W_99924 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99928 : bv 32 := 0x00054503.
Lemma F_99928 : fetch_word USEGS (0x99928 : word) = Some W_99928.
Proof. vm_refl. Qed.
Lemma D_99928 : decode_any W_99928 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9992c : bv 32 := 0x6840006f.
Lemma F_9992c : fetch_word USEGS (0x9992c : word) = Some W_9992c.
Proof. vm_refl. Qed.
Lemma D_9992c : decode_any W_9992c = Some (Jal 0 1668, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99930 : bv 32 := 0x00141993.
Lemma F_99930 : fetch_word USEGS (0x99930 : word) = Some W_99930.
Proof. vm_refl. Qed.
Lemma D_99930 : decode_any W_99930 = Some (ShiftImm ALU_SLL 19 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99934 : bv 32 := 0xfff81517.
Lemma F_99934 : fetch_word USEGS (0x99934 : word) = Some W_99934.
Proof. vm_refl. Qed.
Lemma D_99934 : decode_any W_99934 = Some (Auipc 10 1048449, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99938 : bv 32 := 0x29450c93.
Lemma F_99938 : fetch_word USEGS (0x99938 : word) = Some W_99938.
Proof. vm_refl. Qed.
Lemma D_99938 : decode_any W_99938 = Some (OpImm ALU_ADD 25 10 660, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9993c : bv 32 := 0x013c8533.
Lemma F_9993c : fetch_word USEGS (0x9993c : word) = Some W_9993c.
Proof. vm_refl. Qed.
Lemma D_9993c : decode_any W_9993c = Some (Op ALU_ADD 10 25 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99940 : bv 32 := 0x00055c03.
Lemma F_99940 : fetch_word USEGS (0x99940 : word) = Some W_99940.
Proof. vm_refl. Qed.
Lemma D_99940 : decode_any W_99940 = Some (Load SZ2 false 24 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99944 : bv 32 := 0xfc4ff0ef.
Lemma F_99944 : fetch_word USEGS (0x99944 : word) = Some W_99944.
Proof. vm_refl. Qed.
Lemma D_99944 : decode_any W_99944 = Some (Jal 1 2095044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99948 : bv 32 := 0x00050493.
Lemma F_99948 : fetch_word USEGS (0x99948 : word) = Some W_99948.
Proof. vm_refl. Qed.
Lemma D_99948 : decode_any W_99948 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9994c : bv 32 := 0xfff00513.
Lemma F_9994c : fetch_word USEGS (0x9994c : word) = Some W_9994c.
Proof. vm_refl. Qed.
Lemma D_9994c : decode_any W_9994c = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99950 : bv 32 := 0x66048063.
Lemma F_99950 : fetch_word USEGS (0x99950 : word) = Some W_99950.
Proof. vm_refl. Qed.
Lemma D_99950 : decode_any W_99950 = Some (Branch BC_EQ 9 0 1632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99954 : bv 32 := 0x1d8bb503.
Lemma F_99954 : fetch_word USEGS (0x99954 : word) = Some W_99954.
Proof. vm_refl. Qed.
Lemma D_99954 : decode_any W_99954 = Some (Load SZ8 true 10 23 472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99958 : bv 32 := 0x0004c597.
Lemma F_99958 : fetch_word USEGS (0x99958 : word) = Some W_99958.
Proof. vm_refl. Qed.
Lemma D_99958 : decode_any W_99958 = Some (Auipc 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9995c : bv 32 := 0x9805b583.
Lemma F_9995c : fetch_word USEGS (0x9995c : word) = Some W_9995c.
Proof. vm_refl. Qed.
Lemma D_9995c : decode_any W_9995c = Some (Load SZ8 true 11 11 2432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99960 : bv 32 := 0x00800613.
Lemma F_99960 : fetch_word USEGS (0x99960 : word) = Some W_99960.
Proof. vm_refl. Qed.
Lemma D_99960 : decode_any W_99960 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99964 : bv 32 := 0x004c1c13.
Lemma F_99964 : fetch_word USEGS (0x99964 : word) = Some W_99964.
Proof. vm_refl. Qed.
Lemma D_99964 : decode_any W_99964 = Some (ShiftImm ALU_SLL 24 24 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99968 : bv 32 := 0x02864a63.
Lemma F_99968 : fetch_word USEGS (0x99968 : word) = Some W_99968.
Proof. vm_refl. Qed.
Lemma D_99968 : decode_any W_99968 = Some (Branch BC_LT 12 8 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9996c : bv 32 := 0x00898633.
Lemma F_9996c : fetch_word USEGS (0x9996c : word) = Some W_9996c.
Proof. vm_refl. Qed.
Lemma D_9996c : decode_any W_9996c = Some (Op ALU_ADD 12 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99970 : bv 32 := 0xfff81697.
Lemma F_99970 : fetch_word USEGS (0x99970 : word) = Some W_99970.
Proof. vm_refl. Qed.
Lemma D_99970 : decode_any W_99970 = Some (Auipc 13 1048449, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99978 : bv 32 := 0x00c68633.
Lemma F_99978 : fetch_word USEGS (0x99978 : word) = Some W_99978.
Proof. vm_refl. Qed.
Lemma D_99978 : decode_any W_99978 = Some (Op ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9997c : bv 32 := 0x00064983.
Lemma F_9997c : fetch_word USEGS (0x9997c : word) = Some W_9997c.
Proof. vm_refl. Qed.
Lemma D_9997c : decode_any W_9997c = Some (Load SZ1 false 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99980 : bv 32 := 0x00299693.
Lemma F_99980 : fetch_word USEGS (0x99980 : word) = Some W_99980.
Proof. vm_refl. Qed.
Lemma D_99980 : decode_any W_99980 = Some (ShiftImm ALU_SLL 13 19 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99984 : bv 32 := 0x06d57863.
Lemma F_99984 : fetch_word USEGS (0x99984 : word) = Some W_99984.
Proof. vm_refl. Qed.
Lemma D_99984 : decode_any W_99984 = Some (Branch BC_GEU 10 13 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99988 : bv 32 := 0x00164983.
Lemma F_99988 : fetch_word USEGS (0x99988 : word) = Some W_99988.
Proof. vm_refl. Qed.
Lemma D_99988 : decode_any W_99988 = Some (Load SZ1 false 19 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9998c : bv 32 := 0x00299693.
Lemma F_9998c : fetch_word USEGS (0x9998c : word) = Some W_9998c.
Proof. vm_refl. Qed.
Lemma D_9998c : decode_any W_9998c = Some (ShiftImm ALU_SLL 13 19 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99990 : bv 32 := 0x06d57263.
Lemma F_99990 : fetch_word USEGS (0x99990 : word) = Some W_99990.
Proof. vm_refl. Qed.
Lemma D_99990 : decode_any W_99990 = Some (Branch BC_GEU 10 13 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99994 : bv 32 := 0x00264983.
Lemma F_99994 : fetch_word USEGS (0x99994 : word) = Some W_99994.
Proof. vm_refl. Qed.
Lemma D_99994 : decode_any W_99994 = Some (Load SZ1 false 19 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99998 : bv 32 := 0x05c0006f.
Lemma F_99998 : fetch_word USEGS (0x99998 : word) = Some W_99998.
Proof. vm_refl. Qed.
Lemma D_99998 : decode_any W_99998 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9999c : bv 32 := 0x00347613.
Lemma F_9999c : fetch_word USEGS (0x9999c : word) = Some W_9999c.
Proof. vm_refl. Qed.
Lemma D_9999c : decode_any W_9999c = Some (OpImm ALU_AND 12 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999a0 : bv 32 := 0xfff7a697.
Lemma F_999a0 : fetch_word USEGS (0x999a0 : word) = Some W_999a0.
Proof. vm_refl. Qed.
Lemma D_999a0 : decode_any W_999a0 = Some (Auipc 13 1048442, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999a4 : bv 32 := 0xa6468693.
Lemma F_999a4 : fetch_word USEGS (0x999a4 : word) = Some W_999a4.
Proof. vm_refl. Qed.
Lemma D_999a4 : decode_any W_999a4 = Some (OpImm ALU_ADD 13 13 2660, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999a8 : bv 32 := 0x00c68633.
Lemma F_999a8 : fetch_word USEGS (0x999a8 : word) = Some W_999a8.
Proof. vm_refl. Qed.
Lemma D_999a8 : decode_any W_999a8 = Some (Op ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999ac : bv 32 := 0x00064683.
Lemma F_999ac : fetch_word USEGS (0x999ac : word) = Some W_999ac.
Proof. vm_refl. Qed.
Lemma D_999ac : decode_any W_999ac = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999b4 : bv 32 := 0x02061063.
Lemma F_999b4 : fetch_word USEGS (0x999b4 : word) = Some W_999b4.
Proof. vm_refl. Qed.
Lemma D_999b4 : decode_any W_999b4 = Some (Branch BC_NE 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999b8 : bv 32 := 0x0026961b.
Lemma F_999b8 : fetch_word USEGS (0x999b8 : word) = Some W_999b8.
Proof. vm_refl. Qed.
Lemma D_999b8 : decode_any W_999b8 = Some (ShiftImm32 ALU_SLL 12 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999bc : bv 32 := 0x02c57063.
Lemma F_999bc : fetch_word USEGS (0x999bc : word) = Some W_999bc.
Proof. vm_refl. Qed.
Lemma D_999bc : decode_any W_999bc = Some (Branch BC_GEU 10 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999c0 : bv 32 := 0x0016d61b.
Lemma F_999c0 : fetch_word USEGS (0x999c0 : word) = Some W_999c0.
Proof. vm_refl. Qed.
Lemma D_999c0 : decode_any W_999c0 = Some (ShiftImm32 ALU_SRL 12 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999c4 : bv 32 := 0x0026f713.
Lemma F_999c4 : fetch_word USEGS (0x999c4 : word) = Some W_999c4.
Proof. vm_refl. Qed.
Lemma D_999c4 : decode_any W_999c4 = Some (OpImm ALU_AND 14 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999c8 : bv 32 := 0x00060693.
Lemma F_999c8 : fetch_word USEGS (0x999c8 : word) = Some W_999c8.
Proof. vm_refl. Qed.
Lemma D_999c8 : decode_any W_999c8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999cc : bv 32 := 0xfe0706e3.
Lemma F_999cc : fetch_word USEGS (0x999cc : word) = Some W_999cc.
Proof. vm_refl. Qed.
Lemma D_999cc : decode_any W_999cc = Some (Branch BC_EQ 14 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999d0 : bv 32 := 0x0100006f.
Lemma F_999d0 : fetch_word USEGS (0x999d0 : word) = Some W_999d0.
Proof. vm_refl. Qed.
Lemma D_999d0 : decode_any W_999d0 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999d4 : bv 32 := 0x00068613.
Lemma F_999d4 : fetch_word USEGS (0x999d4 : word) = Some W_999d4.
Proof. vm_refl. Qed.
Lemma D_999d4 : decode_any W_999d4 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999d8 : bv 32 := 0x0080006f.
Lemma F_999d8 : fetch_word USEGS (0x999d8 : word) = Some W_999d8.
Proof. vm_refl. Qed.
Lemma D_999d8 : decode_any W_999d8 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999dc : bv 32 := 0x00068613.
Lemma F_999dc : fetch_word USEGS (0x999dc : word) = Some W_999dc.
Proof. vm_refl. Qed.
Lemma D_999dc : decode_any W_999dc = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999e0 : bv 32 := 0x00060993.
Lemma F_999e0 : fetch_word USEGS (0x999e0 : word) = Some W_999e0.
Proof. vm_refl. Qed.
Lemma D_999e0 : decode_any W_999e0 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999e4 : bv 32 := 0x02cc0633.
Lemma F_999e4 : fetch_word USEGS (0x999e4 : word) = Some W_999e4.
Proof. vm_refl. Qed.
Lemma D_999e4 : decode_any W_999e4 = Some (Mul M_MUL 12 24 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999e8 : bv 32 := 0x01465693.
Lemma F_999e8 : fetch_word USEGS (0x999e8 : word) = Some W_999e8.
Proof. vm_refl. Qed.
Lemma D_999e8 : decode_any W_999e8 = Some (ShiftImm ALU_SRL 13 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999ec : bv 32 := 0x0019d61b.
Lemma F_999ec : fetch_word USEGS (0x999ec : word) = Some W_999ec.
Proof. vm_refl. Qed.
Lemma D_999ec : decode_any W_999ec = Some (ShiftImm32 ALU_SRL 12 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999f0 : bv 32 := 0xfe0698e3.
Lemma F_999f0 : fetch_word USEGS (0x999f0 : word) = Some W_999f0.
Proof. vm_refl. Qed.
Lemma D_999f0 : decode_any W_999f0 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999f4 : bv 32 := 0x010c0613.
Lemma F_999f4 : fetch_word USEGS (0x999f4 : word) = Some W_999f4.
Proof. vm_refl. Qed.
Lemma D_999f4 : decode_any W_999f4 = Some (OpImm ALU_ADD 12 24 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999f8 : bv 32 := 0x00100713.
Lemma F_999f8 : fetch_word USEGS (0x999f8 : word) = Some W_999f8.
Proof. vm_refl. Qed.
Lemma D_999f8 : decode_any W_999f8 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_999fc : bv 32 := 0x0015d693.
Lemma F_999fc : fetch_word USEGS (0x999fc : word) = Some W_999fc.
Proof. vm_refl. Qed.
Lemma D_999fc : decode_any W_999fc = Some (ShiftImm ALU_SRL 13 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a00 : bv 32 := 0x00e99863.
Lemma F_99a00 : fetch_word USEGS (0x99a00 : word) = Some W_99a00.
Proof. vm_refl. Qed.
Lemma D_99a00 : decode_any W_99a00 = Some (Branch BC_NE 19 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a04 : bv 32 := 0x00c6b733.
Lemma F_99a04 : fetch_word USEGS (0x99a04 : word) = Some W_99a04.
Proof. vm_refl. Qed.
Lemma D_99a04 : decode_any W_99a04 = Some (Op ALU_SLTU 14 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a08 : bv 32 := 0x00200793.
Lemma F_99a08 : fetch_word USEGS (0x99a08 : word) = Some W_99a08.
Proof. vm_refl. Qed.
Lemma D_99a08 : decode_any W_99a08 = Some (OpImm ALU_ADD 15 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a0c : bv 32 := 0x40e789bb.
Lemma F_99a0c : fetch_word USEGS (0x99a0c : word) = Some W_99a0c.
Proof. vm_refl. Qed.
Lemma D_99a0c : decode_any W_99a0c = Some (Op32 ALU_SUB 19 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a10 : bv 32 := 0x033c0733.
Lemma F_99a10 : fetch_word USEGS (0x99a10 : word) = Some W_99a10.
Proof. vm_refl. Qed.
Lemma D_99a10 : decode_any W_99a10 = Some (Mul M_MUL 14 24 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a14 : bv 32 := 0x01070793.
Lemma F_99a14 : fetch_word USEGS (0x99a14 : word) = Some W_99a14.
Proof. vm_refl. Qed.
Lemma D_99a14 : decode_any W_99a14 = Some (OpImm ALU_ADD 15 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a18 : bv 32 := 0x04f6f463.
Lemma F_99a18 : fetch_word USEGS (0x99a18 : word) = Some W_99a18.
Proof. vm_refl. Qed.
Lemma D_99a18 : decode_any W_99a18 = Some (Branch BC_GEU 13 15 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a1c : bv 32 := 0xff94079b.
Lemma F_99a1c : fetch_word USEGS (0x99a1c : word) = Some W_99a1c.
Proof. vm_refl. Qed.
Lemma D_99a1c : decode_any W_99a1c = Some (OpImm32 15 8 4089, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a20 : bv 32 := 0x01f00693.
Lemma F_99a20 : fetch_word USEGS (0x99a20 : word) = Some W_99a20.
Proof. vm_refl. Qed.
Lemma D_99a20 : decode_any W_99a20 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a24 : bv 32 := 0x0cf6ec63.
Lemma F_99a24 : fetch_word USEGS (0x99a24 : word) = Some W_99a24.
Proof. vm_refl. Qed.
Lemma D_99a24 : decode_any W_99a24 = Some (Branch BC_LTU 13 15 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a28 : bv 32 := 0x00fb07b3.
Lemma F_99a28 : fetch_word USEGS (0x99a28 : word) = Some W_99a28.
Proof. vm_refl. Qed.
Lemma D_99a28 : decode_any W_99a28 = Some (Op ALU_ADD 15 22 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a2c : bv 32 := 0x3787c883.
Lemma F_99a2c : fetch_word USEGS (0x99a2c : word) = Some W_99a2c.
Proof. vm_refl. Qed.
Lemma D_99a2c : decode_any W_99a2c = Some (Load SZ1 false 17 15 888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a30 : bv 32 := 0x3587c283.
Lemma F_99a30 : fetch_word USEGS (0x99a30 : word) = Some W_99a30.
Proof. vm_refl. Qed.
Lemma D_99a30 : decode_any W_99a30 = Some (Load SZ1 false 5 15 856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a34 : bv 32 := 0x0648b693.
Lemma F_99a34 : fetch_word USEGS (0x99a34 : word) = Some W_99a34.
Proof. vm_refl. Qed.
Lemma D_99a34 : decode_any W_99a34 = Some (OpImm ALU_SLTU 13 17 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a38 : bv 32 := 0x0016c693.
Lemma F_99a38 : fetch_word USEGS (0x99a38 : word) = Some W_99a38.
Proof. vm_refl. Qed.
Lemma D_99a38 : decode_any W_99a38 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a3c : bv 32 := 0x28028863.
Lemma F_99a3c : fetch_word USEGS (0x99a3c : word) = Some W_99a3c.
Proof. vm_refl. Qed.
Lemma D_99a3c : decode_any W_99a3c = Some (Branch BC_EQ 5 0 656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a40 : bv 32 := 0x398b4803.
Lemma F_99a40 : fetch_word USEGS (0x99a40 : word) = Some W_99a40.
Proof. vm_refl. Qed.
Lemma D_99a40 : decode_any W_99a40 = Some (Load SZ1 false 16 22 920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a44 : bv 32 := 0x405802b3.
Lemma F_99a44 : fetch_word USEGS (0x99a44 : word) = Some W_99a44.
Proof. vm_refl. Qed.
Lemma D_99a44 : decode_any W_99a44 = Some (Op ALU_SUB 5 16 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99a48 : bv 32 := 0x00900313.
Lemma F_99a48 : fetch_word USEGS (0x99a48 : word) = Some W_99a48.
Proof. vm_refl. Qed.
Lemma D_99a48 : decode_any W_99a48 = Some (OpImm ALU_ADD 6 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ff4 : bv 32 := 0x02053703.
Lemma F_99ff4 : fetch_word USEGS (0x99ff4 : word) = Some W_99ff4.
Proof. vm_refl. Qed.
Lemma D_99ff4 : decode_any W_99ff4 = Some (Load SZ8 true 14 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ff8 : bv 32 := 0x00c75793.
Lemma F_99ff8 : fetch_word USEGS (0x99ff8 : word) = Some W_99ff8.
Proof. vm_refl. Qed.
Lemma D_99ff8 : decode_any W_99ff8 = Some (ShiftImm ALU_SRL 15 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ffc : bv 32 := 0x00078e63.
Lemma F_99ffc : fetch_word USEGS (0x99ffc : word) = Some W_99ffc.
Proof. vm_refl. Qed.
Lemma D_99ffc : decode_any W_99ffc = Some (Branch BC_EQ 15 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a000 : bv 32 := 0x01f77793.
Lemma F_9a000 : fetch_word USEGS (0x9a000 : word) = Some W_9a000.
Proof. vm_refl. Qed.
Lemma D_9a000 : decode_any W_9a000 = Some (OpImm ALU_AND 15 14 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a004 : bv 32 := 0x00079a63.
Lemma F_9a004 : fetch_word USEGS (0x9a004 : word) = Some W_9a004.
Proof. vm_refl. Qed.
Lemma D_9a004 : decode_any W_9a004 = Some (Branch BC_NE 15 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a008 : bv 32 := 0xfffff7b7.
Lemma F_9a008 : fetch_word USEGS (0x9a008 : word) = Some W_9a008.
Proof. vm_refl. Qed.
Lemma D_9a008 : decode_any W_9a008 = Some (Lui 15 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a00c : bv 32 := 0x00f77733.
Lemma F_9a00c : fetch_word USEGS (0x9a00c : word) = Some W_9a00c.
Proof. vm_refl. Qed.
Lemma D_9a00c : decode_any W_9a00c = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a010 : bv 32 := 0xff070713.
Lemma F_9a010 : fetch_word USEGS (0x9a010 : word) = Some W_9a010.
Proof. vm_refl. Qed.
Lemma D_9a010 : decode_any W_9a010 = Some (OpImm ALU_ADD 14 14 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a014 : bv 32 := 0x0200006f.
Lemma F_9a014 : fetch_word USEGS (0x9a014 : word) = Some W_9a014.
Proof. vm_refl. Qed.
Lemma D_9a014 : decode_any W_9a014 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a018 : bv 32 := 0x00575713.
Lemma F_9a018 : fetch_word USEGS (0x9a018 : word) = Some W_9a018.
Proof. vm_refl. Qed.
Lemma D_9a018 : decode_any W_9a018 = Some (ShiftImm ALU_SRL 14 14 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a01c : bv 32 := 0xfff81797.
Lemma F_9a01c : fetch_word USEGS (0x9a01c : word) = Some W_9a01c.
Proof. vm_refl. Qed.
Lemma D_9a01c : decode_any W_9a01c = Some (Auipc 15 1048449, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a020 : bv 32 := 0x07e77713.
Lemma F_9a020 : fetch_word USEGS (0x9a020 : word) = Some W_9a020.
Proof. vm_refl. Qed.
Lemma D_9a020 : decode_any W_9a020 = Some (OpImm ALU_AND 14 14 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a024 : bv 32 := 0xbac78793.
Lemma F_9a024 : fetch_word USEGS (0x9a024 : word) = Some W_9a024.
Proof. vm_refl. Qed.
Lemma D_9a024 : decode_any W_9a024 = Some (OpImm ALU_ADD 15 15 2988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a028 : bv 32 := 0x00e78733.
Lemma F_9a028 : fetch_word USEGS (0x9a028 : word) = Some W_9a028.
Proof. vm_refl. Qed.
Lemma D_9a028 : decode_any W_9a028 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a02c : bv 32 := 0x00075703.
Lemma F_9a02c : fetch_word USEGS (0x9a02c : word) = Some W_9a02c.
Proof. vm_refl. Qed.
Lemma D_9a02c : decode_any W_9a02c = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a030 : bv 32 := 0x00471713.
Lemma F_9a030 : fetch_word USEGS (0x9a030 : word) = Some W_9a030.
Proof. vm_refl. Qed.
Lemma D_9a030 : decode_any W_9a030 = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a034 : bv 32 := 0x01053803.
Lemma F_9a034 : fetch_word USEGS (0x9a034 : word) = Some W_9a034.
Proof. vm_refl. Qed.
Lemma D_9a034 : decode_any W_9a034 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a038 : bv 32 := 0x02b707b3.
Lemma F_9a038 : fetch_word USEGS (0x9a038 : word) = Some W_9a038.
Proof. vm_refl. Qed.
Lemma D_9a038 : decode_any W_9a038 = Some (Mul M_MUL 15 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a03c : bv 32 := 0x00f807b3.
Lemma F_9a03c : fetch_word USEGS (0x9a03c : word) = Some W_9a03c.
Proof. vm_refl. Qed.
Lemma D_9a03c : decode_any W_9a03c = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a040 : bv 32 := 0x00d7c883.
Lemma F_9a040 : fetch_word USEGS (0x9a040 : word) = Some W_9a040.
Proof. vm_refl. Qed.
Lemma D_9a040 : decode_any W_9a040 = Some (Load SZ1 false 17 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a044 : bv 32 := 0x40c702b3.
Lemma F_9a044 : fetch_word USEGS (0x9a044 : word) = Some W_9a044.
Proof. vm_refl. Qed.
Lemma D_9a044 : decode_any W_9a044 = Some (Op ALU_SUB 5 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a048 : bv 32 := 0xffc28293.
Lemma F_9a048 : fetch_word USEGS (0x9a048 : word) = Some W_9a048.
Proof. vm_refl. Qed.
Lemma D_9a048 : decode_any W_9a048 = Some (OpImm ALU_ADD 5 5 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a04c : bv 32 := 0x01078793.
Lemma F_9a04c : fetch_word USEGS (0x9a04c : word) = Some W_9a04c.
Proof. vm_refl. Qed.
Lemma D_9a04c : decode_any W_9a04c = Some (OpImm ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a050 : bv 32 := 0x00088663.
Lemma F_9a050 : fetch_word USEGS (0x9a050 : word) = Some W_9a050.
Proof. vm_refl. Qed.
Lemma D_9a050 : decode_any W_9a050 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a054 : bv 32 := 0xffe7d683.
Lemma F_9a054 : fetch_word USEGS (0x9a054 : word) = Some W_9a054.
Proof. vm_refl. Qed.
Lemma D_9a054 : decode_any W_9a054 = Some (Load SZ2 false 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a058 : bv 32 := 0x00168693.
Lemma F_9a058 : fetch_word USEGS (0x9a058 : word) = Some W_9a058.
Proof. vm_refl. Qed.
Lemma D_9a058 : decode_any W_9a058 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a05c : bv 32 := 0xffc7c383.
Lemma F_9a05c : fetch_word USEGS (0x9a05c : word) = Some W_9a05c.
Proof. vm_refl. Qed.
Lemma D_9a05c : decode_any W_9a05c = Some (Load SZ1 false 7 15 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a060 : bv 32 := 0x0042d313.
Lemma F_9a060 : fetch_word USEGS (0x9a060 : word) = Some W_9a060.
Proof. vm_refl. Qed.
Lemma D_9a060 : decode_any W_9a060 = Some (ShiftImm ALU_SRL 6 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a064 : bv 32 := 0x0ff6f893.
Lemma F_9a064 : fetch_word USEGS (0x9a064 : word) = Some W_9a064.
Proof. vm_refl. Qed.
Lemma D_9a064 : decode_any W_9a064 = Some (OpImm ALU_AND 17 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a068 : bv 32 := 0x00038463.
Lemma F_9a068 : fetch_word USEGS (0x9a068 : word) = Some W_9a068.
Proof. vm_refl. Qed.
Lemma D_9a068 : decode_any W_9a068 = Some (Branch BC_EQ 7 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a070 : bv 32 := 0x03137e63.
Lemma F_9a070 : fetch_word USEGS (0x9a070 : word) = Some W_9a070.
Proof. vm_refl. Qed.
Lemma D_9a070 : decode_any W_9a070 = Some (Branch BC_GEU 6 17 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a074 : bv 32 := 0x0052d693.
Lemma F_9a074 : fetch_word USEGS (0x9a074 : word) = Some W_9a074.
Proof. vm_refl. Qed.
Lemma D_9a074 : decode_any W_9a074 = Some (ShiftImm ALU_SRL 13 5 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a078 : bv 32 := 0x00d366b3.
Lemma F_9a078 : fetch_word USEGS (0x9a078 : word) = Some W_9a078.
Proof. vm_refl. Qed.
Lemma D_9a078 : decode_any W_9a078 = Some (Op ALU_OR 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a07c : bv 32 := 0x0026d293.
Lemma F_9a07c : fetch_word USEGS (0x9a07c : word) = Some W_9a07c.
Proof. vm_refl. Qed.
Lemma D_9a07c : decode_any W_9a07c = Some (ShiftImm ALU_SRL 5 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a080 : bv 32 := 0x00d2e6b3.
Lemma F_9a080 : fetch_word USEGS (0x9a080 : word) = Some W_9a080.
Proof. vm_refl. Qed.
Lemma D_9a080 : decode_any W_9a080 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a084 : bv 32 := 0x0046d293.
Lemma F_9a084 : fetch_word USEGS (0x9a084 : word) = Some W_9a084.
Proof. vm_refl. Qed.
Lemma D_9a084 : decode_any W_9a084 = Some (ShiftImm ALU_SRL 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a088 : bv 32 := 0x00d2e6b3.
Lemma F_9a088 : fetch_word USEGS (0x9a088 : word) = Some W_9a088.
Proof. vm_refl. Qed.
Lemma D_9a088 : decode_any W_9a088 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a08c : bv 32 := 0x00d8f6b3.
Lemma F_9a08c : fetch_word USEGS (0x9a08c : word) = Some W_9a08c.
Proof. vm_refl. Qed.
Lemma D_9a08c : decode_any W_9a08c = Some (Op ALU_AND 13 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a090 : bv 32 := 0x00d338b3.
Lemma F_9a090 : fetch_word USEGS (0x9a090 : word) = Some W_9a090.
Proof. vm_refl. Qed.
Lemma D_9a090 : decode_any W_9a090 = Some (Op ALU_SLTU 17 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a094 : bv 32 := 0xfff34293.
Lemma F_9a094 : fetch_word USEGS (0x9a094 : word) = Some W_9a094.
Proof. vm_refl. Qed.
Lemma D_9a094 : decode_any W_9a094 = Some (OpImm ALU_XOR 5 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a098 : bv 32 := 0x411008bb.
Lemma F_9a098 : fetch_word USEGS (0x9a098 : word) = Some W_9a098.
Proof. vm_refl. Qed.
Lemma D_9a098 : decode_any W_9a098 = Some (Op32 ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a09c : bv 32 := 0x0058f8b3.
Lemma F_9a09c : fetch_word USEGS (0x9a09c : word) = Some W_9a09c.
Proof. vm_refl. Qed.
Lemma D_9a09c : decode_any W_9a09c = Some (Op ALU_AND 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0a0 : bv 32 := 0x00d888bb.
Lemma F_9a0a0 : fetch_word USEGS (0x9a0a0 : word) = Some W_9a0a0.
Proof. vm_refl. Qed.
Lemma D_9a0a0 : decode_any W_9a0a0 = Some (Op32 ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0a4 : bv 32 := 0x01137463.
Lemma F_9a0a4 : fetch_word USEGS (0x9a0a4 : word) = Some W_9a0a4.
Proof. vm_refl. Qed.
Lemma D_9a0a4 : decode_any W_9a0a4 = Some (Branch BC_GEU 6 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0ac : bv 32 := 0x00078693.
Lemma F_9a0ac : fetch_word USEGS (0x9a0ac : word) = Some W_9a0ac.
Proof. vm_refl. Qed.
Lemma D_9a0ac : decode_any W_9a0ac = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0b0 : bv 32 := 0x02088063.
Lemma F_9a0b0 : fetch_word USEGS (0x9a0b0 : word) = Some W_9a0b0.
Proof. vm_refl. Qed.
Lemma D_9a0b0 : decode_any W_9a0b0 = Some (Branch BC_EQ 17 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0b4 : bv 32 := 0xfe000813.
Lemma F_9a0b4 : fetch_word USEGS (0x9a0b4 : word) = Some W_9a0b4.
Proof. vm_refl. Qed.
Lemma D_9a0b4 : decode_any W_9a0b4 = Some (OpImm ALU_ADD 16 0 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0b8 : bv 32 := 0x0048969b.
Lemma F_9a0b8 : fetch_word USEGS (0x9a0b8 : word) = Some W_9a0b8.
Proof. vm_refl. Qed.
Lemma D_9a0b8 : decode_any W_9a0b8 = Some (ShiftImm32 ALU_SLL 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0bc : bv 32 := 0x00d786b3.
Lemma F_9a0bc : fetch_word USEGS (0x9a0bc : word) = Some W_9a0bc.
Proof. vm_refl. Qed.
Lemma D_9a0bc : decode_any W_9a0bc = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0c0 : bv 32 := 0xff078ea3.
Lemma F_9a0c0 : fetch_word USEGS (0x9a0c0 : word) = Some W_9a0c0.
Proof. vm_refl. Qed.
Lemma D_9a0c0 : decode_any W_9a0c0 = Some (Store SZ1 15 16 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0c4 : bv 32 := 0xff179f23.
Lemma F_9a0c4 : fetch_word USEGS (0x9a0c4 : word) = Some W_9a0c4.
Proof. vm_refl. Qed.
Lemma D_9a0c4 : decode_any W_9a0c4 = Some (Store SZ2 15 17 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0c8 : bv 32 := 0xfe068e23.
Lemma F_9a0c8 : fetch_word USEGS (0x9a0c8 : word) = Some W_9a0c8.
Proof. vm_refl. Qed.
Lemma D_9a0c8 : decode_any W_9a0c8 = Some (Store SZ1 13 0 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0cc : bv 32 := 0x01053803.
Lemma F_9a0cc : fetch_word USEGS (0x9a0cc : word) = Some W_9a0cc.
Proof. vm_refl. Qed.
Lemma D_9a0cc : decode_any W_9a0cc = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0d0 : bv 32 := 0x00e78733.
Lemma F_9a0d0 : fetch_word USEGS (0x9a0d0 : word) = Some W_9a0d0.
Proof. vm_refl. Qed.
Lemma D_9a0d0 : decode_any W_9a0d0 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0d4 : bv 32 := 0x410687bb.
Lemma F_9a0d4 : fetch_word USEGS (0x9a0d4 : word) = Some W_9a0d4.
Proof. vm_refl. Qed.
Lemma D_9a0d4 : decode_any W_9a0d4 = Some (Op32 ALU_SUB 15 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0d8 : bv 32 := 0x00d60633.
Lemma F_9a0d8 : fetch_word USEGS (0x9a0d8 : word) = Some W_9a0d8.
Proof. vm_refl. Qed.
Lemma D_9a0d8 : decode_any W_9a0d8 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0dc : bv 32 := 0xffc70513.
Lemma F_9a0dc : fetch_word USEGS (0x9a0dc : word) = Some W_9a0dc.
Proof. vm_refl. Qed.
Lemma D_9a0dc : decode_any W_9a0dc = Some (OpImm ALU_ADD 10 14 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0e0 : bv 32 := 0xff078793.
Lemma F_9a0e0 : fetch_word USEGS (0x9a0e0 : word) = Some W_9a0e0.
Proof. vm_refl. Qed.
Lemma D_9a0e0 : decode_any W_9a0e0 = Some (OpImm ALU_ADD 15 15 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0e4 : bv 32 := 0x0047d793.
Lemma F_9a0e4 : fetch_word USEGS (0x9a0e4 : word) = Some W_9a0e4.
Proof. vm_refl. Qed.
Lemma D_9a0e4 : decode_any W_9a0e4 = Some (ShiftImm ALU_SRL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0e8 : bv 32 := 0x40c5083b.
Lemma F_9a0e8 : fetch_word USEGS (0x9a0e8 : word) = Some W_9a0e8.
Proof. vm_refl. Qed.
Lemma D_9a0e8 : decode_any W_9a0e8 = Some (Op32 ALU_SUB 16 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0ec : bv 32 := 0xfeb68ea3.
Lemma F_9a0ec : fetch_word USEGS (0x9a0ec : word) = Some W_9a0ec.
Proof. vm_refl. Qed.
Lemma D_9a0ec : decode_any W_9a0ec = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0f0 : bv 32 := 0xfef69f23.
Lemma F_9a0f0 : fetch_word USEGS (0x9a0f0 : word) = Some W_9a0f0.
Proof. vm_refl. Qed.
Lemma D_9a0f0 : decode_any W_9a0f0 = Some (Store SZ2 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0f4 : bv 32 := 0x02080463.
Lemma F_9a0f4 : fetch_word USEGS (0x9a0f4 : word) = Some W_9a0f4.
Proof. vm_refl. Qed.
Lemma D_9a0f4 : decode_any W_9a0f4 = Some (Branch BC_EQ 16 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0f8 : bv 32 := 0x40c505bb.
Lemma F_9a0f8 : fetch_word USEGS (0x9a0f8 : word) = Some W_9a0f8.
Proof. vm_refl. Qed.
Lemma D_9a0f8 : decode_any W_9a0f8 = Some (Op32 ALU_SUB 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a0fc : bv 32 := 0x40b0063b.
Lemma F_9a0fc : fetch_word USEGS (0x9a0fc : word) = Some W_9a0fc.
Proof. vm_refl. Qed.
Lemma D_9a0fc : decode_any W_9a0fc = Some (Op32 ALU_SUB 12 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a100 : bv 32 := 0x00c50633.
Lemma F_9a100 : fetch_word USEGS (0x9a100 : word) = Some W_9a100.
Proof. vm_refl. Qed.
Lemma D_9a100 : decode_any W_9a100 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a104 : bv 32 := 0x00500513.
Lemma F_9a104 : fetch_word USEGS (0x9a104 : word) = Some W_9a104.
Proof. vm_refl. Qed.
Lemma D_9a104 : decode_any W_9a104 = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a108 : bv 32 := 0x00060023.
Lemma F_9a108 : fetch_word USEGS (0x9a108 : word) = Some W_9a108.
Proof. vm_refl. Qed.
Lemma D_9a108 : decode_any W_9a108 = Some (Store SZ1 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a10c : bv 32 := 0x00a5cc63.
Lemma F_9a10c : fetch_word USEGS (0x9a10c : word) = Some W_9a10c.
Proof. vm_refl. Qed.
Lemma D_9a10c : decode_any W_9a10c = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a110 : bv 32 := 0xfe070ba3.
Lemma F_9a110 : fetch_word USEGS (0x9a110 : word) = Some W_9a110.
Proof. vm_refl. Qed.
Lemma D_9a110 : decode_any W_9a110 = Some (Store SZ1 14 0 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a114 : bv 32 := 0xfeb72c23.
Lemma F_9a114 : fetch_word USEGS (0x9a114 : word) = Some W_9a114.
Proof. vm_refl. Qed.
Lemma D_9a114 : decode_any W_9a114 = Some (Store SZ4 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a118 : bv 32 := 0x0100006f.
Lemma F_9a118 : fetch_word USEGS (0x9a118 : word) = Some W_9a118.
Proof. vm_refl. Qed.
Lemma D_9a118 : decode_any W_9a118 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a11c : bv 32 := 0x00000513.
Lemma F_9a11c : fetch_word USEGS (0x9a11c : word) = Some W_9a11c.
Proof. vm_refl. Qed.
Lemma D_9a11c : decode_any W_9a11c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a120 : bv 32 := 0x0080006f.
Lemma F_9a120 : fetch_word USEGS (0x9a120 : word) = Some W_9a120.
Proof. vm_refl. Qed.
Lemma D_9a120 : decode_any W_9a120 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a124 : bv 32 := 0x00058513.
Lemma F_9a124 : fetch_word USEGS (0x9a124 : word) = Some W_9a124.
Proof. vm_refl. Qed.
Lemma D_9a124 : decode_any W_9a124 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a128 : bv 32 := 0xffd6c583.
Lemma F_9a128 : fetch_word USEGS (0x9a128 : word) = Some W_9a128.
Proof. vm_refl. Qed.
Lemma D_9a128 : decode_any W_9a128 = Some (Load SZ1 false 11 13 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a12c : bv 32 := 0x01f5f593.
Lemma F_9a12c : fetch_word USEGS (0x9a12c : word) = Some W_9a12c.
Proof. vm_refl. Qed.
Lemma D_9a12c : decode_any W_9a12c = Some (OpImm ALU_AND 11 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a130 : bv 32 := 0x00551513.
Lemma F_9a130 : fetch_word USEGS (0x9a130 : word) = Some W_9a130.
Proof. vm_refl. Qed.
Lemma D_9a130 : decode_any W_9a130 = Some (ShiftImm ALU_SLL 10 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a134 : bv 32 := 0x00b56533.
Lemma F_9a134 : fetch_word USEGS (0x9a134 : word) = Some W_9a134.
Proof. vm_refl. Qed.
Lemma D_9a134 : decode_any W_9a134 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a138 : bv 32 := 0xfea68ea3.
Lemma F_9a138 : fetch_word USEGS (0x9a138 : word) = Some W_9a138.
Proof. vm_refl. Qed.
Lemma D_9a138 : decode_any W_9a138 = Some (Store SZ1 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a13c : bv 32 := 0x00068513.
Lemma F_9a13c : fetch_word USEGS (0x9a13c : word) = Some W_9a13c.
Proof. vm_refl. Qed.
Lemma D_9a13c : decode_any W_9a13c = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a140 : bv 32 := 0x00008067.
Lemma F_9a140 : fetch_word USEGS (0x9a140 : word) = Some W_9a140.
Proof. vm_refl. Qed.
Lemma D_9a140 : decode_any W_9a140 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

