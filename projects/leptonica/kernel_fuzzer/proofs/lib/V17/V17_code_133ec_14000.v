(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.H Require GcFlushU17.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_1395c : bv 32 := 0xfd010113.
Lemma F_1395c : fetch_word Ubsan.M.loaded_segments (0x13a58 : word) = Some W_1395c.
Proof. vm_refl. Qed.
Lemma D_1395c : decode_any W_1395c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13960 : bv 32 := 0x02113423.
Lemma F_13960 : fetch_word Ubsan.M.loaded_segments (0x13a5c : word) = Some W_13960.
Proof. vm_refl. Qed.
Lemma D_13960 : decode_any W_13960 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13964 : bv 32 := 0x02813023.
Lemma F_13964 : fetch_word Ubsan.M.loaded_segments (0x13a60 : word) = Some W_13964.
Proof. vm_refl. Qed.
Lemma D_13964 : decode_any W_13964 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13968 : bv 32 := 0x00913c23.
Lemma F_13968 : fetch_word Ubsan.M.loaded_segments (0x13a64 : word) = Some W_13968.
Proof. vm_refl. Qed.
Lemma D_13968 : decode_any W_13968 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1396c : bv 32 := 0x00058413.
Lemma F_1396c : fetch_word Ubsan.M.loaded_segments (0x13a68 : word) = Some W_1396c.
Proof. vm_refl. Qed.
Lemma D_1396c : decode_any W_1396c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13970 : bv 32 := 0x00300593.
Lemma F_13970 : fetch_word Ubsan.M.loaded_segments (0x13a6c : word) = Some W_13970.
Proof. vm_refl. Qed.
Lemma D_13970 : decode_any W_13970 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13974 : bv 32 := 0x04b46463.
Lemma F_13974 : fetch_word Ubsan.M.loaded_segments (0x13a70 : word) = Some W_13974.
Proof. vm_refl. Qed.
Lemma D_13974 : decode_any W_13974 = Some (Branch BC_LTU 8 11 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13978 : bv 32 := 0x00050493.
Lemma F_13978 : fetch_word Ubsan.M.loaded_segments (0x13a74 : word) = Some W_13978.
Proof. vm_refl. Qed.
Lemma D_13978 : decode_any W_13978 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1397c : bv 32 := 0x00000517.
Lemma F_1397c : fetch_word Ubsan.M.loaded_segments (0x13a78 : word) = Some W_1397c.
Proof. vm_refl. Qed.
Lemma D_1397c : decode_any W_1397c = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13980 : bv 32 := 0x05850513.
Lemma F_13980 : fetch_word Ubsan.M.loaded_segments (0x13a7c : word) = Some W_13980.
Proof. vm_refl. Qed.
Lemma D_13980 : decode_any W_13980 = Some (OpImm ALU_ADD 10 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13984 : bv 32 := 0x170000ef.
Lemma F_13984 : fetch_word Ubsan.M.loaded_segments (0x13a80 : word) = Some W_13984.
Proof. vm_refl. Qed.
Lemma D_13984 : decode_any W_13984 = Some (Jal 1 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13988 : bv 32 := 0x00048513.
Lemma F_13988 : fetch_word Ubsan.M.loaded_segments (0x13a84 : word) = Some W_13988.
Proof. vm_refl. Qed.
Lemma D_13988 : decode_any W_13988 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1398c : bv 32 := 0x00040593.
Lemma F_1398c : fetch_word Ubsan.M.loaded_segments (0x13a88 : word) = Some W_1398c.
Proof. vm_refl. Qed.
Lemma D_1398c : decode_any W_1398c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13990 : bv 32 := 0x525010ef.
Lemma F_13990 : fetch_word Ubsan.M.loaded_segments (0x13a8c : word) = Some W_13990.
Proof. vm_refl. Qed.
Lemma D_13990 : decode_any W_13990 = Some (Jal 1 7460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13994 : bv 32 := 0x00a13823.
Lemma F_13994 : fetch_word Ubsan.M.loaded_segments (0x13a90 : word) = Some W_13994.
Proof. vm_refl. Qed.
Lemma D_13994 : decode_any W_13994 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13998 : bv 32 := 0x02050263.
Lemma F_13998 : fetch_word Ubsan.M.loaded_segments (0x13a94 : word) = Some W_13998.
Proof. vm_refl. Qed.
Lemma D_13998 : decode_any W_13998 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1399c : bv 32 := 0x00200593.
Lemma F_1399c : fetch_word Ubsan.M.loaded_segments (0x13a98 : word) = Some W_1399c.
Proof. vm_refl. Qed.
Lemma D_1399c : decode_any W_1399c = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139a0 : bv 32 := 0x00200613.
Lemma F_139a0 : fetch_word Ubsan.M.loaded_segments (0x13a9c : word) = Some W_139a0.
Proof. vm_refl. Qed.
Lemma D_139a0 : decode_any W_139a0 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139a4 : bv 32 := 0x6b8020ef.
Lemma F_139a4 : fetch_word Ubsan.M.loaded_segments (0x13aa0 : word) = Some W_139a4.
Proof. vm_refl. Qed.
Lemma D_139a4 : decode_any W_139a4 = Some (Jal 1 9912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139a8 : bv 32 := 0x00a13423.
Lemma F_139a8 : fetch_word Ubsan.M.loaded_segments (0x13aa4 : word) = Some W_139a8.
Proof. vm_refl. Qed.
Lemma D_139a8 : decode_any W_139a8 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139ac : bv 32 := 0x01010513.
Lemma F_139ac : fetch_word Ubsan.M.loaded_segments (0x13aa8 : word) = Some W_139ac.
Proof. vm_refl. Qed.
Lemma D_139ac : decode_any W_139ac = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139b0 : bv 32 := 0x6b8000ef.
Lemma F_139b0 : fetch_word Ubsan.M.loaded_segments (0x13aac : word) = Some W_139b0.
Proof. vm_refl. Qed.
Lemma D_139b0 : decode_any W_139b0 = Some (Jal 1 1720, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139b4 : bv 32 := 0x00810513.
Lemma F_139b4 : fetch_word Ubsan.M.loaded_segments (0x13ab0 : word) = Some W_139b4.
Proof. vm_refl. Qed.
Lemma D_139b4 : decode_any W_139b4 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139b8 : bv 32 := 0x48c020ef.
Lemma F_139b8 : fetch_word Ubsan.M.loaded_segments (0x13ab4 : word) = Some W_139b8.
Proof. vm_refl. Qed.
Lemma D_139b8 : decode_any W_139b8 = Some (Jal 1 9356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139bc : bv 32 := 0x00000513.
Lemma F_139bc : fetch_word Ubsan.M.loaded_segments (0x13ab8 : word) = Some W_139bc.
Proof. vm_refl. Qed.
Lemma D_139bc : decode_any W_139bc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139c0 : bv 32 := 0x02813083.
Lemma F_139c0 : fetch_word Ubsan.M.loaded_segments (0x13abc : word) = Some W_139c0.
Proof. vm_refl. Qed.
Lemma D_139c0 : decode_any W_139c0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139c4 : bv 32 := 0x02013403.
Lemma F_139c4 : fetch_word Ubsan.M.loaded_segments (0x13ac0 : word) = Some W_139c4.
Proof. vm_refl. Qed.
Lemma D_139c4 : decode_any W_139c4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139c8 : bv 32 := 0x01813483.
Lemma F_139c8 : fetch_word Ubsan.M.loaded_segments (0x13ac4 : word) = Some W_139c8.
Proof. vm_refl. Qed.
Lemma D_139c8 : decode_any W_139c8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139cc : bv 32 := 0x03010113.
Lemma F_139cc : fetch_word Ubsan.M.loaded_segments (0x13ac8 : word) = Some W_139cc.
Proof. vm_refl. Qed.
Lemma D_139cc : decode_any W_139cc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139d0 : bv 32 := 0x00008067.
Lemma F_139d0 : fetch_word Ubsan.M.loaded_segments (0x13acc : word) = Some W_139d0.
Proof. vm_refl. Qed.
Lemma D_139d0 : decode_any W_139d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139d8 : bv 32 := 0xff010113.
Lemma F_139d8 : fetch_word Ubsan.M.loaded_segments (0x13ad4 : word) = Some W_139d8.
Proof. vm_refl. Qed.
Lemma D_139d8 : decode_any W_139d8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139dc : bv 32 := 0x00113423.
Lemma F_139dc : fetch_word Ubsan.M.loaded_segments (0x13ad8 : word) = Some W_139dc.
Proof. vm_refl. Qed.
Lemma D_139dc : decode_any W_139dc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139e0 : bv 32 := 0x00813023.
Lemma F_139e0 : fetch_word Ubsan.M.loaded_segments (0x13adc : word) = Some W_139e0.
Proof. vm_refl. Qed.
Lemma D_139e0 : decode_any W_139e0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139e4 : bv 32 := 0x00060413.
Lemma F_139e4 : fetch_word Ubsan.M.loaded_segments (0x13ae0 : word) = Some W_139e4.
Proof. vm_refl. Qed.
Lemma D_139e4 : decode_any W_139e4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139e8 : bv 32 := 0x00050613.
Lemma F_139e8 : fetch_word Ubsan.M.loaded_segments (0x13ae4 : word) = Some W_139e8.
Proof. vm_refl. Qed.
Lemma D_139e8 : decode_any W_139e8 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139ec : bv 32 := 0xffffd517.
Lemma F_139ec : fetch_word Ubsan.M.loaded_segments (0x13ae8 : word) = Some W_139ec.
Proof. vm_refl. Qed.
Lemma D_139ec : decode_any W_139ec = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139f0 : bv 32 := 0x09950513.
Lemma F_139f0 : fetch_word Ubsan.M.loaded_segments (0x13aec : word) = Some W_139f0.
Proof. vm_refl. Qed.
Lemma D_139f0 : decode_any W_139f0 = Some (OpImm ALU_ADD 10 10 153, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139f4 : bv 32 := 0x018000ef.
Lemma F_139f4 : fetch_word Ubsan.M.loaded_segments (0x13af0 : word) = Some W_139f4.
Proof. vm_refl. Qed.
Lemma D_139f4 : decode_any W_139f4 = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139f8 : bv 32 := 0x00040513.
Lemma F_139f8 : fetch_word Ubsan.M.loaded_segments (0x13af4 : word) = Some W_139f8.
Proof. vm_refl. Qed.
Lemma D_139f8 : decode_any W_139f8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139fc : bv 32 := 0x00813083.
Lemma F_139fc : fetch_word Ubsan.M.loaded_segments (0x13af8 : word) = Some W_139fc.
Proof. vm_refl. Qed.
Lemma D_139fc : decode_any W_139fc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a00 : bv 32 := 0x00013403.
Lemma F_13a00 : fetch_word Ubsan.M.loaded_segments (0x13afc : word) = Some W_13a00.
Proof. vm_refl. Qed.
Lemma D_13a00 : decode_any W_13a00 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a04 : bv 32 := 0x01010113.
Lemma F_13a04 : fetch_word Ubsan.M.loaded_segments (0x13b00 : word) = Some W_13a04.
Proof. vm_refl. Qed.
Lemma D_13a04 : decode_any W_13a04 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a08 : bv 32 := 0x00008067.
Lemma F_13a08 : fetch_word Ubsan.M.loaded_segments (0x13b04 : word) = Some W_13a08.
Proof. vm_refl. Qed.
Lemma D_13a08 : decode_any W_13a08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13aa8 : bv 32 := 0xff010113.
Lemma F_13aa8 : fetch_word Ubsan.M.loaded_segments (0x13ba4 : word) = Some W_13aa8.
Proof. vm_refl. Qed.
Lemma D_13aa8 : decode_any W_13aa8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13aac : bv 32 := 0x00113423.
Lemma F_13aac : fetch_word Ubsan.M.loaded_segments (0x13ba8 : word) = Some W_13aac.
Proof. vm_refl. Qed.
Lemma D_13aac : decode_any W_13aac = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ab0 : bv 32 := 0x00813023.
Lemma F_13ab0 : fetch_word Ubsan.M.loaded_segments (0x13bac : word) = Some W_13ab0.
Proof. vm_refl. Qed.
Lemma D_13ab0 : decode_any W_13ab0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ab4 : bv 32 := 0x00060413.
Lemma F_13ab4 : fetch_word Ubsan.M.loaded_segments (0x13bb0 : word) = Some W_13ab4.
Proof. vm_refl. Qed.
Lemma D_13ab4 : decode_any W_13ab4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ab8 : bv 32 := 0x00050613.
Lemma F_13ab8 : fetch_word Ubsan.M.loaded_segments (0x13bb4 : word) = Some W_13ab8.
Proof. vm_refl. Qed.
Lemma D_13ab8 : decode_any W_13ab8 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13abc : bv 32 := 0xffffd517.
Lemma F_13abc : fetch_word Ubsan.M.loaded_segments (0x13bb8 : word) = Some W_13abc.
Proof. vm_refl. Qed.
Lemma D_13abc : decode_any W_13abc = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ac0 : bv 32 := 0xfc950513.
Lemma F_13ac0 : fetch_word Ubsan.M.loaded_segments (0x13bbc : word) = Some W_13ac0.
Proof. vm_refl. Qed.
Lemma D_13ac0 : decode_any W_13ac0 = Some (OpImm ALU_ADD 10 10 4041, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ac4 : bv 32 := 0xf49ff0ef.
Lemma F_13ac4 : fetch_word Ubsan.M.loaded_segments (0x13bc0 : word) = Some W_13ac4.
Proof. vm_refl. Qed.
Lemma D_13ac4 : decode_any W_13ac4 = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ac8 : bv 32 := 0x00040513.
Lemma F_13ac8 : fetch_word Ubsan.M.loaded_segments (0x13bc4 : word) = Some W_13ac8.
Proof. vm_refl. Qed.
Lemma D_13ac8 : decode_any W_13ac8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13acc : bv 32 := 0x00813083.
Lemma F_13acc : fetch_word Ubsan.M.loaded_segments (0x13bc8 : word) = Some W_13acc.
Proof. vm_refl. Qed.
Lemma D_13acc : decode_any W_13acc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ad0 : bv 32 := 0x00013403.
Lemma F_13ad0 : fetch_word Ubsan.M.loaded_segments (0x13bcc : word) = Some W_13ad0.
Proof. vm_refl. Qed.
Lemma D_13ad0 : decode_any W_13ad0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ad4 : bv 32 := 0x01010113.
Lemma F_13ad4 : fetch_word Ubsan.M.loaded_segments (0x13bd0 : word) = Some W_13ad4.
Proof. vm_refl. Qed.
Lemma D_13ad4 : decode_any W_13ad4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ad8 : bv 32 := 0x00008067.
Lemma F_13ad8 : fetch_word Ubsan.M.loaded_segments (0x13bd4 : word) = Some W_13ad8.
Proof. vm_refl. Qed.
Lemma D_13ad8 : decode_any W_13ad8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13af4 : bv 32 := 0x00051663.
Lemma F_13af4 : fetch_word Ubsan.M.loaded_segments (0x13bf0 : word) = Some W_13af4.
Proof. vm_refl. Qed.
Lemma D_13af4 : decode_any W_13af4 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b00 : bv 32 := 0x0000d597.
Lemma F_13b00 : fetch_word Ubsan.M.loaded_segments (0x13bfc : word) = Some W_13b00.
Proof. vm_refl. Qed.
Lemma D_13b00 : decode_any W_13b00 = Some (Auipc 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b04 : bv 32 := 0xe4a5b623.
Lemma F_13b04 : fetch_word Ubsan.M.loaded_segments (0x13c00 : word) = Some W_13b04.
Proof. vm_refl. Qed.
Lemma D_13b04 : decode_any W_13b04 = Some (Store SZ8 11 10 3660, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b08 : bv 32 := 0x00008067.
Lemma F_13b08 : fetch_word Ubsan.M.loaded_segments (0x13c04 : word) = Some W_13b08.
Proof. vm_refl. Qed.
Lemma D_13b08 : decode_any W_13b08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b0c : bv 32 := 0xff010113.
Lemma F_13b0c : fetch_word Ubsan.M.loaded_segments (0x13c08 : word) = Some W_13b0c.
Proof. vm_refl. Qed.
Lemma D_13b0c : decode_any W_13b0c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b10 : bv 32 := 0x00113423.
Lemma F_13b10 : fetch_word Ubsan.M.loaded_segments (0x13c0c : word) = Some W_13b10.
Proof. vm_refl. Qed.
Lemma D_13b10 : decode_any W_13b10 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b14 : bv 32 := 0x00813023.
Lemma F_13b14 : fetch_word Ubsan.M.loaded_segments (0x13c10 : word) = Some W_13b14.
Proof. vm_refl. Qed.
Lemma D_13b14 : decode_any W_13b14 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b18 : bv 32 := 0x098000ef.
Lemma F_13b18 : fetch_word Ubsan.M.loaded_segments (0x13c14 : word) = Some W_13b18.
Proof. vm_refl. Qed.
Lemma D_13b18 : decode_any W_13b18 = Some (Jal 1 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b1c : bv 32 := 0x04050263.
Lemma F_13b1c : fetch_word Ubsan.M.loaded_segments (0x13c18 : word) = Some W_13b1c.
Proof. vm_refl. Qed.
Lemma D_13b1c : decode_any W_13b1c = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b20 : bv 32 := 0x00757593.
Lemma F_13b20 : fetch_word Ubsan.M.loaded_segments (0x13c1c : word) = Some W_13b20.
Proof. vm_refl. Qed.
Lemma D_13b20 : decode_any W_13b20 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b24 : bv 32 := 0x08059463.
Lemma F_13b24 : fetch_word Ubsan.M.loaded_segments (0x13c20 : word) = Some W_13b24.
Proof. vm_refl. Qed.
Lemma D_13b24 : decode_any W_13b24 = Some (Branch BC_NE 11 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b28 : bv 32 := 0x01056583.
Lemma F_13b28 : fetch_word Ubsan.M.loaded_segments (0x13c24 : word) = Some W_13b28.
Proof. vm_refl. Qed.
Lemma D_13b28 : decode_any W_13b28 = Some (Load SZ4 false 11 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b2c : bv 32 := 0x00456603.
Lemma F_13b2c : fetch_word Ubsan.M.loaded_segments (0x13c28 : word) = Some W_13b2c.
Proof. vm_refl. Qed.
Lemma D_13b2c : decode_any W_13b2c = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b30 : bv 32 := 0x00259593.
Lemma F_13b30 : fetch_word Ubsan.M.loaded_segments (0x13c2c : word) = Some W_13b30.
Proof. vm_refl. Qed.
Lemma D_13b30 : decode_any W_13b30 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b34 : bv 32 := 0x02c596b3.
Lemma F_13b34 : fetch_word Ubsan.M.loaded_segments (0x13c30 : word) = Some W_13b34.
Proof. vm_refl. Qed.
Lemma D_13b34 : decode_any W_13b34 = Some (Mul M_MULH 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b38 : bv 32 := 0x02c58633.
Lemma F_13b38 : fetch_word Ubsan.M.loaded_segments (0x13c34 : word) = Some W_13b38.
Proof. vm_refl. Qed.
Lemma D_13b38 : decode_any W_13b38 = Some (Mul M_MUL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b3c : bv 32 := 0x43f65593.
Lemma F_13b3c : fetch_word Ubsan.M.loaded_segments (0x13c38 : word) = Some W_13b3c.
Proof. vm_refl. Qed.
Lemma D_13b3c : decode_any W_13b3c = Some (ShiftImm ALU_SRA 11 12 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b40 : bv 32 := 0x06b69663.
Lemma F_13b40 : fetch_word Ubsan.M.loaded_segments (0x13c3c : word) = Some W_13b40.
Proof. vm_refl. Qed.
Lemma D_13b40 : decode_any W_13b40 = Some (Branch BC_NE 13 11 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b44 : bv 32 := 0x03853583.
Lemma F_13b44 : fetch_word Ubsan.M.loaded_segments (0x13c40 : word) = Some W_13b44.
Proof. vm_refl. Qed.
Lemma D_13b44 : decode_any W_13b44 = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b48 : bv 32 := 0x00050413.
Lemma F_13b48 : fetch_word Ubsan.M.loaded_segments (0x13c44 : word) = Some W_13b48.
Proof. vm_refl. Qed.
Lemma D_13b48 : decode_any W_13b48 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b4c : bv 32 := 0x00058513.
Lemma F_13b4c : fetch_word Ubsan.M.loaded_segments (0x13c48 : word) = Some W_13b4c.
Proof. vm_refl. Qed.
Lemma D_13b4c : decode_any W_13b4c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b50 : bv 32 := 0x00000593.
Lemma F_13b50 : fetch_word Ubsan.M.loaded_segments (0x13c4c : word) = Some W_13b50.
Proof. vm_refl. Qed.
Lemma D_13b50 : decode_any W_13b50 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b54 : bv 32 := 0x7680a0ef.
Lemma F_13b54 : fetch_word Ubsan.M.loaded_segments (0x13c50 : word) = Some W_13b54.
Proof. vm_refl. Qed.
Lemma D_13b54 : decode_any W_13b54 = Some (Jal 1 42856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b58 : bv 32 := 0x00040513.
Lemma F_13b58 : fetch_word Ubsan.M.loaded_segments (0x13c54 : word) = Some W_13b58.
Proof. vm_refl. Qed.
Lemma D_13b58 : decode_any W_13b58 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b5c : bv 32 := 0x0400006f.
Lemma F_13b5c : fetch_word Ubsan.M.loaded_segments (0x13c58 : word) = Some W_13b5c.
Proof. vm_refl. Qed.
Lemma D_13b5c : decode_any W_13b5c = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b60 : bv 32 := 0x0000c517.
Lemma F_13b60 : fetch_word Ubsan.M.loaded_segments (0x13c5c : word) = Some W_13b60.
Proof. vm_refl. Qed.
Lemma D_13b60 : decode_any W_13b60 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b64 : bv 32 := 0xd7453503.
Lemma F_13b64 : fetch_word Ubsan.M.loaded_segments (0x13c60 : word) = Some W_13b64.
Proof. vm_refl. Qed.
Lemma D_13b64 : decode_any W_13b64 = Some (Load SZ8 true 10 10 3444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b68 : bv 32 := 0x00052503.
Lemma F_13b68 : fetch_word Ubsan.M.loaded_segments (0x13c64 : word) = Some W_13b68.
Proof. vm_refl. Qed.
Lemma D_13b68 : decode_any W_13b68 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b6c : bv 32 := 0x00500593.
Lemma F_13b6c : fetch_word Ubsan.M.loaded_segments (0x13c68 : word) = Some W_13b6c.
Proof. vm_refl. Qed.
Lemma D_13b6c : decode_any W_13b6c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b70 : bv 32 := 0x02a5c463.
Lemma F_13b70 : fetch_word Ubsan.M.loaded_segments (0x13c6c : word) = Some W_13b70.
Proof. vm_refl. Qed.
Lemma D_13b70 : decode_any W_13b70 = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b74 : bv 32 := 0xffffc517.
Lemma F_13b74 : fetch_word Ubsan.M.loaded_segments (0x13c70 : word) = Some W_13b74.
Proof. vm_refl. Qed.
Lemma D_13b74 : decode_any W_13b74 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b78 : bv 32 := 0xffffd597.
Lemma F_13b78 : fetch_word Ubsan.M.loaded_segments (0x13c74 : word) = Some W_13b78.
Proof. vm_refl. Qed.
Lemma D_13b78 : decode_any W_13b78 = Some (Auipc 11 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b7c : bv 32 := 0x79450513.
Lemma F_13b7c : fetch_word Ubsan.M.loaded_segments (0x13c78 : word) = Some W_13b7c.
Proof. vm_refl. Qed.
Lemma D_13b7c : decode_any W_13b7c = Some (OpImm ALU_ADD 10 10 1940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b80 : bv 32 := 0x92158593.
Lemma F_13b80 : fetch_word Ubsan.M.loaded_segments (0x13c7c : word) = Some W_13b80.
Proof. vm_refl. Qed.
Lemma D_13b80 : decode_any W_13b80 = Some (OpImm ALU_ADD 11 11 2337, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b84 : bv 32 := 0x00000613.
Lemma F_13b84 : fetch_word Ubsan.M.loaded_segments (0x13c80 : word) = Some W_13b84.
Proof. vm_refl. Qed.
Lemma D_13b84 : decode_any W_13b84 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b88 : bv 32 := 0x00813083.
Lemma F_13b88 : fetch_word Ubsan.M.loaded_segments (0x13c84 : word) = Some W_13b88.
Proof. vm_refl. Qed.
Lemma D_13b88 : decode_any W_13b88 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b8c : bv 32 := 0x00013403.
Lemma F_13b8c : fetch_word Ubsan.M.loaded_segments (0x13c88 : word) = Some W_13b8c.
Proof. vm_refl. Qed.
Lemma D_13b8c : decode_any W_13b8c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b90 : bv 32 := 0x01010113.
Lemma F_13b90 : fetch_word Ubsan.M.loaded_segments (0x13c8c : word) = Some W_13b90.
Proof. vm_refl. Qed.
Lemma D_13b90 : decode_any W_13b90 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b94 : bv 32 := 0xf15ff06f.
Lemma F_13b94 : fetch_word Ubsan.M.loaded_segments (0x13c90 : word) = Some W_13b94.
Proof. vm_refl. Qed.
Lemma D_13b94 : decode_any W_13b94 = Some (Jal 0 2096916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b9c : bv 32 := 0x00813083.
Lemma F_13b9c : fetch_word Ubsan.M.loaded_segments (0x13c98 : word) = Some W_13b9c.
Proof. vm_refl. Qed.
Lemma D_13b9c : decode_any W_13b9c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ba0 : bv 32 := 0x00013403.
Lemma F_13ba0 : fetch_word Ubsan.M.loaded_segments (0x13c9c : word) = Some W_13ba0.
Proof. vm_refl. Qed.
Lemma D_13ba0 : decode_any W_13ba0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ba4 : bv 32 := 0x01010113.
Lemma F_13ba4 : fetch_word Ubsan.M.loaded_segments (0x13ca0 : word) = Some W_13ba4.
Proof. vm_refl. Qed.
Lemma D_13ba4 : decode_any W_13ba4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ba8 : bv 32 := 0x00008067.
Lemma F_13ba8 : fetch_word Ubsan.M.loaded_segments (0x13ca4 : word) = Some W_13ba8.
Proof. vm_refl. Qed.
Lemma D_13ba8 : decode_any W_13ba8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bb0 : bv 32 := 0xfe010113.
Lemma F_13bb0 : fetch_word Ubsan.M.loaded_segments (0x13cac : word) = Some W_13bb0.
Proof. vm_refl. Qed.
Lemma D_13bb0 : decode_any W_13bb0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bb4 : bv 32 := 0x00113c23.
Lemma F_13bb4 : fetch_word Ubsan.M.loaded_segments (0x13cb0 : word) = Some W_13bb4.
Proof. vm_refl. Qed.
Lemma D_13bb4 : decode_any W_13bb4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bb8 : bv 32 := 0x00813823.
Lemma F_13bb8 : fetch_word Ubsan.M.loaded_segments (0x13cb4 : word) = Some W_13bb8.
Proof. vm_refl. Qed.
Lemma D_13bb8 : decode_any W_13bb8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bbc : bv 32 := 0x00913423.
Lemma F_13bbc : fetch_word Ubsan.M.loaded_segments (0x13cb8 : word) = Some W_13bbc.
Proof. vm_refl. Qed.
Lemma D_13bbc : decode_any W_13bbc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bc0 : bv 32 := 0x00058493.
Lemma F_13bc0 : fetch_word Ubsan.M.loaded_segments (0x13cbc : word) = Some W_13bc0.
Proof. vm_refl. Qed.
Lemma D_13bc0 : decode_any W_13bc0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bc4 : bv 32 := 0x134000ef.
Lemma F_13bc4 : fetch_word Ubsan.M.loaded_segments (0x13cc0 : word) = Some W_13bc4.
Proof. vm_refl. Qed.
Lemma D_13bc4 : decode_any W_13bc4 = Some (Jal 1 308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bc8 : bv 32 := 0x04050863.
Lemma F_13bc8 : fetch_word Ubsan.M.loaded_segments (0x13cc4 : word) = Some W_13bc8.
Proof. vm_refl. Qed.
Lemma D_13bc8 : decode_any W_13bc8 = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bcc : bv 32 := 0x00050413.
Lemma F_13bcc : fetch_word Ubsan.M.loaded_segments (0x13cc8 : word) = Some W_13bcc.
Proof. vm_refl. Qed.
Lemma D_13bcc : decode_any W_13bcc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bd0 : bv 32 := 0x00757513.
Lemma F_13bd0 : fetch_word Ubsan.M.loaded_segments (0x13ccc : word) = Some W_13bd0.
Proof. vm_refl. Qed.
Lemma D_13bd0 : decode_any W_13bd0 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bd4 : bv 32 := 0x12051063.
Lemma F_13bd4 : fetch_word Ubsan.M.loaded_segments (0x13cd0 : word) = Some W_13bd4.
Proof. vm_refl. Qed.
Lemma D_13bd4 : decode_any W_13bd4 = Some (Branch BC_NE 10 0 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bd8 : bv 32 := 0x01042503.
Lemma F_13bd8 : fetch_word Ubsan.M.loaded_segments (0x13cd4 : word) = Some W_13bd8.
Proof. vm_refl. Qed.
Lemma D_13bd8 : decode_any W_13bd8 = Some (Load SZ4 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bdc : bv 32 := 0x00251513.
Lemma F_13bdc : fetch_word Ubsan.M.loaded_segments (0x13cd8 : word) = Some W_13bdc.
Proof. vm_refl. Qed.
Lemma D_13bdc : decode_any W_13bdc = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13be0 : bv 32 := 0x029515b3.
Lemma F_13be0 : fetch_word Ubsan.M.loaded_segments (0x13cdc : word) = Some W_13be0.
Proof. vm_refl. Qed.
Lemma D_13be0 : decode_any W_13be0 = Some (Mul M_MULH 11 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13be4 : bv 32 := 0x02950533.
Lemma F_13be4 : fetch_word Ubsan.M.loaded_segments (0x13ce0 : word) = Some W_13be4.
Proof. vm_refl. Qed.
Lemma D_13be4 : decode_any W_13be4 = Some (Mul M_MUL 10 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13be8 : bv 32 := 0x43f55613.
Lemma F_13be8 : fetch_word Ubsan.M.loaded_segments (0x13ce4 : word) = Some W_13be8.
Proof. vm_refl. Qed.
Lemma D_13be8 : decode_any W_13be8 = Some (ShiftImm ALU_SRA 12 10 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bec : bv 32 := 0x10c59463.
Lemma F_13bec : fetch_word Ubsan.M.loaded_segments (0x13ce8 : word) = Some W_13bec.
Proof. vm_refl. Qed.
Lemma D_13bec : decode_any W_13bec = Some (Branch BC_NE 11 12 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bf0 : bv 32 := 0x0000d597.
Lemma F_13bf0 : fetch_word Ubsan.M.loaded_segments (0x13cec : word) = Some W_13bf0.
Proof. vm_refl. Qed.
Lemma D_13bf0 : decode_any W_13bf0 = Some (Auipc 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bf4 : bv 32 := 0xd6458493.
Lemma F_13bf4 : fetch_word Ubsan.M.loaded_segments (0x13cf0 : word) = Some W_13bf4.
Proof. vm_refl. Qed.
Lemma D_13bf4 : decode_any W_13bf4 = Some (OpImm ALU_ADD 9 11 3428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bf8 : bv 32 := 0x0004b583.
Lemma F_13bf8 : fetch_word Ubsan.M.loaded_segments (0x13cf4 : word) = Some W_13bf8.
Proof. vm_refl. Qed.
Lemma D_13bf8 : decode_any W_13bf8 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bfc : bv 32 := 0x000580e7.
Lemma F_13bfc : fetch_word Ubsan.M.loaded_segments (0x13cf8 : word) = Some W_13bfc.
Proof. vm_refl. Qed.
Lemma D_13bfc : decode_any W_13bfc = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c00 : bv 32 := 0x04050a63.
Lemma F_13c00 : fetch_word Ubsan.M.loaded_segments (0x13cfc : word) = Some W_13c00.
Proof. vm_refl. Qed.
Lemma D_13c00 : decode_any W_13c00 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c04 : bv 32 := 0x02a43c23.
Lemma F_13c04 : fetch_word Ubsan.M.loaded_segments (0x13d00 : word) = Some W_13c04.
Proof. vm_refl. Qed.
Lemma D_13c04 : decode_any W_13c04 = Some (Store SZ8 8 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c08 : bv 32 := 0x00040513.
Lemma F_13c08 : fetch_word Ubsan.M.loaded_segments (0x13d04 : word) = Some W_13c08.
Proof. vm_refl. Qed.
Lemma D_13c08 : decode_any W_13c08 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c0c : bv 32 := 0x00000593.
Lemma F_13c0c : fetch_word Ubsan.M.loaded_segments (0x13d08 : word) = Some W_13c0c.
Proof. vm_refl. Qed.
Lemma D_13c0c : decode_any W_13c0c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c10 : bv 32 := 0x4ad000ef.
Lemma F_13c10 : fetch_word Ubsan.M.loaded_segments (0x13d0c : word) = Some W_13c10.
Proof. vm_refl. Qed.
Lemma D_13c10 : decode_any W_13c10 = Some (Jal 1 3244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c14 : bv 32 := 0x0c80006f.
Lemma F_13c14 : fetch_word Ubsan.M.loaded_segments (0x13d10 : word) = Some W_13c14.
Proof. vm_refl. Qed.
Lemma D_13c14 : decode_any W_13c14 = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c18 : bv 32 := 0x0000c517.
Lemma F_13c18 : fetch_word Ubsan.M.loaded_segments (0x13d14 : word) = Some W_13c18.
Proof. vm_refl. Qed.
Lemma D_13c18 : decode_any W_13c18 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c1c : bv 32 := 0xcbc53503.
Lemma F_13c1c : fetch_word Ubsan.M.loaded_segments (0x13d18 : word) = Some W_13c1c.
Proof. vm_refl. Qed.
Lemma D_13c1c : decode_any W_13c1c = Some (Load SZ8 true 10 10 3260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c20 : bv 32 := 0x00052503.
Lemma F_13c20 : fetch_word Ubsan.M.loaded_segments (0x13d1c : word) = Some W_13c20.
Proof. vm_refl. Qed.
Lemma D_13c20 : decode_any W_13c20 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c24 : bv 32 := 0x00500593.
Lemma F_13c24 : fetch_word Ubsan.M.loaded_segments (0x13d20 : word) = Some W_13c24.
Proof. vm_refl. Qed.
Lemma D_13c24 : decode_any W_13c24 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c28 : bv 32 := 0x0aa5c863.
Lemma F_13c28 : fetch_word Ubsan.M.loaded_segments (0x13d24 : word) = Some W_13c28.
Proof. vm_refl. Qed.
Lemma D_13c28 : decode_any W_13c28 = Some (Branch BC_LT 11 10 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c2c : bv 32 := 0xffffc517.
Lemma F_13c2c : fetch_word Ubsan.M.loaded_segments (0x13d28 : word) = Some W_13c2c.
Proof. vm_refl. Qed.
Lemma D_13c2c : decode_any W_13c2c = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c30 : bv 32 := 0xffffc597.
Lemma F_13c30 : fetch_word Ubsan.M.loaded_segments (0x13d2c : word) = Some W_13c30.
Proof. vm_refl. Qed.
Lemma D_13c30 : decode_any W_13c30 = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c34 : bv 32 := 0x6dc50513.
Lemma F_13c34 : fetch_word Ubsan.M.loaded_segments (0x13d30 : word) = Some W_13c34.
Proof. vm_refl. Qed.
Lemma D_13c34 : decode_any W_13c34 = Some (OpImm ALU_ADD 10 10 1756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c38 : bv 32 := 0x7c958593.
Lemma F_13c38 : fetch_word Ubsan.M.loaded_segments (0x13d34 : word) = Some W_13c38.
Proof. vm_refl. Qed.
Lemma D_13c38 : decode_any W_13c38 = Some (OpImm ALU_ADD 11 11 1993, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c3c : bv 32 := 0x00000613.
Lemma F_13c3c : fetch_word Ubsan.M.loaded_segments (0x13d38 : word) = Some W_13c3c.
Proof. vm_refl. Qed.
Lemma D_13c3c : decode_any W_13c3c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c40 : bv 32 := 0x01813083.
Lemma F_13c40 : fetch_word Ubsan.M.loaded_segments (0x13d3c : word) = Some W_13c40.
Proof. vm_refl. Qed.
Lemma D_13c40 : decode_any W_13c40 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c44 : bv 32 := 0x01013403.
Lemma F_13c44 : fetch_word Ubsan.M.loaded_segments (0x13d40 : word) = Some W_13c44.
Proof. vm_refl. Qed.
Lemma D_13c44 : decode_any W_13c44 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c48 : bv 32 := 0x00813483.
Lemma F_13c48 : fetch_word Ubsan.M.loaded_segments (0x13d44 : word) = Some W_13c48.
Proof. vm_refl. Qed.
Lemma D_13c48 : decode_any W_13c48 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c4c : bv 32 := 0x02010113.
Lemma F_13c4c : fetch_word Ubsan.M.loaded_segments (0x13d48 : word) = Some W_13c4c.
Proof. vm_refl. Qed.
Lemma D_13c4c : decode_any W_13c4c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c50 : bv 32 := 0xe59ff06f.
Lemma F_13c50 : fetch_word Ubsan.M.loaded_segments (0x13d4c : word) = Some W_13c50.
Proof. vm_refl. Qed.
Lemma D_13c50 : decode_any W_13c50 = Some (Jal 0 2096728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c54 : bv 32 := 0x01440513.
Lemma F_13c54 : fetch_word Ubsan.M.loaded_segments (0x13d50 : word) = Some W_13c54.
Proof. vm_refl. Qed.
Lemma D_13c54 : decode_any W_13c54 = Some (OpImm ALU_ADD 10 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c58 : bv 32 := 0xfff00593.
Lemma F_13c58 : fetch_word Ubsan.M.loaded_segments (0x13d54 : word) = Some W_13c58.
Proof. vm_refl. Qed.
Lemma D_13c58 : decode_any W_13c58 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c5c : bv 32 := 0x06b5252f.
Lemma F_13c5c : fetch_word Ubsan.M.loaded_segments (0x13d58 : word) = Some W_13c5c.
Proof. vm_refl. Qed.
Lemma D_13c5c : decode_any W_13c5c = Some (Amo AMO_ADD AW true true 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c60 : bv 32 := 0x00100593.
Lemma F_13c60 : fetch_word Ubsan.M.loaded_segments (0x13d5c : word) = Some W_13c60.
Proof. vm_refl. Qed.
Lemma D_13c60 : decode_any W_13c60 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c64 : bv 32 := 0x04b51063.
Lemma F_13c64 : fetch_word Ubsan.M.loaded_segments (0x13d60 : word) = Some W_13c64.
Proof. vm_refl. Qed.
Lemma D_13c64 : decode_any W_13c64 = Some (Branch BC_NE 10 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c68 : bv 32 := 0x03843503.
Lemma F_13c68 : fetch_word Ubsan.M.loaded_segments (0x13d64 : word) = Some W_13c68.
Proof. vm_refl. Qed.
Lemma D_13c68 : decode_any W_13c68 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c6c : bv 32 := 0x00050663.
Lemma F_13c6c : fetch_word Ubsan.M.loaded_segments (0x13d68 : word) = Some W_13c6c.
Proof. vm_refl. Qed.
Lemma D_13c6c : decode_any W_13c6c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c78 : bv 32 := 0x02843503.
Lemma F_13c78 : fetch_word Ubsan.M.loaded_segments (0x13d74 : word) = Some W_13c78.
Proof. vm_refl. Qed.
Lemma D_13c78 : decode_any W_13c78 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c7c : bv 32 := 0x00050463.
Lemma F_13c7c : fetch_word Ubsan.M.loaded_segments (0x13d78 : word) = Some W_13c7c.
Proof. vm_refl. Qed.
Lemma D_13c7c : decode_any W_13c7c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c84 : bv 32 := 0x03043503.
Lemma F_13c84 : fetch_word Ubsan.M.loaded_segments (0x13d80 : word) = Some W_13c84.
Proof. vm_refl. Qed.
Lemma D_13c84 : decode_any W_13c84 = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c88 : bv 32 := 0x00a13023.
Lemma F_13c88 : fetch_word Ubsan.M.loaded_segments (0x13d84 : word) = Some W_13c88.
Proof. vm_refl. Qed.
Lemma D_13c88 : decode_any W_13c88 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c8c : bv 32 := 0x00050863.
Lemma F_13c8c : fetch_word Ubsan.M.loaded_segments (0x13d88 : word) = Some W_13c8c.
Proof. vm_refl. Qed.
Lemma D_13c8c : decode_any W_13c8c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c9c : bv 32 := 0x00040513.
Lemma F_13c9c : fetch_word Ubsan.M.loaded_segments (0x13d98 : word) = Some W_13c9c.
Proof. vm_refl. Qed.
Lemma D_13c9c : decode_any W_13c9c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ca0 : bv 32 := 0x0e4030ef.
Lemma F_13ca0 : fetch_word Ubsan.M.loaded_segments (0x13d9c : word) = Some W_13ca0.
Proof. vm_refl. Qed.
Lemma D_13ca0 : decode_any W_13ca0 = Some (Jal 1 12516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ca4 : bv 32 := 0x0000c517.
Lemma F_13ca4 : fetch_word Ubsan.M.loaded_segments (0x13da0 : word) = Some W_13ca4.
Proof. vm_refl. Qed.
Lemma D_13ca4 : decode_any W_13ca4 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ca8 : bv 32 := 0xc3053503.
Lemma F_13ca8 : fetch_word Ubsan.M.loaded_segments (0x13da4 : word) = Some W_13ca8.
Proof. vm_refl. Qed.
Lemma D_13ca8 : decode_any W_13ca8 = Some (Load SZ8 true 10 10 3120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cac : bv 32 := 0x00052503.
Lemma F_13cac : fetch_word Ubsan.M.loaded_segments (0x13da8 : word) = Some W_13cac.
Proof. vm_refl. Qed.
Lemma D_13cac : decode_any W_13cac = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cb0 : bv 32 := 0x00500593.
Lemma F_13cb0 : fetch_word Ubsan.M.loaded_segments (0x13dac : word) = Some W_13cb0.
Proof. vm_refl. Qed.
Lemma D_13cb0 : decode_any W_13cb0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cb4 : bv 32 := 0x02a5c263.
Lemma F_13cb4 : fetch_word Ubsan.M.loaded_segments (0x13db0 : word) = Some W_13cb4.
Proof. vm_refl. Qed.
Lemma D_13cb4 : decode_any W_13cb4 = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cb8 : bv 32 := 0xffffd517.
Lemma F_13cb8 : fetch_word Ubsan.M.loaded_segments (0x13db4 : word) = Some W_13cb8.
Proof. vm_refl. Qed.
Lemma D_13cb8 : decode_any W_13cb8 = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cbc : bv 32 := 0xffffc597.
Lemma F_13cbc : fetch_word Ubsan.M.loaded_segments (0x13db8 : word) = Some W_13cbc.
Proof. vm_refl. Qed.
Lemma D_13cbc : decode_any W_13cbc = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cc0 : bv 32 := 0xc3950513.
Lemma F_13cc0 : fetch_word Ubsan.M.loaded_segments (0x13dbc : word) = Some W_13cc0.
Proof. vm_refl. Qed.
Lemma D_13cc0 : decode_any W_13cc0 = Some (OpImm ALU_ADD 10 10 3129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cc4 : bv 32 := 0x73d58593.
Lemma F_13cc4 : fetch_word Ubsan.M.loaded_segments (0x13dc0 : word) = Some W_13cc4.
Proof. vm_refl. Qed.
Lemma D_13cc4 : decode_any W_13cc4 = Some (OpImm ALU_ADD 11 11 1853, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cc8 : bv 32 := 0x00000613.
Lemma F_13cc8 : fetch_word Ubsan.M.loaded_segments (0x13dc4 : word) = Some W_13cc8.
Proof. vm_refl. Qed.
Lemma D_13cc8 : decode_any W_13cc8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ccc : bv 32 := 0xdddff0ef.
Lemma F_13ccc : fetch_word Ubsan.M.loaded_segments (0x13dc8 : word) = Some W_13ccc.
Proof. vm_refl. Qed.
Lemma D_13ccc : decode_any W_13ccc = Some (Jal 1 2096604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cd0 : bv 32 := 0x00050413.
Lemma F_13cd0 : fetch_word Ubsan.M.loaded_segments (0x13dcc : word) = Some W_13cd0.
Proof. vm_refl. Qed.
Lemma D_13cd0 : decode_any W_13cd0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cd4 : bv 32 := 0x0080006f.
Lemma F_13cd4 : fetch_word Ubsan.M.loaded_segments (0x13dd0 : word) = Some W_13cd4.
Proof. vm_refl. Qed.
Lemma D_13cd4 : decode_any W_13cd4 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cdc : bv 32 := 0x00040513.
Lemma F_13cdc : fetch_word Ubsan.M.loaded_segments (0x13dd8 : word) = Some W_13cdc.
Proof. vm_refl. Qed.
Lemma D_13cdc : decode_any W_13cdc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ce0 : bv 32 := 0x01813083.
Lemma F_13ce0 : fetch_word Ubsan.M.loaded_segments (0x13ddc : word) = Some W_13ce0.
Proof. vm_refl. Qed.
Lemma D_13ce0 : decode_any W_13ce0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ce4 : bv 32 := 0x01013403.
Lemma F_13ce4 : fetch_word Ubsan.M.loaded_segments (0x13de0 : word) = Some W_13ce4.
Proof. vm_refl. Qed.
Lemma D_13ce4 : decode_any W_13ce4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ce8 : bv 32 := 0x00813483.
Lemma F_13ce8 : fetch_word Ubsan.M.loaded_segments (0x13de4 : word) = Some W_13ce8.
Proof. vm_refl. Qed.
Lemma D_13ce8 : decode_any W_13ce8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cec : bv 32 := 0x02010113.
Lemma F_13cec : fetch_word Ubsan.M.loaded_segments (0x13de8 : word) = Some W_13cec.
Proof. vm_refl. Qed.
Lemma D_13cec : decode_any W_13cec = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cf0 : bv 32 := 0x00008067.
Lemma F_13cf0 : fetch_word Ubsan.M.loaded_segments (0x13dec : word) = Some W_13cf0.
Proof. vm_refl. Qed.
Lemma D_13cf0 : decode_any W_13cf0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cf8 : bv 32 := 0xfd010113.
Lemma F_13cf8 : fetch_word Ubsan.M.loaded_segments (0x13df4 : word) = Some W_13cf8.
Proof. vm_refl. Qed.
Lemma D_13cf8 : decode_any W_13cf8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cfc : bv 32 := 0x02113423.
Lemma F_13cfc : fetch_word Ubsan.M.loaded_segments (0x13df8 : word) = Some W_13cfc.
Proof. vm_refl. Qed.
Lemma D_13cfc : decode_any W_13cfc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d00 : bv 32 := 0x02813023.
Lemma F_13d00 : fetch_word Ubsan.M.loaded_segments (0x13dfc : word) = Some W_13d00.
Proof. vm_refl. Qed.
Lemma D_13d00 : decode_any W_13d00 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d04 : bv 32 := 0x00913c23.
Lemma F_13d04 : fetch_word Ubsan.M.loaded_segments (0x13e00 : word) = Some W_13d04.
Proof. vm_refl. Qed.
Lemma D_13d04 : decode_any W_13d04 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d08 : bv 32 := 0x01213823.
Lemma F_13d08 : fetch_word Ubsan.M.loaded_segments (0x13e04 : word) = Some W_13d08.
Proof. vm_refl. Qed.
Lemma D_13d08 : decode_any W_13d08 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d0c : bv 32 := 0x01313423.
Lemma F_13d0c : fetch_word Ubsan.M.loaded_segments (0x13e08 : word) = Some W_13d0c.
Proof. vm_refl. Qed.
Lemma D_13d0c : decode_any W_13d0c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d10 : bv 32 := 0x01413023.
Lemma F_13d10 : fetch_word Ubsan.M.loaded_segments (0x13e0c : word) = Some W_13d10.
Proof. vm_refl. Qed.
Lemma D_13d10 : decode_any W_13d10 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d14 : bv 32 := 0x02000693.
Lemma F_13d14 : fetch_word Ubsan.M.loaded_segments (0x13e10 : word) = Some W_13d14.
Proof. vm_refl. Qed.
Lemma D_13d14 : decode_any W_13d14 = Some (OpImm ALU_ADD 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d18 : bv 32 := 0x14c6ea63.
Lemma F_13d18 : fetch_word Ubsan.M.loaded_segments (0x13e14 : word) = Some W_13d18.
Proof. vm_refl. Qed.
Lemma D_13d18 : decode_any W_13d18 = Some (Branch BC_LTU 13 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d1c : bv 32 := 0x101016b7.
Lemma F_13d1c : fetch_word Ubsan.M.loaded_segments (0x13e18 : word) = Some W_13d1c.
Proof. vm_refl. Qed.
Lemma D_13d1c : decode_any W_13d1c = Some (Lui 13 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d20 : bv 32 := 0x00469693.
Lemma F_13d20 : fetch_word Ubsan.M.loaded_segments (0x13e1c : word) = Some W_13d20.
Proof. vm_refl. Qed.
Lemma D_13d20 : decode_any W_13d20 = Some (ShiftImm ALU_SLL 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d24 : bv 32 := 0x11668693.
Lemma F_13d24 : fetch_word Ubsan.M.loaded_segments (0x13e20 : word) = Some W_13d24.
Proof. vm_refl. Qed.
Lemma D_13d24 : decode_any W_13d24 = Some (OpImm ALU_ADD 13 13 278, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d28 : bv 32 := 0x00c6d6b3.
Lemma F_13d28 : fetch_word Ubsan.M.loaded_segments (0x13e24 : word) = Some W_13d28.
Proof. vm_refl. Qed.
Lemma D_13d28 : decode_any W_13d28 = Some (Op ALU_SRL 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d2c : bv 32 := 0x0016f693.
Lemma F_13d2c : fetch_word Ubsan.M.loaded_segments (0x13e28 : word) = Some W_13d2c.
Proof. vm_refl. Qed.
Lemma D_13d2c : decode_any W_13d2c = Some (OpImm ALU_AND 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d30 : bv 32 := 0x12068e63.
Lemma F_13d30 : fetch_word Ubsan.M.loaded_segments (0x13e2c : word) = Some W_13d30.
Proof. vm_refl. Qed.
Lemma D_13d30 : decode_any W_13d30 = Some (Branch BC_EQ 13 0 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d34 : bv 32 := 0x06a05a63.
Lemma F_13d34 : fetch_word Ubsan.M.loaded_segments (0x13e30 : word) = Some W_13d34.
Proof. vm_refl. Qed.
Lemma D_13d34 : decode_any W_13d34 = Some (Branch BC_GE 0 10 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d38 : bv 32 := 0x08b05c63.
Lemma F_13d38 : fetch_word Ubsan.M.loaded_segments (0x13e34 : word) = Some W_13d38.
Proof. vm_refl. Qed.
Lemma D_13d38 : decode_any W_13d38 = Some (Branch BC_GE 0 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d3c : bv 32 := 0x02a606b3.
Lemma F_13d3c : fetch_word Ubsan.M.loaded_segments (0x13e38 : word) = Some W_13d3c.
Proof. vm_refl. Qed.
Lemma D_13d3c : decode_any W_13d3c = Some (Mul M_MUL 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d40 : bv 32 := 0x20000737.
Lemma F_13d40 : fetch_word Ubsan.M.loaded_segments (0x13e3c : word) = Some W_13d40.
Proof. vm_refl. Qed.
Lemma D_13d40 : decode_any W_13d40 = Some (Lui 14 131072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d44 : bv 32 := 0xfe17071b.
Lemma F_13d44 : fetch_word Ubsan.M.loaded_segments (0x13e40 : word) = Some W_13d44.
Proof. vm_refl. Qed.
Lemma D_13d44 : decode_any W_13d44 = Some (OpImm32 14 14 4065, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d48 : bv 32 := 0x0ae6e863.
Lemma F_13d48 : fetch_word Ubsan.M.loaded_segments (0x13e44 : word) = Some W_13d48.
Proof. vm_refl. Qed.
Lemma D_13d48 : decode_any W_13d48 = Some (Branch BC_LTU 13 14 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13df8 : bv 32 := 0x01f68693.
Lemma F_13df8 : fetch_word Ubsan.M.loaded_segments (0x13ef4 : word) = Some W_13df8.
Proof. vm_refl. Qed.
Lemma D_13df8 : decode_any W_13df8 = Some (OpImm ALU_ADD 13 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13dfc : bv 32 := 0x0056da13.
Lemma F_13dfc : fetch_word Ubsan.M.loaded_segments (0x13ef8 : word) = Some W_13dfc.
Proof. vm_refl. Qed.
Lemma D_13dfc : decode_any W_13dfc = Some (ShiftImm ALU_SRL 20 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e00 : bv 32 := 0x02ba06b3.
Lemma F_13e00 : fetch_word Ubsan.M.loaded_segments (0x13efc : word) = Some W_13e00.
Proof. vm_refl. Qed.
Lemma D_13e00 : decode_any W_13e00 = Some (Mul M_MUL 13 20 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e04 : bv 32 := 0x00269693.
Lemma F_13e04 : fetch_word Ubsan.M.loaded_segments (0x13f00 : word) = Some W_13e04.
Proof. vm_refl. Qed.
Lemma D_13e04 : decode_any W_13e04 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e08 : bv 32 := 0x01f6d713.
Lemma F_13e08 : fetch_word Ubsan.M.loaded_segments (0x13f04 : word) = Some W_13e08.
Proof. vm_refl. Qed.
Lemma D_13e08 : decode_any W_13e08 = Some (ShiftImm ALU_SRL 14 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e0c : bv 32 := 0x0a070463.
Lemma F_13e0c : fetch_word Ubsan.M.loaded_segments (0x13f08 : word) = Some W_13e0c.
Proof. vm_refl. Qed.
Lemma D_13e0c : decode_any W_13e0c = Some (Branch BC_EQ 14 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e6c : bv 32 := 0x0000c517.
Lemma F_13e6c : fetch_word Ubsan.M.loaded_segments (0x13f68 : word) = Some W_13e6c.
Proof. vm_refl. Qed.
Lemma D_13e6c : decode_any W_13e6c = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e70 : bv 32 := 0xa6853503.
Lemma F_13e70 : fetch_word Ubsan.M.loaded_segments (0x13f6c : word) = Some W_13e70.
Proof. vm_refl. Qed.
Lemma D_13e70 : decode_any W_13e70 = Some (Load SZ8 true 10 10 2664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e74 : bv 32 := 0x00052503.
Lemma F_13e74 : fetch_word Ubsan.M.loaded_segments (0x13f70 : word) = Some W_13e74.
Proof. vm_refl. Qed.
Lemma D_13e74 : decode_any W_13e74 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e78 : bv 32 := 0x00500593.
Lemma F_13e78 : fetch_word Ubsan.M.loaded_segments (0x13f74 : word) = Some W_13e78.
Proof. vm_refl. Qed.
Lemma D_13e78 : decode_any W_13e78 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e7c : bv 32 := 0x0ca5c663.
Lemma F_13e7c : fetch_word Ubsan.M.loaded_segments (0x13f78 : word) = Some W_13e7c.
Proof. vm_refl. Qed.
Lemma D_13e7c : decode_any W_13e7c = Some (Branch BC_LT 11 10 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e80 : bv 32 := 0xffffc517.
Lemma F_13e80 : fetch_word Ubsan.M.loaded_segments (0x13f7c : word) = Some W_13e80.
Proof. vm_refl. Qed.
Lemma D_13e80 : decode_any W_13e80 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e84 : bv 32 := 0xffffc597.
Lemma F_13e84 : fetch_word Ubsan.M.loaded_segments (0x13f80 : word) = Some W_13e84.
Proof. vm_refl. Qed.
Lemma D_13e84 : decode_any W_13e84 = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e88 : bv 32 := 0x4e050513.
Lemma F_13e88 : fetch_word Ubsan.M.loaded_segments (0x13f84 : word) = Some W_13e88.
Proof. vm_refl. Qed.
Lemma D_13e88 : decode_any W_13e88 = Some (OpImm ALU_ADD 10 10 1248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e8c : bv 32 := 0x68658593.
Lemma F_13e8c : fetch_word Ubsan.M.loaded_segments (0x13f88 : word) = Some W_13e8c.
Proof. vm_refl. Qed.
Lemma D_13e8c : decode_any W_13e8c = Some (OpImm ALU_ADD 11 11 1670, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e90 : bv 32 := 0x00000613.
Lemma F_13e90 : fetch_word Ubsan.M.loaded_segments (0x13f8c : word) = Some W_13e90.
Proof. vm_refl. Qed.
Lemma D_13e90 : decode_any W_13e90 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e94 : bv 32 := 0x02813083.
Lemma F_13e94 : fetch_word Ubsan.M.loaded_segments (0x13f90 : word) = Some W_13e94.
Proof. vm_refl. Qed.
Lemma D_13e94 : decode_any W_13e94 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e98 : bv 32 := 0x02013403.
Lemma F_13e98 : fetch_word Ubsan.M.loaded_segments (0x13f94 : word) = Some W_13e98.
Proof. vm_refl. Qed.
Lemma D_13e98 : decode_any W_13e98 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e9c : bv 32 := 0x01813483.
Lemma F_13e9c : fetch_word Ubsan.M.loaded_segments (0x13f98 : word) = Some W_13e9c.
Proof. vm_refl. Qed.
Lemma D_13e9c : decode_any W_13e9c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ea0 : bv 32 := 0x01013903.
Lemma F_13ea0 : fetch_word Ubsan.M.loaded_segments (0x13f9c : word) = Some W_13ea0.
Proof. vm_refl. Qed.
Lemma D_13ea0 : decode_any W_13ea0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ea4 : bv 32 := 0x00813983.
Lemma F_13ea4 : fetch_word Ubsan.M.loaded_segments (0x13fa0 : word) = Some W_13ea4.
Proof. vm_refl. Qed.
Lemma D_13ea4 : decode_any W_13ea4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ea8 : bv 32 := 0x00013a03.
Lemma F_13ea8 : fetch_word Ubsan.M.loaded_segments (0x13fa4 : word) = Some W_13ea8.
Proof. vm_refl. Qed.
Lemma D_13ea8 : decode_any W_13ea8 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13eac : bv 32 := 0x03010113.
Lemma F_13eac : fetch_word Ubsan.M.loaded_segments (0x13fa8 : word) = Some W_13eac.
Proof. vm_refl. Qed.
Lemma D_13eac : decode_any W_13eac = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13eb0 : bv 32 := 0xbf9ff06f.
Lemma F_13eb0 : fetch_word Ubsan.M.loaded_segments (0x13fac : word) = Some W_13eb0.
Proof. vm_refl. Qed.
Lemma D_13eb0 : decode_any W_13eb0 = Some (Jal 0 2096120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13eb4 : bv 32 := 0x04000737.
Lemma F_13eb4 : fetch_word Ubsan.M.loaded_segments (0x13fb0 : word) = Some W_13eb4.
Proof. vm_refl. Qed.
Lemma D_13eb4 : decode_any W_13eb4 = Some (Lui 14 16384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13eb8 : bv 32 := 0x0017071b.
Lemma F_13eb8 : fetch_word Ubsan.M.loaded_segments (0x13fb4 : word) = Some W_13eb8.
Proof. vm_refl. Qed.
Lemma D_13eb8 : decode_any W_13eb8 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ebc : bv 32 := 0x02e6e663.
Lemma F_13ebc : fetch_word Ubsan.M.loaded_segments (0x13fb8 : word) = Some W_13ebc.
Proof. vm_refl. Qed.
Lemma D_13ebc : decode_any W_13ebc = Some (Branch BC_LTU 13 14 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ec0 : bv 32 := 0x0000c517.
Lemma F_13ec0 : fetch_word Ubsan.M.loaded_segments (0x13fbc : word) = Some W_13ec0.
Proof. vm_refl. Qed.
Lemma D_13ec0 : decode_any W_13ec0 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ec4 : bv 32 := 0xa1453503.
Lemma F_13ec4 : fetch_word Ubsan.M.loaded_segments (0x13fc0 : word) = Some W_13ec4.
Proof. vm_refl. Qed.
Lemma D_13ec4 : decode_any W_13ec4 = Some (Load SZ8 true 10 10 2580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ec8 : bv 32 := 0x00052503.
Lemma F_13ec8 : fetch_word Ubsan.M.loaded_segments (0x13fc4 : word) = Some W_13ec8.
Proof. vm_refl. Qed.
Lemma D_13ec8 : decode_any W_13ec8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ecc : bv 32 := 0x00500593.
Lemma F_13ecc : fetch_word Ubsan.M.loaded_segments (0x13fc8 : word) = Some W_13ecc.
Proof. vm_refl. Qed.
Lemma D_13ecc : decode_any W_13ecc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ed0 : bv 32 := 0x06a5cc63.
Lemma F_13ed0 : fetch_word Ubsan.M.loaded_segments (0x13fcc : word) = Some W_13ed0.
Proof. vm_refl. Qed.
Lemma D_13ed0 : decode_any W_13ed0 = Some (Branch BC_LT 11 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ed4 : bv 32 := 0xffffc517.
Lemma F_13ed4 : fetch_word Ubsan.M.loaded_segments (0x13fd0 : word) = Some W_13ed4.
Proof. vm_refl. Qed.
Lemma D_13ed4 : decode_any W_13ed4 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ed8 : bv 32 := 0xffffc597.
Lemma F_13ed8 : fetch_word Ubsan.M.loaded_segments (0x13fd4 : word) = Some W_13ed8.
Proof. vm_refl. Qed.
Lemma D_13ed8 : decode_any W_13ed8 = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13edc : bv 32 := 0x3bc50513.
Lemma F_13edc : fetch_word Ubsan.M.loaded_segments (0x13fd8 : word) = Some W_13edc.
Proof. vm_refl. Qed.
Lemma D_13edc : decode_any W_13edc = Some (OpImm ALU_ADD 10 10 956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ee0 : bv 32 := 0x63258593.
Lemma F_13ee0 : fetch_word Ubsan.M.loaded_segments (0x13fdc : word) = Some W_13ee0.
Proof. vm_refl. Qed.
Lemma D_13ee0 : decode_any W_13ee0 = Some (OpImm ALU_ADD 11 11 1586, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ee4 : bv 32 := 0x0600006f.
Lemma F_13ee4 : fetch_word Ubsan.M.loaded_segments (0x13fe0 : word) = Some W_13ee4.
Proof. vm_refl. Qed.
Lemma D_13ee4 : decode_any W_13ee4 = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ee8 : bv 32 := 0x000056b7.
Lemma F_13ee8 : fetch_word Ubsan.M.loaded_segments (0x13fe4 : word) = Some W_13ee8.
Proof. vm_refl. Qed.
Lemma D_13ee8 : decode_any W_13ee8 = Some (Lui 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13eec : bv 32 := 0xe216869b.
Lemma F_13eec : fetch_word Ubsan.M.loaded_segments (0x13fe8 : word) = Some W_13eec.
Proof. vm_refl. Qed.
Lemma D_13eec : decode_any W_13eec = Some (OpImm32 13 13 3617, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ef0 : bv 32 := 0x02d56663.
Lemma F_13ef0 : fetch_word Ubsan.M.loaded_segments (0x13fec : word) = Some W_13ef0.
Proof. vm_refl. Qed.
Lemma D_13ef0 : decode_any W_13ef0 = Some (Branch BC_LTU 10 13 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ef4 : bv 32 := 0x0000c517.
Lemma F_13ef4 : fetch_word Ubsan.M.loaded_segments (0x13ff0 : word) = Some W_13ef4.
Proof. vm_refl. Qed.
Lemma D_13ef4 : decode_any W_13ef4 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ef8 : bv 32 := 0x9e053503.
Lemma F_13ef8 : fetch_word Ubsan.M.loaded_segments (0x13ff4 : word) = Some W_13ef8.
Proof. vm_refl. Qed.
Lemma D_13ef8 : decode_any W_13ef8 = Some (Load SZ8 true 10 10 2528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13efc : bv 32 := 0x00052503.
Lemma F_13efc : fetch_word Ubsan.M.loaded_segments (0x13ff8 : word) = Some W_13efc.
Proof. vm_refl. Qed.
Lemma D_13efc : decode_any W_13efc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f00 : bv 32 := 0x00500593.
Lemma F_13f00 : fetch_word Ubsan.M.loaded_segments (0x13ffc : word) = Some W_13f00.
Proof. vm_refl. Qed.
Lemma D_13f00 : decode_any W_13f00 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f04 : bv 32 := 0x04a5c263.
Lemma F_13f04 : fetch_word Ubsan.M.loaded_segments (0x14000 : word) = Some W_13f04.
Proof. vm_refl. Qed.
Lemma D_13f04 : decode_any W_13f04 = Some (Branch BC_LT 11 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f08 : bv 32 := 0xffffd517.
Lemma F_13f08 : fetch_word Ubsan.M.loaded_segments (0x14004 : word) = Some W_13f08.
Proof. vm_refl. Qed.
Lemma D_13f08 : decode_any W_13f08 = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f0c : bv 32 := 0xffffc597.
Lemma F_13f0c : fetch_word Ubsan.M.loaded_segments (0x14008 : word) = Some W_13f0c.
Proof. vm_refl. Qed.
Lemma D_13f0c : decode_any W_13f0c = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f10 : bv 32 := 0xa8650513.
Lemma F_13f10 : fetch_word Ubsan.M.loaded_segments (0x1400c : word) = Some W_13f10.
Proof. vm_refl. Qed.
Lemma D_13f10 : decode_any W_13f10 = Some (OpImm ALU_ADD 10 10 2694, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f14 : bv 32 := 0x5fe58593.
Lemma F_13f14 : fetch_word Ubsan.M.loaded_segments (0x14010 : word) = Some W_13f14.
Proof. vm_refl. Qed.
Lemma D_13f14 : decode_any W_13f14 = Some (OpImm ALU_ADD 11 11 1534, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f18 : bv 32 := 0x02c0006f.
Lemma F_13f18 : fetch_word Ubsan.M.loaded_segments (0x14014 : word) = Some W_13f18.
Proof. vm_refl. Qed.
Lemma D_13f18 : decode_any W_13f18 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f1c : bv 32 := 0x04d5e863.
Lemma F_13f1c : fetch_word Ubsan.M.loaded_segments (0x14018 : word) = Some W_13f1c.
Proof. vm_refl. Qed.
Lemma D_13f1c : decode_any W_13f1c = Some (Branch BC_LTU 11 13 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f20 : bv 32 := 0x0000c517.
Lemma F_13f20 : fetch_word Ubsan.M.loaded_segments (0x1401c : word) = Some W_13f20.
Proof. vm_refl. Qed.
Lemma D_13f20 : decode_any W_13f20 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f24 : bv 32 := 0x9b453503.
Lemma F_13f24 : fetch_word Ubsan.M.loaded_segments (0x14020 : word) = Some W_13f24.
Proof. vm_refl. Qed.
Lemma D_13f24 : decode_any W_13f24 = Some (Load SZ8 true 10 10 2484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f28 : bv 32 := 0x00052503.
Lemma F_13f28 : fetch_word Ubsan.M.loaded_segments (0x14024 : word) = Some W_13f28.
Proof. vm_refl. Qed.
Lemma D_13f28 : decode_any W_13f28 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f2c : bv 32 := 0x00500593.
Lemma F_13f2c : fetch_word Ubsan.M.loaded_segments (0x14028 : word) = Some W_13f2c.
Proof. vm_refl. Qed.
Lemma D_13f2c : decode_any W_13f2c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f30 : bv 32 := 0x00a5cc63.
Lemma F_13f30 : fetch_word Ubsan.M.loaded_segments (0x1402c : word) = Some W_13f30.
Proof. vm_refl. Qed.
Lemma D_13f30 : decode_any W_13f30 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f34 : bv 32 := 0xffffd517.
Lemma F_13f34 : fetch_word Ubsan.M.loaded_segments (0x14030 : word) = Some W_13f34.
Proof. vm_refl. Qed.
Lemma D_13f34 : decode_any W_13f34 = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f38 : bv 32 := 0xffffc597.
Lemma F_13f38 : fetch_word Ubsan.M.loaded_segments (0x14034 : word) = Some W_13f38.
Proof. vm_refl. Qed.
Lemma D_13f38 : decode_any W_13f38 = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f3c : bv 32 := 0x82d50513.
Lemma F_13f3c : fetch_word Ubsan.M.loaded_segments (0x14038 : word) = Some W_13f3c.
Proof. vm_refl. Qed.
Lemma D_13f3c : decode_any W_13f3c = Some (OpImm ALU_ADD 10 10 2093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f40 : bv 32 := 0x5d258593.
Lemma F_13f40 : fetch_word Ubsan.M.loaded_segments (0x1403c : word) = Some W_13f40.
Proof. vm_refl. Qed.
Lemma D_13f40 : decode_any W_13f40 = Some (OpImm ALU_ADD 11 11 1490, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f44 : bv 32 := 0xac9ff0ef.
Lemma F_13f44 : fetch_word Ubsan.M.loaded_segments (0x14040 : word) = Some W_13f44.
Proof. vm_refl. Qed.
Lemma D_13f44 : decode_any W_13f44 = Some (Jal 1 2095816, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f48 : bv 32 := 0x00000513.
Lemma F_13f48 : fetch_word Ubsan.M.loaded_segments (0x14044 : word) = Some W_13f48.
Proof. vm_refl. Qed.
Lemma D_13f48 : decode_any W_13f48 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f4c : bv 32 := 0x02813083.
Lemma F_13f4c : fetch_word Ubsan.M.loaded_segments (0x14048 : word) = Some W_13f4c.
Proof. vm_refl. Qed.
Lemma D_13f4c : decode_any W_13f4c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f50 : bv 32 := 0x02013403.
Lemma F_13f50 : fetch_word Ubsan.M.loaded_segments (0x1404c : word) = Some W_13f50.
Proof. vm_refl. Qed.
Lemma D_13f50 : decode_any W_13f50 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f54 : bv 32 := 0x01813483.
Lemma F_13f54 : fetch_word Ubsan.M.loaded_segments (0x14050 : word) = Some W_13f54.
Proof. vm_refl. Qed.
Lemma D_13f54 : decode_any W_13f54 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f58 : bv 32 := 0x01013903.
Lemma F_13f58 : fetch_word Ubsan.M.loaded_segments (0x14054 : word) = Some W_13f58.
Proof. vm_refl. Qed.
Lemma D_13f58 : decode_any W_13f58 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f5c : bv 32 := 0x00813983.
Lemma F_13f5c : fetch_word Ubsan.M.loaded_segments (0x14058 : word) = Some W_13f5c.
Proof. vm_refl. Qed.
Lemma D_13f5c : decode_any W_13f5c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f60 : bv 32 := 0x00013a03.
Lemma F_13f60 : fetch_word Ubsan.M.loaded_segments (0x1405c : word) = Some W_13f60.
Proof. vm_refl. Qed.
Lemma D_13f60 : decode_any W_13f60 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f64 : bv 32 := 0x03010113.
Lemma F_13f64 : fetch_word Ubsan.M.loaded_segments (0x14060 : word) = Some W_13f64.
Proof. vm_refl. Qed.
Lemma D_13f64 : decode_any W_13f64 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f68 : bv 32 := 0x00008067.
Lemma F_13f68 : fetch_word Ubsan.M.loaded_segments (0x14064 : word) = Some W_13f68.
Proof. vm_refl. Qed.
Lemma D_13f68 : decode_any W_13f68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f6c : bv 32 := 0x00050993.
Lemma F_13f6c : fetch_word Ubsan.M.loaded_segments (0x14068 : word) = Some W_13f6c.
Proof. vm_refl. Qed.
Lemma D_13f6c : decode_any W_13f6c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f70 : bv 32 := 0x00058493.
Lemma F_13f70 : fetch_word Ubsan.M.loaded_segments (0x1406c : word) = Some W_13f70.
Proof. vm_refl. Qed.
Lemma D_13f70 : decode_any W_13f70 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f74 : bv 32 := 0x00060413.
Lemma F_13f74 : fetch_word Ubsan.M.loaded_segments (0x14070 : word) = Some W_13f74.
Proof. vm_refl. Qed.
Lemma D_13f74 : decode_any W_13f74 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f78 : bv 32 := 0x00100513.
Lemma F_13f78 : fetch_word Ubsan.M.loaded_segments (0x14074 : word) = Some W_13f78.
Proof. vm_refl. Qed.
Lemma D_13f78 : decode_any W_13f78 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f7c : bv 32 := 0x04000593.
Lemma F_13f7c : fetch_word Ubsan.M.loaded_segments (0x14078 : word) = Some W_13f7c.
Proof. vm_refl. Qed.
Lemma D_13f7c : decode_any W_13f7c = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f80 : bv 32 := 0x4cd020ef.
Lemma F_13f80 : fetch_word Ubsan.M.loaded_segments (0x1407c : word) = Some W_13f80.
Proof. vm_refl. Qed.
Lemma D_13f80 : decode_any W_13f80 = Some (Jal 1 11468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f84 : bv 32 := 0x04050863.
Lemma F_13f84 : fetch_word Ubsan.M.loaded_segments (0x14080 : word) = Some W_13f84.
Proof. vm_refl. Qed.
Lemma D_13f84 : decode_any W_13f84 = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f88 : bv 32 := 0x00050913.
Lemma F_13f88 : fetch_word Ubsan.M.loaded_segments (0x14084 : word) = Some W_13f88.
Proof. vm_refl. Qed.
Lemma D_13f88 : decode_any W_13f88 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f8c : bv 32 := 0x00098593.
Lemma F_13f8c : fetch_word Ubsan.M.loaded_segments (0x14088 : word) = Some W_13f8c.
Proof. vm_refl. Qed.
Lemma D_13f8c : decode_any W_13f8c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f90 : bv 32 := 0x364000ef.
Lemma F_13f90 : fetch_word Ubsan.M.loaded_segments (0x1408c : word) = Some W_13f90.
Proof. vm_refl. Qed.
Lemma D_13f90 : decode_any W_13f90 = Some (Jal 1 868, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f94 : bv 32 := 0x00090513.
Lemma F_13f94 : fetch_word Ubsan.M.loaded_segments (0x14090 : word) = Some W_13f94.
Proof. vm_refl. Qed.
Lemma D_13f94 : decode_any W_13f94 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f98 : bv 32 := 0x00048593.
Lemma F_13f98 : fetch_word Ubsan.M.loaded_segments (0x14094 : word) = Some W_13f98.
Proof. vm_refl. Qed.
Lemma D_13f98 : decode_any W_13f98 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f9c : bv 32 := 0x3e0000ef.
Lemma F_13f9c : fetch_word Ubsan.M.loaded_segments (0x14098 : word) = Some W_13f9c.
Proof. vm_refl. Qed.
Lemma D_13f9c : decode_any W_13f9c = Some (Jal 1 992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fa0 : bv 32 := 0x00090513.
Lemma F_13fa0 : fetch_word Ubsan.M.loaded_segments (0x1409c : word) = Some W_13fa0.
Proof. vm_refl. Qed.
Lemma D_13fa0 : decode_any W_13fa0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fa4 : bv 32 := 0x00040593.
Lemma F_13fa4 : fetch_word Ubsan.M.loaded_segments (0x140a0 : word) = Some W_13fa4.
Proof. vm_refl. Qed.
Lemma D_13fa4 : decode_any W_13fa4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fa8 : bv 32 := 0x45c000ef.
Lemma F_13fa8 : fetch_word Ubsan.M.loaded_segments (0x140a4 : word) = Some W_13fa8.
Proof. vm_refl. Qed.
Lemma D_13fa8 : decode_any W_13fa8 = Some (Jal 1 1116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fac : bv 32 := 0x00797593.
Lemma F_13fac : fetch_word Ubsan.M.loaded_segments (0x140a8 : word) = Some W_13fac.
Proof. vm_refl. Qed.
Lemma D_13fac : decode_any W_13fac = Some (OpImm ALU_AND 11 18 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fb0 : bv 32 := 0x06059463.
Lemma F_13fb0 : fetch_word Ubsan.M.loaded_segments (0x140ac : word) = Some W_13fb0.
Proof. vm_refl. Qed.
Lemma D_13fb0 : decode_any W_13fb0 = Some (Branch BC_NE 11 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fb4 : bv 32 := 0x00090513.
Lemma F_13fb4 : fetch_word Ubsan.M.loaded_segments (0x140b0 : word) = Some W_13fb4.
Proof. vm_refl. Qed.
Lemma D_13fb4 : decode_any W_13fb4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fb8 : bv 32 := 0x01492823.
Lemma F_13fb8 : fetch_word Ubsan.M.loaded_segments (0x140b4 : word) = Some W_13fb8.
Proof. vm_refl. Qed.
Lemma D_13fb8 : decode_any W_13fb8 = Some (Store SZ4 18 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fbc : bv 32 := 0xfe84041b.
Lemma F_13fbc : fetch_word Ubsan.M.loaded_segments (0x140b8 : word) = Some W_13fbc.
Proof. vm_refl. Qed.
Lemma D_13fbc : decode_any W_13fbc = Some (OpImm32 8 8 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fc0 : bv 32 := 0xff747413.
Lemma F_13fc0 : fetch_word Ubsan.M.loaded_segments (0x140bc : word) = Some W_13fc0.
Proof. vm_refl. Qed.
Lemma D_13fc0 : decode_any W_13fc0 = Some (OpImm ALU_AND 8 8 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fc4 : bv 32 := 0x00100593.
Lemma F_13fc4 : fetch_word Ubsan.M.loaded_segments (0x140c0 : word) = Some W_13fc4.
Proof. vm_refl. Qed.
Lemma D_13fc4 : decode_any W_13fc4 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fc8 : bv 32 := 0x02040a63.
Lemma F_13fc8 : fetch_word Ubsan.M.loaded_segments (0x140c4 : word) = Some W_13fc8.
Proof. vm_refl. Qed.
Lemma D_13fc8 : decode_any W_13fc8 = Some (Branch BC_EQ 8 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fcc : bv 32 := 0x00100613.
Lemma F_13fcc : fetch_word Ubsan.M.loaded_segments (0x140c8 : word) = Some W_13fcc.
Proof. vm_refl. Qed.
Lemma D_13fcc : decode_any W_13fcc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fd0 : bv 32 := 0x0300006f.
Lemma F_13fd0 : fetch_word Ubsan.M.loaded_segments (0x140cc : word) = Some W_13fd0.
Proof. vm_refl. Qed.
Lemma D_13fd0 : decode_any W_13fd0 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fd4 : bv 32 := 0x0000c517.
Lemma F_13fd4 : fetch_word Ubsan.M.loaded_segments (0x140d0 : word) = Some W_13fd4.
Proof. vm_refl. Qed.
Lemma D_13fd4 : decode_any W_13fd4 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fd8 : bv 32 := 0x90053503.
Lemma F_13fd8 : fetch_word Ubsan.M.loaded_segments (0x140d4 : word) = Some W_13fd8.
Proof. vm_refl. Qed.
Lemma D_13fd8 : decode_any W_13fd8 = Some (Load SZ8 true 10 10 2304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fdc : bv 32 := 0x00052503.
Lemma F_13fdc : fetch_word Ubsan.M.loaded_segments (0x140d8 : word) = Some W_13fdc.
Proof. vm_refl. Qed.
Lemma D_13fdc : decode_any W_13fdc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fe0 : bv 32 := 0x00500593.
Lemma F_13fe0 : fetch_word Ubsan.M.loaded_segments (0x140dc : word) = Some W_13fe0.
Proof. vm_refl. Qed.
Lemma D_13fe0 : decode_any W_13fe0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fe4 : bv 32 := 0xf6a5c2e3.
Lemma F_13fe4 : fetch_word Ubsan.M.loaded_segments (0x140e0 : word) = Some W_13fe4.
Proof. vm_refl. Qed.
Lemma D_13fe4 : decode_any W_13fe4 = Some (Branch BC_LT 11 10 8036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fe8 : bv 32 := 0xffffc517.
Lemma F_13fe8 : fetch_word Ubsan.M.loaded_segments (0x140e4 : word) = Some W_13fe8.
Proof. vm_refl. Qed.
Lemma D_13fe8 : decode_any W_13fe8 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fec : bv 32 := 0xffffc597.
Lemma F_13fec : fetch_word Ubsan.M.loaded_segments (0x140e8 : word) = Some W_13fec.
Proof. vm_refl. Qed.
Lemma D_13fec : decode_any W_13fec = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ff0 : bv 32 := 0x32050513.
Lemma F_13ff0 : fetch_word Ubsan.M.loaded_segments (0x140ec : word) = Some W_13ff0.
Proof. vm_refl. Qed.
Lemma D_13ff0 : decode_any W_13ff0 = Some (OpImm ALU_ADD 10 10 800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ff4 : bv 32 := 0x51e58593.
Lemma F_13ff4 : fetch_word Ubsan.M.loaded_segments (0x140f0 : word) = Some W_13ff4.
Proof. vm_refl. Qed.
Lemma D_13ff4 : decode_any W_13ff4 = Some (OpImm ALU_ADD 11 11 1310, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ff8 : bv 32 := 0xe99ff06f.
Lemma F_13ff8 : fetch_word Ubsan.M.loaded_segments (0x140f4 : word) = Some W_13ff8.
Proof. vm_refl. Qed.
Lemma D_13ff8 : decode_any W_13ff8 = Some (Jal 0 2096792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ffc : bv 32 := 0x00300613.
Lemma F_13ffc : fetch_word Ubsan.M.loaded_segments (0x140f8 : word) = Some W_13ffc.
Proof. vm_refl. Qed.
Lemma D_13ffc : decode_any W_13ffc = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.
