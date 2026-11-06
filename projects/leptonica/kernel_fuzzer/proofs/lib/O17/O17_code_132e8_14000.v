(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.H Require GcFlushS17.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_13858 : bv 32 := 0xfd010113.
Lemma F_13858 : fetch_word Plain.M.loaded_segments (0x13954 : word) = Some W_13858.
Proof. vm_refl. Qed.
Lemma D_13858 : decode_any W_13858 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1385c : bv 32 := 0x02113423.
Lemma F_1385c : fetch_word Plain.M.loaded_segments (0x13958 : word) = Some W_1385c.
Proof. vm_refl. Qed.
Lemma D_1385c : decode_any W_1385c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13860 : bv 32 := 0x02813023.
Lemma F_13860 : fetch_word Plain.M.loaded_segments (0x1395c : word) = Some W_13860.
Proof. vm_refl. Qed.
Lemma D_13860 : decode_any W_13860 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13864 : bv 32 := 0x00913c23.
Lemma F_13864 : fetch_word Plain.M.loaded_segments (0x13960 : word) = Some W_13864.
Proof. vm_refl. Qed.
Lemma D_13864 : decode_any W_13864 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13868 : bv 32 := 0x00058413.
Lemma F_13868 : fetch_word Plain.M.loaded_segments (0x13964 : word) = Some W_13868.
Proof. vm_refl. Qed.
Lemma D_13868 : decode_any W_13868 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1386c : bv 32 := 0x00300593.
Lemma F_1386c : fetch_word Plain.M.loaded_segments (0x13968 : word) = Some W_1386c.
Proof. vm_refl. Qed.
Lemma D_1386c : decode_any W_1386c = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13870 : bv 32 := 0x04b46463.
Lemma F_13870 : fetch_word Plain.M.loaded_segments (0x1396c : word) = Some W_13870.
Proof. vm_refl. Qed.
Lemma D_13870 : decode_any W_13870 = Some (Branch BC_LTU 8 11 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13874 : bv 32 := 0x00050493.
Lemma F_13874 : fetch_word Plain.M.loaded_segments (0x13970 : word) = Some W_13874.
Proof. vm_refl. Qed.
Lemma D_13874 : decode_any W_13874 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13878 : bv 32 := 0x00000517.
Lemma F_13878 : fetch_word Plain.M.loaded_segments (0x13974 : word) = Some W_13878.
Proof. vm_refl. Qed.
Lemma D_13878 : decode_any W_13878 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1387c : bv 32 := 0x05850513.
Lemma F_1387c : fetch_word Plain.M.loaded_segments (0x13978 : word) = Some W_1387c.
Proof. vm_refl. Qed.
Lemma D_1387c : decode_any W_1387c = Some (OpImm ALU_ADD 10 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13880 : bv 32 := 0x170000ef.
Lemma F_13880 : fetch_word Plain.M.loaded_segments (0x1397c : word) = Some W_13880.
Proof. vm_refl. Qed.
Lemma D_13880 : decode_any W_13880 = Some (Jal 1 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13884 : bv 32 := 0x00048513.
Lemma F_13884 : fetch_word Plain.M.loaded_segments (0x13980 : word) = Some W_13884.
Proof. vm_refl. Qed.
Lemma D_13884 : decode_any W_13884 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13888 : bv 32 := 0x00040593.
Lemma F_13888 : fetch_word Plain.M.loaded_segments (0x13984 : word) = Some W_13888.
Proof. vm_refl. Qed.
Lemma D_13888 : decode_any W_13888 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1388c : bv 32 := 0x750010ef.
Lemma F_1388c : fetch_word Plain.M.loaded_segments (0x13988 : word) = Some W_1388c.
Proof. vm_refl. Qed.
Lemma D_1388c : decode_any W_1388c = Some (Jal 1 5968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13890 : bv 32 := 0x00a13823.
Lemma F_13890 : fetch_word Plain.M.loaded_segments (0x1398c : word) = Some W_13890.
Proof. vm_refl. Qed.
Lemma D_13890 : decode_any W_13890 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13894 : bv 32 := 0x02050263.
Lemma F_13894 : fetch_word Plain.M.loaded_segments (0x13990 : word) = Some W_13894.
Proof. vm_refl. Qed.
Lemma D_13894 : decode_any W_13894 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13898 : bv 32 := 0x00200593.
Lemma F_13898 : fetch_word Plain.M.loaded_segments (0x13994 : word) = Some W_13898.
Proof. vm_refl. Qed.
Lemma D_13898 : decode_any W_13898 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1389c : bv 32 := 0x00200613.
Lemma F_1389c : fetch_word Plain.M.loaded_segments (0x13998 : word) = Some W_1389c.
Proof. vm_refl. Qed.
Lemma D_1389c : decode_any W_1389c = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138a0 : bv 32 := 0x74d010ef.
Lemma F_138a0 : fetch_word Plain.M.loaded_segments (0x1399c : word) = Some W_138a0.
Proof. vm_refl. Qed.
Lemma D_138a0 : decode_any W_138a0 = Some (Jal 1 8012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138a4 : bv 32 := 0x00a13423.
Lemma F_138a4 : fetch_word Plain.M.loaded_segments (0x139a0 : word) = Some W_138a4.
Proof. vm_refl. Qed.
Lemma D_138a4 : decode_any W_138a4 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138a8 : bv 32 := 0x01010513.
Lemma F_138a8 : fetch_word Plain.M.loaded_segments (0x139a4 : word) = Some W_138a8.
Proof. vm_refl. Qed.
Lemma D_138a8 : decode_any W_138a8 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138ac : bv 32 := 0x660000ef.
Lemma F_138ac : fetch_word Plain.M.loaded_segments (0x139a8 : word) = Some W_138ac.
Proof. vm_refl. Qed.
Lemma D_138ac : decode_any W_138ac = Some (Jal 1 1632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138b0 : bv 32 := 0x00810513.
Lemma F_138b0 : fetch_word Plain.M.loaded_segments (0x139ac : word) = Some W_138b0.
Proof. vm_refl. Qed.
Lemma D_138b0 : decode_any W_138b0 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138b4 : bv 32 := 0x59d010ef.
Lemma F_138b4 : fetch_word Plain.M.loaded_segments (0x139b0 : word) = Some W_138b4.
Proof. vm_refl. Qed.
Lemma D_138b4 : decode_any W_138b4 = Some (Jal 1 7580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138b8 : bv 32 := 0x00000513.
Lemma F_138b8 : fetch_word Plain.M.loaded_segments (0x139b4 : word) = Some W_138b8.
Proof. vm_refl. Qed.
Lemma D_138b8 : decode_any W_138b8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138bc : bv 32 := 0x02813083.
Lemma F_138bc : fetch_word Plain.M.loaded_segments (0x139b8 : word) = Some W_138bc.
Proof. vm_refl. Qed.
Lemma D_138bc : decode_any W_138bc = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138c0 : bv 32 := 0x02013403.
Lemma F_138c0 : fetch_word Plain.M.loaded_segments (0x139bc : word) = Some W_138c0.
Proof. vm_refl. Qed.
Lemma D_138c0 : decode_any W_138c0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138c4 : bv 32 := 0x01813483.
Lemma F_138c4 : fetch_word Plain.M.loaded_segments (0x139c0 : word) = Some W_138c4.
Proof. vm_refl. Qed.
Lemma D_138c4 : decode_any W_138c4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138c8 : bv 32 := 0x03010113.
Lemma F_138c8 : fetch_word Plain.M.loaded_segments (0x139c4 : word) = Some W_138c8.
Proof. vm_refl. Qed.
Lemma D_138c8 : decode_any W_138c8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138cc : bv 32 := 0x00008067.
Lemma F_138cc : fetch_word Plain.M.loaded_segments (0x139c8 : word) = Some W_138cc.
Proof. vm_refl. Qed.
Lemma D_138cc : decode_any W_138cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138d4 : bv 32 := 0xff010113.
Lemma F_138d4 : fetch_word Plain.M.loaded_segments (0x139d0 : word) = Some W_138d4.
Proof. vm_refl. Qed.
Lemma D_138d4 : decode_any W_138d4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138d8 : bv 32 := 0x00113423.
Lemma F_138d8 : fetch_word Plain.M.loaded_segments (0x139d4 : word) = Some W_138d8.
Proof. vm_refl. Qed.
Lemma D_138d8 : decode_any W_138d8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138dc : bv 32 := 0x00813023.
Lemma F_138dc : fetch_word Plain.M.loaded_segments (0x139d8 : word) = Some W_138dc.
Proof. vm_refl. Qed.
Lemma D_138dc : decode_any W_138dc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138e0 : bv 32 := 0x00060413.
Lemma F_138e0 : fetch_word Plain.M.loaded_segments (0x139dc : word) = Some W_138e0.
Proof. vm_refl. Qed.
Lemma D_138e0 : decode_any W_138e0 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138e4 : bv 32 := 0x00050613.
Lemma F_138e4 : fetch_word Plain.M.loaded_segments (0x139e0 : word) = Some W_138e4.
Proof. vm_refl. Qed.
Lemma D_138e4 : decode_any W_138e4 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138e8 : bv 32 := 0xffffd517.
Lemma F_138e8 : fetch_word Plain.M.loaded_segments (0x139e4 : word) = Some W_138e8.
Proof. vm_refl. Qed.
Lemma D_138e8 : decode_any W_138e8 = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138ec : bv 32 := 0x14750513.
Lemma F_138ec : fetch_word Plain.M.loaded_segments (0x139e8 : word) = Some W_138ec.
Proof. vm_refl. Qed.
Lemma D_138ec : decode_any W_138ec = Some (OpImm ALU_ADD 10 10 327, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138f0 : bv 32 := 0x018000ef.
Lemma F_138f0 : fetch_word Plain.M.loaded_segments (0x139ec : word) = Some W_138f0.
Proof. vm_refl. Qed.
Lemma D_138f0 : decode_any W_138f0 = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138f4 : bv 32 := 0x00040513.
Lemma F_138f4 : fetch_word Plain.M.loaded_segments (0x139f0 : word) = Some W_138f4.
Proof. vm_refl. Qed.
Lemma D_138f4 : decode_any W_138f4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138f8 : bv 32 := 0x00813083.
Lemma F_138f8 : fetch_word Plain.M.loaded_segments (0x139f4 : word) = Some W_138f8.
Proof. vm_refl. Qed.
Lemma D_138f8 : decode_any W_138f8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138fc : bv 32 := 0x00013403.
Lemma F_138fc : fetch_word Plain.M.loaded_segments (0x139f8 : word) = Some W_138fc.
Proof. vm_refl. Qed.
Lemma D_138fc : decode_any W_138fc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13900 : bv 32 := 0x01010113.
Lemma F_13900 : fetch_word Plain.M.loaded_segments (0x139fc : word) = Some W_13900.
Proof. vm_refl. Qed.
Lemma D_13900 : decode_any W_13900 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13904 : bv 32 := 0x00008067.
Lemma F_13904 : fetch_word Plain.M.loaded_segments (0x13a00 : word) = Some W_13904.
Proof. vm_refl. Qed.
Lemma D_13904 : decode_any W_13904 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139a4 : bv 32 := 0xff010113.
Lemma F_139a4 : fetch_word Plain.M.loaded_segments (0x13aa0 : word) = Some W_139a4.
Proof. vm_refl. Qed.
Lemma D_139a4 : decode_any W_139a4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139a8 : bv 32 := 0x00113423.
Lemma F_139a8 : fetch_word Plain.M.loaded_segments (0x13aa4 : word) = Some W_139a8.
Proof. vm_refl. Qed.
Lemma D_139a8 : decode_any W_139a8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139ac : bv 32 := 0x00813023.
Lemma F_139ac : fetch_word Plain.M.loaded_segments (0x13aa8 : word) = Some W_139ac.
Proof. vm_refl. Qed.
Lemma D_139ac : decode_any W_139ac = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139b0 : bv 32 := 0x00060413.
Lemma F_139b0 : fetch_word Plain.M.loaded_segments (0x13aac : word) = Some W_139b0.
Proof. vm_refl. Qed.
Lemma D_139b0 : decode_any W_139b0 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139b4 : bv 32 := 0x00050613.
Lemma F_139b4 : fetch_word Plain.M.loaded_segments (0x13ab0 : word) = Some W_139b4.
Proof. vm_refl. Qed.
Lemma D_139b4 : decode_any W_139b4 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139b8 : bv 32 := 0xffffd517.
Lemma F_139b8 : fetch_word Plain.M.loaded_segments (0x13ab4 : word) = Some W_139b8.
Proof. vm_refl. Qed.
Lemma D_139b8 : decode_any W_139b8 = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139bc : bv 32 := 0x07750513.
Lemma F_139bc : fetch_word Plain.M.loaded_segments (0x13ab8 : word) = Some W_139bc.
Proof. vm_refl. Qed.
Lemma D_139bc : decode_any W_139bc = Some (OpImm ALU_ADD 10 10 119, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139c0 : bv 32 := 0xf49ff0ef.
Lemma F_139c0 : fetch_word Plain.M.loaded_segments (0x13abc : word) = Some W_139c0.
Proof. vm_refl. Qed.
Lemma D_139c0 : decode_any W_139c0 = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139c4 : bv 32 := 0x00040513.
Lemma F_139c4 : fetch_word Plain.M.loaded_segments (0x13ac0 : word) = Some W_139c4.
Proof. vm_refl. Qed.
Lemma D_139c4 : decode_any W_139c4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139c8 : bv 32 := 0x00813083.
Lemma F_139c8 : fetch_word Plain.M.loaded_segments (0x13ac4 : word) = Some W_139c8.
Proof. vm_refl. Qed.
Lemma D_139c8 : decode_any W_139c8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139cc : bv 32 := 0x00013403.
Lemma F_139cc : fetch_word Plain.M.loaded_segments (0x13ac8 : word) = Some W_139cc.
Proof. vm_refl. Qed.
Lemma D_139cc : decode_any W_139cc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139d0 : bv 32 := 0x01010113.
Lemma F_139d0 : fetch_word Plain.M.loaded_segments (0x13acc : word) = Some W_139d0.
Proof. vm_refl. Qed.
Lemma D_139d0 : decode_any W_139d0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139d4 : bv 32 := 0x00008067.
Lemma F_139d4 : fetch_word Plain.M.loaded_segments (0x13ad0 : word) = Some W_139d4.
Proof. vm_refl. Qed.
Lemma D_139d4 : decode_any W_139d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139f0 : bv 32 := 0x00051663.
Lemma F_139f0 : fetch_word Plain.M.loaded_segments (0x13aec : word) = Some W_139f0.
Proof. vm_refl. Qed.
Lemma D_139f0 : decode_any W_139f0 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139fc : bv 32 := 0x0000c597.
Lemma F_139fc : fetch_word Plain.M.loaded_segments (0x13af8 : word) = Some W_139fc.
Proof. vm_refl. Qed.
Lemma D_139fc : decode_any W_139fc = Some (Auipc 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a00 : bv 32 := 0x6ca5b823.
Lemma F_13a00 : fetch_word Plain.M.loaded_segments (0x13afc : word) = Some W_13a00.
Proof. vm_refl. Qed.
Lemma D_13a00 : decode_any W_13a00 = Some (Store SZ8 11 10 1744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a04 : bv 32 := 0x00008067.
Lemma F_13a04 : fetch_word Plain.M.loaded_segments (0x13b00 : word) = Some W_13a04.
Proof. vm_refl. Qed.
Lemma D_13a04 : decode_any W_13a04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a08 : bv 32 := 0xff010113.
Lemma F_13a08 : fetch_word Plain.M.loaded_segments (0x13b04 : word) = Some W_13a08.
Proof. vm_refl. Qed.
Lemma D_13a08 : decode_any W_13a08 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a0c : bv 32 := 0x00113423.
Lemma F_13a0c : fetch_word Plain.M.loaded_segments (0x13b08 : word) = Some W_13a0c.
Proof. vm_refl. Qed.
Lemma D_13a0c : decode_any W_13a0c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a10 : bv 32 := 0x00813023.
Lemma F_13a10 : fetch_word Plain.M.loaded_segments (0x13b0c : word) = Some W_13a10.
Proof. vm_refl. Qed.
Lemma D_13a10 : decode_any W_13a10 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a14 : bv 32 := 0x080000ef.
Lemma F_13a14 : fetch_word Plain.M.loaded_segments (0x13b10 : word) = Some W_13a14.
Proof. vm_refl. Qed.
Lemma D_13a14 : decode_any W_13a14 = Some (Jal 1 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a18 : bv 32 := 0x02050863.
Lemma F_13a18 : fetch_word Plain.M.loaded_segments (0x13b14 : word) = Some W_13a18.
Proof. vm_refl. Qed.
Lemma D_13a18 : decode_any W_13a18 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a1c : bv 32 := 0x00456603.
Lemma F_13a1c : fetch_word Plain.M.loaded_segments (0x13b18 : word) = Some W_13a1c.
Proof. vm_refl. Qed.
Lemma D_13a1c : decode_any W_13a1c = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a20 : bv 32 := 0x01056683.
Lemma F_13a20 : fetch_word Plain.M.loaded_segments (0x13b1c : word) = Some W_13a20.
Proof. vm_refl. Qed.
Lemma D_13a20 : decode_any W_13a20 = Some (Load SZ4 false 13 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a24 : bv 32 := 0x03853583.
Lemma F_13a24 : fetch_word Plain.M.loaded_segments (0x13b20 : word) = Some W_13a24.
Proof. vm_refl. Qed.
Lemma D_13a24 : decode_any W_13a24 = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a28 : bv 32 := 0x02c68633.
Lemma F_13a28 : fetch_word Plain.M.loaded_segments (0x13b24 : word) = Some W_13a28.
Proof. vm_refl. Qed.
Lemma D_13a28 : decode_any W_13a28 = Some (Mul M_MUL 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a2c : bv 32 := 0x00261613.
Lemma F_13a2c : fetch_word Plain.M.loaded_segments (0x13b28 : word) = Some W_13a2c.
Proof. vm_refl. Qed.
Lemma D_13a2c : decode_any W_13a2c = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a30 : bv 32 := 0x00050413.
Lemma F_13a30 : fetch_word Plain.M.loaded_segments (0x13b2c : word) = Some W_13a30.
Proof. vm_refl. Qed.
Lemma D_13a30 : decode_any W_13a30 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a34 : bv 32 := 0x00058513.
Lemma F_13a34 : fetch_word Plain.M.loaded_segments (0x13b30 : word) = Some W_13a34.
Proof. vm_refl. Qed.
Lemma D_13a34 : decode_any W_13a34 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a38 : bv 32 := 0x00000593.
Lemma F_13a38 : fetch_word Plain.M.loaded_segments (0x13b34 : word) = Some W_13a38.
Proof. vm_refl. Qed.
Lemma D_13a38 : decode_any W_13a38 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a3c : bv 32 := 0x0040a0ef.
Lemma F_13a3c : fetch_word Plain.M.loaded_segments (0x13b38 : word) = Some W_13a3c.
Proof. vm_refl. Qed.
Lemma D_13a3c : decode_any W_13a3c = Some (Jal 1 40964, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a40 : bv 32 := 0x00040513.
Lemma F_13a40 : fetch_word Plain.M.loaded_segments (0x13b3c : word) = Some W_13a40.
Proof. vm_refl. Qed.
Lemma D_13a40 : decode_any W_13a40 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a44 : bv 32 := 0x0400006f.
Lemma F_13a44 : fetch_word Plain.M.loaded_segments (0x13b40 : word) = Some W_13a44.
Proof. vm_refl. Qed.
Lemma D_13a44 : decode_any W_13a44 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a48 : bv 32 := 0x0000b517.
Lemma F_13a48 : fetch_word Plain.M.loaded_segments (0x13b44 : word) = Some W_13a48.
Proof. vm_refl. Qed.
Lemma D_13a48 : decode_any W_13a48 = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a4c : bv 32 := 0x60c53503.
Lemma F_13a4c : fetch_word Plain.M.loaded_segments (0x13b48 : word) = Some W_13a4c.
Proof. vm_refl. Qed.
Lemma D_13a4c : decode_any W_13a4c = Some (Load SZ8 true 10 10 1548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a50 : bv 32 := 0x00052503.
Lemma F_13a50 : fetch_word Plain.M.loaded_segments (0x13b4c : word) = Some W_13a50.
Proof. vm_refl. Qed.
Lemma D_13a50 : decode_any W_13a50 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a54 : bv 32 := 0x00500593.
Lemma F_13a54 : fetch_word Plain.M.loaded_segments (0x13b50 : word) = Some W_13a54.
Proof. vm_refl. Qed.
Lemma D_13a54 : decode_any W_13a54 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a58 : bv 32 := 0x02a5c463.
Lemma F_13a58 : fetch_word Plain.M.loaded_segments (0x13b54 : word) = Some W_13a58.
Proof. vm_refl. Qed.
Lemma D_13a58 : decode_any W_13a58 = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a5c : bv 32 := 0xffffd517.
Lemma F_13a5c : fetch_word Plain.M.loaded_segments (0x13b58 : word) = Some W_13a5c.
Proof. vm_refl. Qed.
Lemma D_13a5c : decode_any W_13a5c = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a60 : bv 32 := 0xffffd597.
Lemma F_13a60 : fetch_word Plain.M.loaded_segments (0x13b5c : word) = Some W_13a60.
Proof. vm_refl. Qed.
Lemma D_13a60 : decode_any W_13a60 = Some (Auipc 11 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a64 : bv 32 := 0x8a050513.
Lemma F_13a64 : fetch_word Plain.M.loaded_segments (0x13b60 : word) = Some W_13a64.
Proof. vm_refl. Qed.
Lemma D_13a64 : decode_any W_13a64 = Some (OpImm ALU_ADD 10 10 2208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a68 : bv 32 := 0xa1a58593.
Lemma F_13a68 : fetch_word Plain.M.loaded_segments (0x13b64 : word) = Some W_13a68.
Proof. vm_refl. Qed.
Lemma D_13a68 : decode_any W_13a68 = Some (OpImm ALU_ADD 11 11 2586, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a6c : bv 32 := 0x00000613.
Lemma F_13a6c : fetch_word Plain.M.loaded_segments (0x13b68 : word) = Some W_13a6c.
Proof. vm_refl. Qed.
Lemma D_13a6c : decode_any W_13a6c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a70 : bv 32 := 0x00813083.
Lemma F_13a70 : fetch_word Plain.M.loaded_segments (0x13b6c : word) = Some W_13a70.
Proof. vm_refl. Qed.
Lemma D_13a70 : decode_any W_13a70 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a74 : bv 32 := 0x00013403.
Lemma F_13a74 : fetch_word Plain.M.loaded_segments (0x13b70 : word) = Some W_13a74.
Proof. vm_refl. Qed.
Lemma D_13a74 : decode_any W_13a74 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a78 : bv 32 := 0x01010113.
Lemma F_13a78 : fetch_word Plain.M.loaded_segments (0x13b74 : word) = Some W_13a78.
Proof. vm_refl. Qed.
Lemma D_13a78 : decode_any W_13a78 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a7c : bv 32 := 0xf29ff06f.
Lemma F_13a7c : fetch_word Plain.M.loaded_segments (0x13b78 : word) = Some W_13a7c.
Proof. vm_refl. Qed.
Lemma D_13a7c : decode_any W_13a7c = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a84 : bv 32 := 0x00813083.
Lemma F_13a84 : fetch_word Plain.M.loaded_segments (0x13b80 : word) = Some W_13a84.
Proof. vm_refl. Qed.
Lemma D_13a84 : decode_any W_13a84 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a88 : bv 32 := 0x00013403.
Lemma F_13a88 : fetch_word Plain.M.loaded_segments (0x13b84 : word) = Some W_13a88.
Proof. vm_refl. Qed.
Lemma D_13a88 : decode_any W_13a88 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a8c : bv 32 := 0x01010113.
Lemma F_13a8c : fetch_word Plain.M.loaded_segments (0x13b88 : word) = Some W_13a8c.
Proof. vm_refl. Qed.
Lemma D_13a8c : decode_any W_13a8c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a90 : bv 32 := 0x00008067.
Lemma F_13a90 : fetch_word Plain.M.loaded_segments (0x13b8c : word) = Some W_13a90.
Proof. vm_refl. Qed.
Lemma D_13a90 : decode_any W_13a90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a94 : bv 32 := 0xfd010113.
Lemma F_13a94 : fetch_word Plain.M.loaded_segments (0x13b90 : word) = Some W_13a94.
Proof. vm_refl. Qed.
Lemma D_13a94 : decode_any W_13a94 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a98 : bv 32 := 0x02113423.
Lemma F_13a98 : fetch_word Plain.M.loaded_segments (0x13b94 : word) = Some W_13a98.
Proof. vm_refl. Qed.
Lemma D_13a98 : decode_any W_13a98 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a9c : bv 32 := 0x02813023.
Lemma F_13a9c : fetch_word Plain.M.loaded_segments (0x13b98 : word) = Some W_13a9c.
Proof. vm_refl. Qed.
Lemma D_13a9c : decode_any W_13a9c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13aa0 : bv 32 := 0x00913c23.
Lemma F_13aa0 : fetch_word Plain.M.loaded_segments (0x13b9c : word) = Some W_13aa0.
Proof. vm_refl. Qed.
Lemma D_13aa0 : decode_any W_13aa0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13aa4 : bv 32 := 0x01213823.
Lemma F_13aa4 : fetch_word Plain.M.loaded_segments (0x13ba0 : word) = Some W_13aa4.
Proof. vm_refl. Qed.
Lemma D_13aa4 : decode_any W_13aa4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13aa8 : bv 32 := 0x00058493.
Lemma F_13aa8 : fetch_word Plain.M.loaded_segments (0x13ba4 : word) = Some W_13aa8.
Proof. vm_refl. Qed.
Lemma D_13aa8 : decode_any W_13aa8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13aac : bv 32 := 0x124000ef.
Lemma F_13aac : fetch_word Plain.M.loaded_segments (0x13ba8 : word) = Some W_13aac.
Proof. vm_refl. Qed.
Lemma D_13aac : decode_any W_13aac = Some (Jal 1 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ab0 : bv 32 := 0x02050e63.
Lemma F_13ab0 : fetch_word Plain.M.loaded_segments (0x13bac : word) = Some W_13ab0.
Proof. vm_refl. Qed.
Lemma D_13ab0 : decode_any W_13ab0 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ab4 : bv 32 := 0x00050413.
Lemma F_13ab4 : fetch_word Plain.M.loaded_segments (0x13bb0 : word) = Some W_13ab4.
Proof. vm_refl. Qed.
Lemma D_13ab4 : decode_any W_13ab4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ab8 : bv 32 := 0x01052503.
Lemma F_13ab8 : fetch_word Plain.M.loaded_segments (0x13bb4 : word) = Some W_13ab8.
Proof. vm_refl. Qed.
Lemma D_13ab8 : decode_any W_13ab8 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13abc : bv 32 := 0x0000c597.
Lemma F_13abc : fetch_word Plain.M.loaded_segments (0x13bb8 : word) = Some W_13abc.
Proof. vm_refl. Qed.
Lemma D_13abc : decode_any W_13abc = Some (Auipc 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ac0 : bv 32 := 0x61858913.
Lemma F_13ac0 : fetch_word Plain.M.loaded_segments (0x13bbc : word) = Some W_13ac0.
Proof. vm_refl. Qed.
Lemma D_13ac0 : decode_any W_13ac0 = Some (OpImm ALU_ADD 18 11 1560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ac4 : bv 32 := 0x00093583.
Lemma F_13ac4 : fetch_word Plain.M.loaded_segments (0x13bc0 : word) = Some W_13ac4.
Proof. vm_refl. Qed.
Lemma D_13ac4 : decode_any W_13ac4 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ac8 : bv 32 := 0x02a48533.
Lemma F_13ac8 : fetch_word Plain.M.loaded_segments (0x13bc4 : word) = Some W_13ac8.
Proof. vm_refl. Qed.
Lemma D_13ac8 : decode_any W_13ac8 = Some (Mul M_MUL 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13acc : bv 32 := 0x00251513.
Lemma F_13acc : fetch_word Plain.M.loaded_segments (0x13bc8 : word) = Some W_13acc.
Proof. vm_refl. Qed.
Lemma D_13acc : decode_any W_13acc = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ad0 : bv 32 := 0x000580e7.
Lemma F_13ad0 : fetch_word Plain.M.loaded_segments (0x13bcc : word) = Some W_13ad0.
Proof. vm_refl. Qed.
Lemma D_13ad0 : decode_any W_13ad0 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ad4 : bv 32 := 0x04050c63.
Lemma F_13ad4 : fetch_word Plain.M.loaded_segments (0x13bd0 : word) = Some W_13ad4.
Proof. vm_refl. Qed.
Lemma D_13ad4 : decode_any W_13ad4 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ad8 : bv 32 := 0x02a43c23.
Lemma F_13ad8 : fetch_word Plain.M.loaded_segments (0x13bd4 : word) = Some W_13ad8.
Proof. vm_refl. Qed.
Lemma D_13ad8 : decode_any W_13ad8 = Some (Store SZ8 8 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13adc : bv 32 := 0x00040513.
Lemma F_13adc : fetch_word Plain.M.loaded_segments (0x13bd8 : word) = Some W_13adc.
Proof. vm_refl. Qed.
Lemma D_13adc : decode_any W_13adc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ae0 : bv 32 := 0x00000593.
Lemma F_13ae0 : fetch_word Plain.M.loaded_segments (0x13bdc : word) = Some W_13ae0.
Proof. vm_refl. Qed.
Lemma D_13ae0 : decode_any W_13ae0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ae4 : bv 32 := 0x171000ef.
Lemma F_13ae4 : fetch_word Plain.M.loaded_segments (0x13be0 : word) = Some W_13ae4.
Proof. vm_refl. Qed.
Lemma D_13ae4 : decode_any W_13ae4 = Some (Jal 1 2416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ae8 : bv 32 := 0x0cc0006f.
Lemma F_13ae8 : fetch_word Plain.M.loaded_segments (0x13be4 : word) = Some W_13ae8.
Proof. vm_refl. Qed.
Lemma D_13ae8 : decode_any W_13ae8 = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13aec : bv 32 := 0x0000b517.
Lemma F_13aec : fetch_word Plain.M.loaded_segments (0x13be8 : word) = Some W_13aec.
Proof. vm_refl. Qed.
Lemma D_13aec : decode_any W_13aec = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13af0 : bv 32 := 0x56853503.
Lemma F_13af0 : fetch_word Plain.M.loaded_segments (0x13bec : word) = Some W_13af0.
Proof. vm_refl. Qed.
Lemma D_13af0 : decode_any W_13af0 = Some (Load SZ8 true 10 10 1384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13af4 : bv 32 := 0x00052503.
Lemma F_13af4 : fetch_word Plain.M.loaded_segments (0x13bf0 : word) = Some W_13af4.
Proof. vm_refl. Qed.
Lemma D_13af4 : decode_any W_13af4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13af8 : bv 32 := 0x00500593.
Lemma F_13af8 : fetch_word Plain.M.loaded_segments (0x13bf4 : word) = Some W_13af8.
Proof. vm_refl. Qed.
Lemma D_13af8 : decode_any W_13af8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13afc : bv 32 := 0x0aa5ca63.
Lemma F_13afc : fetch_word Plain.M.loaded_segments (0x13bf8 : word) = Some W_13afc.
Proof. vm_refl. Qed.
Lemma D_13afc : decode_any W_13afc = Some (Branch BC_LT 11 10 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b00 : bv 32 := 0xffffc517.
Lemma F_13b00 : fetch_word Plain.M.loaded_segments (0x13bfc : word) = Some W_13b00.
Proof. vm_refl. Qed.
Lemma D_13b00 : decode_any W_13b00 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b04 : bv 32 := 0xffffd597.
Lemma F_13b04 : fetch_word Plain.M.loaded_segments (0x13c00 : word) = Some W_13b04.
Proof. vm_refl. Qed.
Lemma D_13b04 : decode_any W_13b04 = Some (Auipc 11 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b08 : bv 32 := 0x7fc50513.
Lemma F_13b08 : fetch_word Plain.M.loaded_segments (0x13c04 : word) = Some W_13b08.
Proof. vm_refl. Qed.
Lemma D_13b08 : decode_any W_13b08 = Some (OpImm ALU_ADD 10 10 2044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b0c : bv 32 := 0x8e958593.
Lemma F_13b0c : fetch_word Plain.M.loaded_segments (0x13c08 : word) = Some W_13b0c.
Proof. vm_refl. Qed.
Lemma D_13b0c : decode_any W_13b0c = Some (OpImm ALU_ADD 11 11 2281, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b10 : bv 32 := 0x00000613.
Lemma F_13b10 : fetch_word Plain.M.loaded_segments (0x13c0c : word) = Some W_13b10.
Proof. vm_refl. Qed.
Lemma D_13b10 : decode_any W_13b10 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b14 : bv 32 := 0x02813083.
Lemma F_13b14 : fetch_word Plain.M.loaded_segments (0x13c10 : word) = Some W_13b14.
Proof. vm_refl. Qed.
Lemma D_13b14 : decode_any W_13b14 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b18 : bv 32 := 0x02013403.
Lemma F_13b18 : fetch_word Plain.M.loaded_segments (0x13c14 : word) = Some W_13b18.
Proof. vm_refl. Qed.
Lemma D_13b18 : decode_any W_13b18 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b1c : bv 32 := 0x01813483.
Lemma F_13b1c : fetch_word Plain.M.loaded_segments (0x13c18 : word) = Some W_13b1c.
Proof. vm_refl. Qed.
Lemma D_13b1c : decode_any W_13b1c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b20 : bv 32 := 0x01013903.
Lemma F_13b20 : fetch_word Plain.M.loaded_segments (0x13c1c : word) = Some W_13b20.
Proof. vm_refl. Qed.
Lemma D_13b20 : decode_any W_13b20 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b24 : bv 32 := 0x03010113.
Lemma F_13b24 : fetch_word Plain.M.loaded_segments (0x13c20 : word) = Some W_13b24.
Proof. vm_refl. Qed.
Lemma D_13b24 : decode_any W_13b24 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b28 : bv 32 := 0xe7dff06f.
Lemma F_13b28 : fetch_word Plain.M.loaded_segments (0x13c24 : word) = Some W_13b28.
Proof. vm_refl. Qed.
Lemma D_13b28 : decode_any W_13b28 = Some (Jal 0 2096764, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b2c : bv 32 := 0x01440513.
Lemma F_13b2c : fetch_word Plain.M.loaded_segments (0x13c28 : word) = Some W_13b2c.
Proof. vm_refl. Qed.
Lemma D_13b2c : decode_any W_13b2c = Some (OpImm ALU_ADD 10 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b30 : bv 32 := 0xfff00593.
Lemma F_13b30 : fetch_word Plain.M.loaded_segments (0x13c2c : word) = Some W_13b30.
Proof. vm_refl. Qed.
Lemma D_13b30 : decode_any W_13b30 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b34 : bv 32 := 0x06b5252f.
Lemma F_13b34 : fetch_word Plain.M.loaded_segments (0x13c30 : word) = Some W_13b34.
Proof. vm_refl. Qed.
Lemma D_13b34 : decode_any W_13b34 = Some (Amo AMO_ADD AW true true 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b38 : bv 32 := 0x00100593.
Lemma F_13b38 : fetch_word Plain.M.loaded_segments (0x13c34 : word) = Some W_13b38.
Proof. vm_refl. Qed.
Lemma D_13b38 : decode_any W_13b38 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b3c : bv 32 := 0x04b51063.
Lemma F_13b3c : fetch_word Plain.M.loaded_segments (0x13c38 : word) = Some W_13b3c.
Proof. vm_refl. Qed.
Lemma D_13b3c : decode_any W_13b3c = Some (Branch BC_NE 10 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b40 : bv 32 := 0x03843503.
Lemma F_13b40 : fetch_word Plain.M.loaded_segments (0x13c3c : word) = Some W_13b40.
Proof. vm_refl. Qed.
Lemma D_13b40 : decode_any W_13b40 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b44 : bv 32 := 0x00050663.
Lemma F_13b44 : fetch_word Plain.M.loaded_segments (0x13c40 : word) = Some W_13b44.
Proof. vm_refl. Qed.
Lemma D_13b44 : decode_any W_13b44 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b50 : bv 32 := 0x02843503.
Lemma F_13b50 : fetch_word Plain.M.loaded_segments (0x13c4c : word) = Some W_13b50.
Proof. vm_refl. Qed.
Lemma D_13b50 : decode_any W_13b50 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b54 : bv 32 := 0x00050463.
Lemma F_13b54 : fetch_word Plain.M.loaded_segments (0x13c50 : word) = Some W_13b54.
Proof. vm_refl. Qed.
Lemma D_13b54 : decode_any W_13b54 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b5c : bv 32 := 0x03043503.
Lemma F_13b5c : fetch_word Plain.M.loaded_segments (0x13c58 : word) = Some W_13b5c.
Proof. vm_refl. Qed.
Lemma D_13b5c : decode_any W_13b5c = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b60 : bv 32 := 0x00a13423.
Lemma F_13b60 : fetch_word Plain.M.loaded_segments (0x13c5c : word) = Some W_13b60.
Proof. vm_refl. Qed.
Lemma D_13b60 : decode_any W_13b60 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b64 : bv 32 := 0x00050863.
Lemma F_13b64 : fetch_word Plain.M.loaded_segments (0x13c60 : word) = Some W_13b64.
Proof. vm_refl. Qed.
Lemma D_13b64 : decode_any W_13b64 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b74 : bv 32 := 0x00040513.
Lemma F_13b74 : fetch_word Plain.M.loaded_segments (0x13c70 : word) = Some W_13b74.
Proof. vm_refl. Qed.
Lemma D_13b74 : decode_any W_13b74 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b78 : bv 32 := 0x191020ef.
Lemma F_13b78 : fetch_word Plain.M.loaded_segments (0x13c74 : word) = Some W_13b78.
Proof. vm_refl. Qed.
Lemma D_13b78 : decode_any W_13b78 = Some (Jal 1 10640, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b7c : bv 32 := 0x0000b517.
Lemma F_13b7c : fetch_word Plain.M.loaded_segments (0x13c78 : word) = Some W_13b7c.
Proof. vm_refl. Qed.
Lemma D_13b7c : decode_any W_13b7c = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b80 : bv 32 := 0x4d853503.
Lemma F_13b80 : fetch_word Plain.M.loaded_segments (0x13c7c : word) = Some W_13b80.
Proof. vm_refl. Qed.
Lemma D_13b80 : decode_any W_13b80 = Some (Load SZ8 true 10 10 1240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b84 : bv 32 := 0x00052503.
Lemma F_13b84 : fetch_word Plain.M.loaded_segments (0x13c80 : word) = Some W_13b84.
Proof. vm_refl. Qed.
Lemma D_13b84 : decode_any W_13b84 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b88 : bv 32 := 0x00500593.
Lemma F_13b88 : fetch_word Plain.M.loaded_segments (0x13c84 : word) = Some W_13b88.
Proof. vm_refl. Qed.
Lemma D_13b88 : decode_any W_13b88 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b8c : bv 32 := 0x02a5c263.
Lemma F_13b8c : fetch_word Plain.M.loaded_segments (0x13c88 : word) = Some W_13b8c.
Proof. vm_refl. Qed.
Lemma D_13b8c : decode_any W_13b8c = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b90 : bv 32 := 0xffffd517.
Lemma F_13b90 : fetch_word Plain.M.loaded_segments (0x13c8c : word) = Some W_13b90.
Proof. vm_refl. Qed.
Lemma D_13b90 : decode_any W_13b90 = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b94 : bv 32 := 0xffffd597.
Lemma F_13b94 : fetch_word Plain.M.loaded_segments (0x13c90 : word) = Some W_13b94.
Proof. vm_refl. Qed.
Lemma D_13b94 : decode_any W_13b94 = Some (Auipc 11 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b98 : bv 32 := 0xd1750513.
Lemma F_13b98 : fetch_word Plain.M.loaded_segments (0x13c94 : word) = Some W_13b98.
Proof. vm_refl. Qed.
Lemma D_13b98 : decode_any W_13b98 = Some (OpImm ALU_ADD 10 10 3351, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b9c : bv 32 := 0x85958593.
Lemma F_13b9c : fetch_word Plain.M.loaded_segments (0x13c98 : word) = Some W_13b9c.
Proof. vm_refl. Qed.
Lemma D_13b9c : decode_any W_13b9c = Some (OpImm ALU_ADD 11 11 2137, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ba0 : bv 32 := 0x00000613.
Lemma F_13ba0 : fetch_word Plain.M.loaded_segments (0x13c9c : word) = Some W_13ba0.
Proof. vm_refl. Qed.
Lemma D_13ba0 : decode_any W_13ba0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ba4 : bv 32 := 0xe01ff0ef.
Lemma F_13ba4 : fetch_word Plain.M.loaded_segments (0x13ca0 : word) = Some W_13ba4.
Proof. vm_refl. Qed.
Lemma D_13ba4 : decode_any W_13ba4 = Some (Jal 1 2096640, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ba8 : bv 32 := 0x00050413.
Lemma F_13ba8 : fetch_word Plain.M.loaded_segments (0x13ca4 : word) = Some W_13ba8.
Proof. vm_refl. Qed.
Lemma D_13ba8 : decode_any W_13ba8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bac : bv 32 := 0x0080006f.
Lemma F_13bac : fetch_word Plain.M.loaded_segments (0x13ca8 : word) = Some W_13bac.
Proof. vm_refl. Qed.
Lemma D_13bac : decode_any W_13bac = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bb4 : bv 32 := 0x00040513.
Lemma F_13bb4 : fetch_word Plain.M.loaded_segments (0x13cb0 : word) = Some W_13bb4.
Proof. vm_refl. Qed.
Lemma D_13bb4 : decode_any W_13bb4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bb8 : bv 32 := 0x02813083.
Lemma F_13bb8 : fetch_word Plain.M.loaded_segments (0x13cb4 : word) = Some W_13bb8.
Proof. vm_refl. Qed.
Lemma D_13bb8 : decode_any W_13bb8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bbc : bv 32 := 0x02013403.
Lemma F_13bbc : fetch_word Plain.M.loaded_segments (0x13cb8 : word) = Some W_13bbc.
Proof. vm_refl. Qed.
Lemma D_13bbc : decode_any W_13bbc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bc0 : bv 32 := 0x01813483.
Lemma F_13bc0 : fetch_word Plain.M.loaded_segments (0x13cbc : word) = Some W_13bc0.
Proof. vm_refl. Qed.
Lemma D_13bc0 : decode_any W_13bc0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bc4 : bv 32 := 0x01013903.
Lemma F_13bc4 : fetch_word Plain.M.loaded_segments (0x13cc0 : word) = Some W_13bc4.
Proof. vm_refl. Qed.
Lemma D_13bc4 : decode_any W_13bc4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bc8 : bv 32 := 0x03010113.
Lemma F_13bc8 : fetch_word Plain.M.loaded_segments (0x13cc4 : word) = Some W_13bc8.
Proof. vm_refl. Qed.
Lemma D_13bc8 : decode_any W_13bc8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bcc : bv 32 := 0x00008067.
Lemma F_13bcc : fetch_word Plain.M.loaded_segments (0x13cc8 : word) = Some W_13bcc.
Proof. vm_refl. Qed.
Lemma D_13bcc : decode_any W_13bcc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bd0 : bv 32 := 0xfd010113.
Lemma F_13bd0 : fetch_word Plain.M.loaded_segments (0x13ccc : word) = Some W_13bd0.
Proof. vm_refl. Qed.
Lemma D_13bd0 : decode_any W_13bd0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bd4 : bv 32 := 0x02113423.
Lemma F_13bd4 : fetch_word Plain.M.loaded_segments (0x13cd0 : word) = Some W_13bd4.
Proof. vm_refl. Qed.
Lemma D_13bd4 : decode_any W_13bd4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bd8 : bv 32 := 0x02813023.
Lemma F_13bd8 : fetch_word Plain.M.loaded_segments (0x13cd4 : word) = Some W_13bd8.
Proof. vm_refl. Qed.
Lemma D_13bd8 : decode_any W_13bd8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bdc : bv 32 := 0x00913c23.
Lemma F_13bdc : fetch_word Plain.M.loaded_segments (0x13cd8 : word) = Some W_13bdc.
Proof. vm_refl. Qed.
Lemma D_13bdc : decode_any W_13bdc = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13be0 : bv 32 := 0x01213823.
Lemma F_13be0 : fetch_word Plain.M.loaded_segments (0x13cdc : word) = Some W_13be0.
Proof. vm_refl. Qed.
Lemma D_13be0 : decode_any W_13be0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13be4 : bv 32 := 0x01313423.
Lemma F_13be4 : fetch_word Plain.M.loaded_segments (0x13ce0 : word) = Some W_13be4.
Proof. vm_refl. Qed.
Lemma D_13be4 : decode_any W_13be4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13be8 : bv 32 := 0x01413023.
Lemma F_13be8 : fetch_word Plain.M.loaded_segments (0x13ce4 : word) = Some W_13be8.
Proof. vm_refl. Qed.
Lemma D_13be8 : decode_any W_13be8 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bec : bv 32 := 0x02000693.
Lemma F_13bec : fetch_word Plain.M.loaded_segments (0x13ce8 : word) = Some W_13bec.
Proof. vm_refl. Qed.
Lemma D_13bec : decode_any W_13bec = Some (OpImm ALU_ADD 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bf0 : bv 32 := 0x14c6ea63.
Lemma F_13bf0 : fetch_word Plain.M.loaded_segments (0x13cec : word) = Some W_13bf0.
Proof. vm_refl. Qed.
Lemma D_13bf0 : decode_any W_13bf0 = Some (Branch BC_LTU 13 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bf4 : bv 32 := 0x101016b7.
Lemma F_13bf4 : fetch_word Plain.M.loaded_segments (0x13cf0 : word) = Some W_13bf4.
Proof. vm_refl. Qed.
Lemma D_13bf4 : decode_any W_13bf4 = Some (Lui 13 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bf8 : bv 32 := 0x00469693.
Lemma F_13bf8 : fetch_word Plain.M.loaded_segments (0x13cf4 : word) = Some W_13bf8.
Proof. vm_refl. Qed.
Lemma D_13bf8 : decode_any W_13bf8 = Some (ShiftImm ALU_SLL 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bfc : bv 32 := 0x11668693.
Lemma F_13bfc : fetch_word Plain.M.loaded_segments (0x13cf8 : word) = Some W_13bfc.
Proof. vm_refl. Qed.
Lemma D_13bfc : decode_any W_13bfc = Some (OpImm ALU_ADD 13 13 278, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c00 : bv 32 := 0x00c6d6b3.
Lemma F_13c00 : fetch_word Plain.M.loaded_segments (0x13cfc : word) = Some W_13c00.
Proof. vm_refl. Qed.
Lemma D_13c00 : decode_any W_13c00 = Some (Op ALU_SRL 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c04 : bv 32 := 0x0016f693.
Lemma F_13c04 : fetch_word Plain.M.loaded_segments (0x13d00 : word) = Some W_13c04.
Proof. vm_refl. Qed.
Lemma D_13c04 : decode_any W_13c04 = Some (OpImm ALU_AND 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c08 : bv 32 := 0x12068e63.
Lemma F_13c08 : fetch_word Plain.M.loaded_segments (0x13d04 : word) = Some W_13c08.
Proof. vm_refl. Qed.
Lemma D_13c08 : decode_any W_13c08 = Some (Branch BC_EQ 13 0 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c0c : bv 32 := 0x06a05a63.
Lemma F_13c0c : fetch_word Plain.M.loaded_segments (0x13d08 : word) = Some W_13c0c.
Proof. vm_refl. Qed.
Lemma D_13c0c : decode_any W_13c0c = Some (Branch BC_GE 0 10 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c10 : bv 32 := 0x08b05c63.
Lemma F_13c10 : fetch_word Plain.M.loaded_segments (0x13d0c : word) = Some W_13c10.
Proof. vm_refl. Qed.
Lemma D_13c10 : decode_any W_13c10 = Some (Branch BC_GE 0 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c14 : bv 32 := 0x02a606b3.
Lemma F_13c14 : fetch_word Plain.M.loaded_segments (0x13d10 : word) = Some W_13c14.
Proof. vm_refl. Qed.
Lemma D_13c14 : decode_any W_13c14 = Some (Mul M_MUL 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c18 : bv 32 := 0x20000737.
Lemma F_13c18 : fetch_word Plain.M.loaded_segments (0x13d14 : word) = Some W_13c18.
Proof. vm_refl. Qed.
Lemma D_13c18 : decode_any W_13c18 = Some (Lui 14 131072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c1c : bv 32 := 0xfe17071b.
Lemma F_13c1c : fetch_word Plain.M.loaded_segments (0x13d18 : word) = Some W_13c1c.
Proof. vm_refl. Qed.
Lemma D_13c1c : decode_any W_13c1c = Some (OpImm32 14 14 4065, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c20 : bv 32 := 0x0ae6e863.
Lemma F_13c20 : fetch_word Plain.M.loaded_segments (0x13d1c : word) = Some W_13c20.
Proof. vm_refl. Qed.
Lemma D_13c20 : decode_any W_13c20 = Some (Branch BC_LTU 13 14 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cd0 : bv 32 := 0x01f68693.
Lemma F_13cd0 : fetch_word Plain.M.loaded_segments (0x13dcc : word) = Some W_13cd0.
Proof. vm_refl. Qed.
Lemma D_13cd0 : decode_any W_13cd0 = Some (OpImm ALU_ADD 13 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cd4 : bv 32 := 0x0056d413.
Lemma F_13cd4 : fetch_word Plain.M.loaded_segments (0x13dd0 : word) = Some W_13cd4.
Proof. vm_refl. Qed.
Lemma D_13cd4 : decode_any W_13cd4 = Some (ShiftImm ALU_SRL 8 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cd8 : bv 32 := 0x02b406b3.
Lemma F_13cd8 : fetch_word Plain.M.loaded_segments (0x13dd4 : word) = Some W_13cd8.
Proof. vm_refl. Qed.
Lemma D_13cd8 : decode_any W_13cd8 = Some (Mul M_MUL 13 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cdc : bv 32 := 0x00269693.
Lemma F_13cdc : fetch_word Plain.M.loaded_segments (0x13dd8 : word) = Some W_13cdc.
Proof. vm_refl. Qed.
Lemma D_13cdc : decode_any W_13cdc = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ce0 : bv 32 := 0x01f6d713.
Lemma F_13ce0 : fetch_word Plain.M.loaded_segments (0x13ddc : word) = Some W_13ce0.
Proof. vm_refl. Qed.
Lemma D_13ce0 : decode_any W_13ce0 = Some (ShiftImm ALU_SRL 14 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ce4 : bv 32 := 0x0a070463.
Lemma F_13ce4 : fetch_word Plain.M.loaded_segments (0x13de0 : word) = Some W_13ce4.
Proof. vm_refl. Qed.
Lemma D_13ce4 : decode_any W_13ce4 = Some (Branch BC_EQ 14 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d44 : bv 32 := 0x0000b517.
Lemma F_13d44 : fetch_word Plain.M.loaded_segments (0x13e40 : word) = Some W_13d44.
Proof. vm_refl. Qed.
Lemma D_13d44 : decode_any W_13d44 = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d48 : bv 32 := 0x31053503.
Lemma F_13d48 : fetch_word Plain.M.loaded_segments (0x13e44 : word) = Some W_13d48.
Proof. vm_refl. Qed.
Lemma D_13d48 : decode_any W_13d48 = Some (Load SZ8 true 10 10 784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d4c : bv 32 := 0x00052503.
Lemma F_13d4c : fetch_word Plain.M.loaded_segments (0x13e48 : word) = Some W_13d4c.
Proof. vm_refl. Qed.
Lemma D_13d4c : decode_any W_13d4c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d50 : bv 32 := 0x00500593.
Lemma F_13d50 : fetch_word Plain.M.loaded_segments (0x13e4c : word) = Some W_13d50.
Proof. vm_refl. Qed.
Lemma D_13d50 : decode_any W_13d50 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d54 : bv 32 := 0x0ca5c663.
Lemma F_13d54 : fetch_word Plain.M.loaded_segments (0x13e50 : word) = Some W_13d54.
Proof. vm_refl. Qed.
Lemma D_13d54 : decode_any W_13d54 = Some (Branch BC_LT 11 10 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d58 : bv 32 := 0xffffc517.
Lemma F_13d58 : fetch_word Plain.M.loaded_segments (0x13e54 : word) = Some W_13d58.
Proof. vm_refl. Qed.
Lemma D_13d58 : decode_any W_13d58 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d5c : bv 32 := 0xffffc597.
Lemma F_13d5c : fetch_word Plain.M.loaded_segments (0x13e58 : word) = Some W_13d5c.
Proof. vm_refl. Qed.
Lemma D_13d5c : decode_any W_13d5c = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d60 : bv 32 := 0x5fc50513.
Lemma F_13d60 : fetch_word Plain.M.loaded_segments (0x13e5c : word) = Some W_13d60.
Proof. vm_refl. Qed.
Lemma D_13d60 : decode_any W_13d60 = Some (OpImm ALU_ADD 10 10 1532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d64 : bv 32 := 0x78f58593.
Lemma F_13d64 : fetch_word Plain.M.loaded_segments (0x13e60 : word) = Some W_13d64.
Proof. vm_refl. Qed.
Lemma D_13d64 : decode_any W_13d64 = Some (OpImm ALU_ADD 11 11 1935, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d68 : bv 32 := 0x00000613.
Lemma F_13d68 : fetch_word Plain.M.loaded_segments (0x13e64 : word) = Some W_13d68.
Proof. vm_refl. Qed.
Lemma D_13d68 : decode_any W_13d68 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d6c : bv 32 := 0x02813083.
Lemma F_13d6c : fetch_word Plain.M.loaded_segments (0x13e68 : word) = Some W_13d6c.
Proof. vm_refl. Qed.
Lemma D_13d6c : decode_any W_13d6c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d70 : bv 32 := 0x02013403.
Lemma F_13d70 : fetch_word Plain.M.loaded_segments (0x13e6c : word) = Some W_13d70.
Proof. vm_refl. Qed.
Lemma D_13d70 : decode_any W_13d70 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d74 : bv 32 := 0x01813483.
Lemma F_13d74 : fetch_word Plain.M.loaded_segments (0x13e70 : word) = Some W_13d74.
Proof. vm_refl. Qed.
Lemma D_13d74 : decode_any W_13d74 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d78 : bv 32 := 0x01013903.
Lemma F_13d78 : fetch_word Plain.M.loaded_segments (0x13e74 : word) = Some W_13d78.
Proof. vm_refl. Qed.
Lemma D_13d78 : decode_any W_13d78 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d7c : bv 32 := 0x00813983.
Lemma F_13d7c : fetch_word Plain.M.loaded_segments (0x13e78 : word) = Some W_13d7c.
Proof. vm_refl. Qed.
Lemma D_13d7c : decode_any W_13d7c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d80 : bv 32 := 0x00013a03.
Lemma F_13d80 : fetch_word Plain.M.loaded_segments (0x13e7c : word) = Some W_13d80.
Proof. vm_refl. Qed.
Lemma D_13d80 : decode_any W_13d80 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d84 : bv 32 := 0x03010113.
Lemma F_13d84 : fetch_word Plain.M.loaded_segments (0x13e80 : word) = Some W_13d84.
Proof. vm_refl. Qed.
Lemma D_13d84 : decode_any W_13d84 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d88 : bv 32 := 0xc1dff06f.
Lemma F_13d88 : fetch_word Plain.M.loaded_segments (0x13e84 : word) = Some W_13d88.
Proof. vm_refl. Qed.
Lemma D_13d88 : decode_any W_13d88 = Some (Jal 0 2096156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d8c : bv 32 := 0x04000737.
Lemma F_13d8c : fetch_word Plain.M.loaded_segments (0x13e88 : word) = Some W_13d8c.
Proof. vm_refl. Qed.
Lemma D_13d8c : decode_any W_13d8c = Some (Lui 14 16384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d90 : bv 32 := 0x0017071b.
Lemma F_13d90 : fetch_word Plain.M.loaded_segments (0x13e8c : word) = Some W_13d90.
Proof. vm_refl. Qed.
Lemma D_13d90 : decode_any W_13d90 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d94 : bv 32 := 0x02e6e663.
Lemma F_13d94 : fetch_word Plain.M.loaded_segments (0x13e90 : word) = Some W_13d94.
Proof. vm_refl. Qed.
Lemma D_13d94 : decode_any W_13d94 = Some (Branch BC_LTU 13 14 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d98 : bv 32 := 0x0000b517.
Lemma F_13d98 : fetch_word Plain.M.loaded_segments (0x13e94 : word) = Some W_13d98.
Proof. vm_refl. Qed.
Lemma D_13d98 : decode_any W_13d98 = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d9c : bv 32 := 0x2bc53503.
Lemma F_13d9c : fetch_word Plain.M.loaded_segments (0x13e98 : word) = Some W_13d9c.
Proof. vm_refl. Qed.
Lemma D_13d9c : decode_any W_13d9c = Some (Load SZ8 true 10 10 700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13da0 : bv 32 := 0x00052503.
Lemma F_13da0 : fetch_word Plain.M.loaded_segments (0x13e9c : word) = Some W_13da0.
Proof. vm_refl. Qed.
Lemma D_13da0 : decode_any W_13da0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13da4 : bv 32 := 0x00500593.
Lemma F_13da4 : fetch_word Plain.M.loaded_segments (0x13ea0 : word) = Some W_13da4.
Proof. vm_refl. Qed.
Lemma D_13da4 : decode_any W_13da4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13da8 : bv 32 := 0x06a5cc63.
Lemma F_13da8 : fetch_word Plain.M.loaded_segments (0x13ea4 : word) = Some W_13da8.
Proof. vm_refl. Qed.
Lemma D_13da8 : decode_any W_13da8 = Some (Branch BC_LT 11 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13dac : bv 32 := 0xffffc517.
Lemma F_13dac : fetch_word Plain.M.loaded_segments (0x13ea8 : word) = Some W_13dac.
Proof. vm_refl. Qed.
Lemma D_13dac : decode_any W_13dac = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13db0 : bv 32 := 0xffffc597.
Lemma F_13db0 : fetch_word Plain.M.loaded_segments (0x13eac : word) = Some W_13db0.
Proof. vm_refl. Qed.
Lemma D_13db0 : decode_any W_13db0 = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13db4 : bv 32 := 0x4d850513.
Lemma F_13db4 : fetch_word Plain.M.loaded_segments (0x13eb0 : word) = Some W_13db4.
Proof. vm_refl. Qed.
Lemma D_13db4 : decode_any W_13db4 = Some (OpImm ALU_ADD 10 10 1240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13db8 : bv 32 := 0x73b58593.
Lemma F_13db8 : fetch_word Plain.M.loaded_segments (0x13eb4 : word) = Some W_13db8.
Proof. vm_refl. Qed.
Lemma D_13db8 : decode_any W_13db8 = Some (OpImm ALU_ADD 11 11 1851, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13dbc : bv 32 := 0x0600006f.
Lemma F_13dbc : fetch_word Plain.M.loaded_segments (0x13eb8 : word) = Some W_13dbc.
Proof. vm_refl. Qed.
Lemma D_13dbc : decode_any W_13dbc = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13dc0 : bv 32 := 0x000056b7.
Lemma F_13dc0 : fetch_word Plain.M.loaded_segments (0x13ebc : word) = Some W_13dc0.
Proof. vm_refl. Qed.
Lemma D_13dc0 : decode_any W_13dc0 = Some (Lui 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13dc4 : bv 32 := 0xe216869b.
Lemma F_13dc4 : fetch_word Plain.M.loaded_segments (0x13ec0 : word) = Some W_13dc4.
Proof. vm_refl. Qed.
Lemma D_13dc4 : decode_any W_13dc4 = Some (OpImm32 13 13 3617, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13dc8 : bv 32 := 0x02d56663.
Lemma F_13dc8 : fetch_word Plain.M.loaded_segments (0x13ec4 : word) = Some W_13dc8.
Proof. vm_refl. Qed.
Lemma D_13dc8 : decode_any W_13dc8 = Some (Branch BC_LTU 10 13 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13dcc : bv 32 := 0x0000b517.
Lemma F_13dcc : fetch_word Plain.M.loaded_segments (0x13ec8 : word) = Some W_13dcc.
Proof. vm_refl. Qed.
Lemma D_13dcc : decode_any W_13dcc = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13dd0 : bv 32 := 0x28853503.
Lemma F_13dd0 : fetch_word Plain.M.loaded_segments (0x13ecc : word) = Some W_13dd0.
Proof. vm_refl. Qed.
Lemma D_13dd0 : decode_any W_13dd0 = Some (Load SZ8 true 10 10 648, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13dd4 : bv 32 := 0x00052503.
Lemma F_13dd4 : fetch_word Plain.M.loaded_segments (0x13ed0 : word) = Some W_13dd4.
Proof. vm_refl. Qed.
Lemma D_13dd4 : decode_any W_13dd4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13dd8 : bv 32 := 0x00500593.
Lemma F_13dd8 : fetch_word Plain.M.loaded_segments (0x13ed4 : word) = Some W_13dd8.
Proof. vm_refl. Qed.
Lemma D_13dd8 : decode_any W_13dd8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ddc : bv 32 := 0x04a5c263.
Lemma F_13ddc : fetch_word Plain.M.loaded_segments (0x13ed8 : word) = Some W_13ddc.
Proof. vm_refl. Qed.
Lemma D_13ddc : decode_any W_13ddc = Some (Branch BC_LT 11 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13de0 : bv 32 := 0xffffd517.
Lemma F_13de0 : fetch_word Plain.M.loaded_segments (0x13edc : word) = Some W_13de0.
Proof. vm_refl. Qed.
Lemma D_13de0 : decode_any W_13de0 = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13de4 : bv 32 := 0xffffc597.
Lemma F_13de4 : fetch_word Plain.M.loaded_segments (0x13ee0 : word) = Some W_13de4.
Proof. vm_refl. Qed.
Lemma D_13de4 : decode_any W_13de4 = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13de8 : bv 32 := 0xb6450513.
Lemma F_13de8 : fetch_word Plain.M.loaded_segments (0x13ee4 : word) = Some W_13de8.
Proof. vm_refl. Qed.
Lemma D_13de8 : decode_any W_13de8 = Some (OpImm ALU_ADD 10 10 2916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13dec : bv 32 := 0x70758593.
Lemma F_13dec : fetch_word Plain.M.loaded_segments (0x13ee8 : word) = Some W_13dec.
Proof. vm_refl. Qed.
Lemma D_13dec : decode_any W_13dec = Some (OpImm ALU_ADD 11 11 1799, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13df0 : bv 32 := 0x02c0006f.
Lemma F_13df0 : fetch_word Plain.M.loaded_segments (0x13eec : word) = Some W_13df0.
Proof. vm_refl. Qed.
Lemma D_13df0 : decode_any W_13df0 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13df4 : bv 32 := 0x04d5e863.
Lemma F_13df4 : fetch_word Plain.M.loaded_segments (0x13ef0 : word) = Some W_13df4.
Proof. vm_refl. Qed.
Lemma D_13df4 : decode_any W_13df4 = Some (Branch BC_LTU 11 13 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13df8 : bv 32 := 0x0000b517.
Lemma F_13df8 : fetch_word Plain.M.loaded_segments (0x13ef4 : word) = Some W_13df8.
Proof. vm_refl. Qed.
Lemma D_13df8 : decode_any W_13df8 = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13dfc : bv 32 := 0x25c53503.
Lemma F_13dfc : fetch_word Plain.M.loaded_segments (0x13ef8 : word) = Some W_13dfc.
Proof. vm_refl. Qed.
Lemma D_13dfc : decode_any W_13dfc = Some (Load SZ8 true 10 10 604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e00 : bv 32 := 0x00052503.
Lemma F_13e00 : fetch_word Plain.M.loaded_segments (0x13efc : word) = Some W_13e00.
Proof. vm_refl. Qed.
Lemma D_13e00 : decode_any W_13e00 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e04 : bv 32 := 0x00500593.
Lemma F_13e04 : fetch_word Plain.M.loaded_segments (0x13f00 : word) = Some W_13e04.
Proof. vm_refl. Qed.
Lemma D_13e04 : decode_any W_13e04 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e08 : bv 32 := 0x00a5cc63.
Lemma F_13e08 : fetch_word Plain.M.loaded_segments (0x13f04 : word) = Some W_13e08.
Proof. vm_refl. Qed.
Lemma D_13e08 : decode_any W_13e08 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e0c : bv 32 := 0xffffd517.
Lemma F_13e0c : fetch_word Plain.M.loaded_segments (0x13f08 : word) = Some W_13e0c.
Proof. vm_refl. Qed.
Lemma D_13e0c : decode_any W_13e0c = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e10 : bv 32 := 0xffffc597.
Lemma F_13e10 : fetch_word Plain.M.loaded_segments (0x13f0c : word) = Some W_13e10.
Proof. vm_refl. Qed.
Lemma D_13e10 : decode_any W_13e10 = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e14 : bv 32 := 0x92950513.
Lemma F_13e14 : fetch_word Plain.M.loaded_segments (0x13f10 : word) = Some W_13e14.
Proof. vm_refl. Qed.
Lemma D_13e14 : decode_any W_13e14 = Some (OpImm ALU_ADD 10 10 2345, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e18 : bv 32 := 0x6db58593.
Lemma F_13e18 : fetch_word Plain.M.loaded_segments (0x13f14 : word) = Some W_13e18.
Proof. vm_refl. Qed.
Lemma D_13e18 : decode_any W_13e18 = Some (OpImm ALU_ADD 11 11 1755, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e1c : bv 32 := 0xaedff0ef.
Lemma F_13e1c : fetch_word Plain.M.loaded_segments (0x13f18 : word) = Some W_13e1c.
Proof. vm_refl. Qed.
Lemma D_13e1c : decode_any W_13e1c = Some (Jal 1 2095852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e20 : bv 32 := 0x00000513.
Lemma F_13e20 : fetch_word Plain.M.loaded_segments (0x13f1c : word) = Some W_13e20.
Proof. vm_refl. Qed.
Lemma D_13e20 : decode_any W_13e20 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e24 : bv 32 := 0x02813083.
Lemma F_13e24 : fetch_word Plain.M.loaded_segments (0x13f20 : word) = Some W_13e24.
Proof. vm_refl. Qed.
Lemma D_13e24 : decode_any W_13e24 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e28 : bv 32 := 0x02013403.
Lemma F_13e28 : fetch_word Plain.M.loaded_segments (0x13f24 : word) = Some W_13e28.
Proof. vm_refl. Qed.
Lemma D_13e28 : decode_any W_13e28 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e2c : bv 32 := 0x01813483.
Lemma F_13e2c : fetch_word Plain.M.loaded_segments (0x13f28 : word) = Some W_13e2c.
Proof. vm_refl. Qed.
Lemma D_13e2c : decode_any W_13e2c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e30 : bv 32 := 0x01013903.
Lemma F_13e30 : fetch_word Plain.M.loaded_segments (0x13f2c : word) = Some W_13e30.
Proof. vm_refl. Qed.
Lemma D_13e30 : decode_any W_13e30 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e34 : bv 32 := 0x00813983.
Lemma F_13e34 : fetch_word Plain.M.loaded_segments (0x13f30 : word) = Some W_13e34.
Proof. vm_refl. Qed.
Lemma D_13e34 : decode_any W_13e34 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e38 : bv 32 := 0x00013a03.
Lemma F_13e38 : fetch_word Plain.M.loaded_segments (0x13f34 : word) = Some W_13e38.
Proof. vm_refl. Qed.
Lemma D_13e38 : decode_any W_13e38 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e3c : bv 32 := 0x03010113.
Lemma F_13e3c : fetch_word Plain.M.loaded_segments (0x13f38 : word) = Some W_13e3c.
Proof. vm_refl. Qed.
Lemma D_13e3c : decode_any W_13e3c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e40 : bv 32 := 0x00008067.
Lemma F_13e40 : fetch_word Plain.M.loaded_segments (0x13f3c : word) = Some W_13e40.
Proof. vm_refl. Qed.
Lemma D_13e40 : decode_any W_13e40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e44 : bv 32 := 0x00050993.
Lemma F_13e44 : fetch_word Plain.M.loaded_segments (0x13f40 : word) = Some W_13e44.
Proof. vm_refl. Qed.
Lemma D_13e44 : decode_any W_13e44 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e48 : bv 32 := 0x00058913.
Lemma F_13e48 : fetch_word Plain.M.loaded_segments (0x13f44 : word) = Some W_13e48.
Proof. vm_refl. Qed.
Lemma D_13e48 : decode_any W_13e48 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e4c : bv 32 := 0x00060a13.
Lemma F_13e4c : fetch_word Plain.M.loaded_segments (0x13f48 : word) = Some W_13e4c.
Proof. vm_refl. Qed.
Lemma D_13e4c : decode_any W_13e4c = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e50 : bv 32 := 0x00100513.
Lemma F_13e50 : fetch_word Plain.M.loaded_segments (0x13f4c : word) = Some W_13e50.
Proof. vm_refl. Qed.
Lemma D_13e50 : decode_any W_13e50 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e54 : bv 32 := 0x04000593.
Lemma F_13e54 : fetch_word Plain.M.loaded_segments (0x13f50 : word) = Some W_13e54.
Proof. vm_refl. Qed.
Lemma D_13e54 : decode_any W_13e54 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e58 : bv 32 := 0x00100493.
Lemma F_13e58 : fetch_word Plain.M.loaded_segments (0x13f54 : word) = Some W_13e58.
Proof. vm_refl. Qed.
Lemma D_13e58 : decode_any W_13e58 = Some (OpImm ALU_ADD 9 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e5c : bv 32 := 0x574020ef.
Lemma F_13e5c : fetch_word Plain.M.loaded_segments (0x13f58 : word) = Some W_13e5c.
Proof. vm_refl. Qed.
Lemma D_13e5c : decode_any W_13e5c = Some (Jal 1 9588, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e60 : bv 32 := 0x02050463.
Lemma F_13e60 : fetch_word Plain.M.loaded_segments (0x13f5c : word) = Some W_13e60.
Proof. vm_refl. Qed.
Lemma D_13e60 : decode_any W_13e60 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e64 : bv 32 := 0xfe8a059b.
Lemma F_13e64 : fetch_word Plain.M.loaded_segments (0x13f60 : word) = Some W_13e64.
Proof. vm_refl. Qed.
Lemma D_13e64 : decode_any W_13e64 = Some (OpImm32 11 20 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e68 : bv 32 := 0xff75f593.
Lemma F_13e68 : fetch_word Plain.M.loaded_segments (0x13f64 : word) = Some W_13e68.
Proof. vm_refl. Qed.
Lemma D_13e68 : decode_any W_13e68 = Some (OpImm ALU_AND 11 11 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e6c : bv 32 := 0x01352023.
Lemma F_13e6c : fetch_word Plain.M.loaded_segments (0x13f68 : word) = Some W_13e6c.
Proof. vm_refl. Qed.
Lemma D_13e6c : decode_any W_13e6c = Some (Store SZ4 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e70 : bv 32 := 0x01252223.
Lemma F_13e70 : fetch_word Plain.M.loaded_segments (0x13f6c : word) = Some W_13e70.
Proof. vm_refl. Qed.
Lemma D_13e70 : decode_any W_13e70 = Some (Store SZ4 10 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e74 : bv 32 := 0x01452423.
Lemma F_13e74 : fetch_word Plain.M.loaded_segments (0x13f70 : word) = Some W_13e74.
Proof. vm_refl. Qed.
Lemma D_13e74 : decode_any W_13e74 = Some (Store SZ4 10 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e78 : bv 32 := 0x00852823.
Lemma F_13e78 : fetch_word Plain.M.loaded_segments (0x13f74 : word) = Some W_13e78.
Proof. vm_refl. Qed.
Lemma D_13e78 : decode_any W_13e78 = Some (Store SZ4 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e7c : bv 32 := 0x02058a63.
Lemma F_13e7c : fetch_word Plain.M.loaded_segments (0x13f78 : word) = Some W_13e7c.
Proof. vm_refl. Qed.
Lemma D_13e7c : decode_any W_13e7c = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e80 : bv 32 := 0x00100593.
Lemma F_13e80 : fetch_word Plain.M.loaded_segments (0x13f7c : word) = Some W_13e80.
Proof. vm_refl. Qed.
Lemma D_13e80 : decode_any W_13e80 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e84 : bv 32 := 0x0300006f.
Lemma F_13e84 : fetch_word Plain.M.loaded_segments (0x13f80 : word) = Some W_13e84.
Proof. vm_refl. Qed.
Lemma D_13e84 : decode_any W_13e84 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e88 : bv 32 := 0x0000b517.
Lemma F_13e88 : fetch_word Plain.M.loaded_segments (0x13f84 : word) = Some W_13e88.
Proof. vm_refl. Qed.
Lemma D_13e88 : decode_any W_13e88 = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e8c : bv 32 := 0x1cc53503.
Lemma F_13e8c : fetch_word Plain.M.loaded_segments (0x13f88 : word) = Some W_13e8c.
Proof. vm_refl. Qed.
Lemma D_13e8c : decode_any W_13e8c = Some (Load SZ8 true 10 10 460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e90 : bv 32 := 0x00052503.
Lemma F_13e90 : fetch_word Plain.M.loaded_segments (0x13f8c : word) = Some W_13e90.
Proof. vm_refl. Qed.
Lemma D_13e90 : decode_any W_13e90 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e94 : bv 32 := 0x00500593.
Lemma F_13e94 : fetch_word Plain.M.loaded_segments (0x13f90 : word) = Some W_13e94.
Proof. vm_refl. Qed.
Lemma D_13e94 : decode_any W_13e94 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e98 : bv 32 := 0xf8a5c4e3.
Lemma F_13e98 : fetch_word Plain.M.loaded_segments (0x13f94 : word) = Some W_13e98.
Proof. vm_refl. Qed.
Lemma D_13e98 : decode_any W_13e98 = Some (Branch BC_LT 11 10 8072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e9c : bv 32 := 0xffffc517.
Lemma F_13e9c : fetch_word Plain.M.loaded_segments (0x13f98 : word) = Some W_13e9c.
Proof. vm_refl. Qed.
Lemma D_13e9c : decode_any W_13e9c = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ea0 : bv 32 := 0xffffc597.
Lemma F_13ea0 : fetch_word Plain.M.loaded_segments (0x13f9c : word) = Some W_13ea0.
Proof. vm_refl. Qed.
Lemma D_13ea0 : decode_any W_13ea0 = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ea4 : bv 32 := 0x46050513.
Lemma F_13ea4 : fetch_word Plain.M.loaded_segments (0x13fa0 : word) = Some W_13ea4.
Proof. vm_refl. Qed.
Lemma D_13ea4 : decode_any W_13ea4 = Some (OpImm ALU_ADD 10 10 1120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ea8 : bv 32 := 0x64b58593.
Lemma F_13ea8 : fetch_word Plain.M.loaded_segments (0x13fa4 : word) = Some W_13ea8.
Proof. vm_refl. Qed.
Lemma D_13ea8 : decode_any W_13ea8 = Some (OpImm ALU_ADD 11 11 1611, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13eac : bv 32 := 0xebdff06f.
Lemma F_13eac : fetch_word Plain.M.loaded_segments (0x13fa8 : word) = Some W_13eac.
Proof. vm_refl. Qed.
Lemma D_13eac : decode_any W_13eac = Some (Jal 0 2096828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13eb0 : bv 32 := 0x00300593.
Lemma F_13eb0 : fetch_word Plain.M.loaded_segments (0x13fac : word) = Some W_13eb0.
Proof. vm_refl. Qed.
Lemma D_13eb0 : decode_any W_13eb0 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13eb4 : bv 32 := 0x00b52623.
Lemma F_13eb4 : fetch_word Plain.M.loaded_segments (0x13fb0 : word) = Some W_13eb4.
Proof. vm_refl. Qed.
Lemma D_13eb4 : decode_any W_13eb4 = Some (Store SZ4 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13eb8 : bv 32 := 0x0310000f.
Lemma F_13eb8 : fetch_word Plain.M.loaded_segments (0x13fb4 : word) = Some W_13eb8.
Proof. vm_refl. Qed.
Lemma D_13eb8 : decode_any W_13eb8 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ebc : bv 32 := 0x00952a23.
Lemma F_13ebc : fetch_word Plain.M.loaded_segments (0x13fb8 : word) = Some W_13ebc.
Proof. vm_refl. Qed.
Lemma D_13ebc : decode_any W_13ebc = Some (Store SZ4 10 9 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ec0 : bv 32 := 0x0330000f.
Lemma F_13ec0 : fetch_word Plain.M.loaded_segments (0x13fbc : word) = Some W_13ec0.
Proof. vm_refl. Qed.
Lemma D_13ec0 : decode_any W_13ec0 = Some (Fence 0 3 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ec4 : bv 32 := 0x02052023.
Lemma F_13ec4 : fetch_word Plain.M.loaded_segments (0x13fc0 : word) = Some W_13ec4.
Proof. vm_refl. Qed.
Lemma D_13ec4 : decode_any W_13ec4 = Some (Store SZ4 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ec8 : bv 32 := 0xf5dff06f.
Lemma F_13ec8 : fetch_word Plain.M.loaded_segments (0x13fc4 : word) = Some W_13ec8.
Proof. vm_refl. Qed.
Lemma D_13ec8 : decode_any W_13ec8 = Some (Jal 0 2096988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ecc : bv 32 := 0x00050663.
Lemma F_13ecc : fetch_word Plain.M.loaded_segments (0x13fc8 : word) = Some W_13ecc.
Proof. vm_refl. Qed.
Lemma D_13ecc : decode_any W_13ecc = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ed0 : bv 32 := 0x01052503.
Lemma F_13ed0 : fetch_word Plain.M.loaded_segments (0x13fcc : word) = Some W_13ed0.
Proof. vm_refl. Qed.
Lemma D_13ed0 : decode_any W_13ed0 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ed4 : bv 32 := 0x00008067.
Lemma F_13ed4 : fetch_word Plain.M.loaded_segments (0x13fd0 : word) = Some W_13ed4.
Proof. vm_refl. Qed.
Lemma D_13ed4 : decode_any W_13ed4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f0c : bv 32 := 0xfe010113.
Lemma F_13f0c : fetch_word Plain.M.loaded_segments (0x14008 : word) = Some W_13f0c.
Proof. vm_refl. Qed.
Lemma D_13f0c : decode_any W_13f0c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f10 : bv 32 := 0x00113c23.
Lemma F_13f10 : fetch_word Plain.M.loaded_segments (0x1400c : word) = Some W_13f10.
Proof. vm_refl. Qed.
Lemma D_13f10 : decode_any W_13f10 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f14 : bv 32 := 0x00813823.
Lemma F_13f14 : fetch_word Plain.M.loaded_segments (0x14010 : word) = Some W_13f14.
Proof. vm_refl. Qed.
Lemma D_13f14 : decode_any W_13f14 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f18 : bv 32 := 0x00913423.
Lemma F_13f18 : fetch_word Plain.M.loaded_segments (0x14014 : word) = Some W_13f18.
Proof. vm_refl. Qed.
Lemma D_13f18 : decode_any W_13f18 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f1c : bv 32 := 0x06050863.
Lemma F_13f1c : fetch_word Plain.M.loaded_segments (0x14018 : word) = Some W_13f1c.
Proof. vm_refl. Qed.
Lemma D_13f1c : decode_any W_13f1c = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f20 : bv 32 := 0x00053403.
Lemma F_13f20 : fetch_word Plain.M.loaded_segments (0x1401c : word) = Some W_13f20.
Proof. vm_refl. Qed.
Lemma D_13f20 : decode_any W_13f20 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f24 : bv 32 := 0x0a040063.
Lemma F_13f24 : fetch_word Plain.M.loaded_segments (0x14020 : word) = Some W_13f24.
Proof. vm_refl. Qed.
Lemma D_13f24 : decode_any W_13f24 = Some (Branch BC_EQ 8 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f28 : bv 32 := 0x01440593.
Lemma F_13f28 : fetch_word Plain.M.loaded_segments (0x14024 : word) = Some W_13f28.
Proof. vm_refl. Qed.
Lemma D_13f28 : decode_any W_13f28 = Some (OpImm ALU_ADD 11 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f2c : bv 32 := 0xfff00613.
Lemma F_13f2c : fetch_word Plain.M.loaded_segments (0x14028 : word) = Some W_13f2c.
Proof. vm_refl. Qed.
Lemma D_13f2c : decode_any W_13f2c = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f30 : bv 32 := 0x06c5a5af.
Lemma F_13f30 : fetch_word Plain.M.loaded_segments (0x1402c : word) = Some W_13f30.
Proof. vm_refl. Qed.
Lemma D_13f30 : decode_any W_13f30 = Some (Amo AMO_ADD AW true true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f34 : bv 32 := 0x00100613.
Lemma F_13f34 : fetch_word Plain.M.loaded_segments (0x14030 : word) = Some W_13f34.
Proof. vm_refl. Qed.
Lemma D_13f34 : decode_any W_13f34 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f38 : bv 32 := 0x04c59663.
Lemma F_13f38 : fetch_word Plain.M.loaded_segments (0x14034 : word) = Some W_13f38.
Proof. vm_refl. Qed.
Lemma D_13f38 : decode_any W_13f38 = Some (Branch BC_NE 11 12 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f3c : bv 32 := 0x00050493.
Lemma F_13f3c : fetch_word Plain.M.loaded_segments (0x14038 : word) = Some W_13f3c.
Proof. vm_refl. Qed.
Lemma D_13f3c : decode_any W_13f3c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f40 : bv 32 := 0x03843503.
Lemma F_13f40 : fetch_word Plain.M.loaded_segments (0x1403c : word) = Some W_13f40.
Proof. vm_refl. Qed.
Lemma D_13f40 : decode_any W_13f40 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f44 : bv 32 := 0x00050863.
Lemma F_13f44 : fetch_word Plain.M.loaded_segments (0x14040 : word) = Some W_13f44.
Proof. vm_refl. Qed.
Lemma D_13f44 : decode_any W_13f44 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f48 : bv 32 := 0x0000c597.
Lemma F_13f48 : fetch_word Plain.M.loaded_segments (0x14044 : word) = Some W_13f48.
Proof. vm_refl. Qed.
Lemma D_13f48 : decode_any W_13f48 = Some (Auipc 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f4c : bv 32 := 0x1945b583.
Lemma F_13f4c : fetch_word Plain.M.loaded_segments (0x14048 : word) = Some W_13f4c.
Proof. vm_refl. Qed.
Lemma D_13f4c : decode_any W_13f4c = Some (Load SZ8 true 11 11 404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f50 : bv 32 := 0x000580e7.
Lemma F_13f50 : fetch_word Plain.M.loaded_segments (0x1404c : word) = Some W_13f50.
Proof. vm_refl. Qed.
Lemma D_13f50 : decode_any W_13f50 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f54 : bv 32 := 0x02843503.
Lemma F_13f54 : fetch_word Plain.M.loaded_segments (0x14050 : word) = Some W_13f54.
Proof. vm_refl. Qed.
Lemma D_13f54 : decode_any W_13f54 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f58 : bv 32 := 0x00050463.
Lemma F_13f58 : fetch_word Plain.M.loaded_segments (0x14054 : word) = Some W_13f58.
Proof. vm_refl. Qed.
Lemma D_13f58 : decode_any W_13f58 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f60 : bv 32 := 0x03043503.
Lemma F_13f60 : fetch_word Plain.M.loaded_segments (0x1405c : word) = Some W_13f60.
Proof. vm_refl. Qed.
Lemma D_13f60 : decode_any W_13f60 = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f64 : bv 32 := 0x00a13023.
Lemma F_13f64 : fetch_word Plain.M.loaded_segments (0x14060 : word) = Some W_13f64.
Proof. vm_refl. Qed.
Lemma D_13f64 : decode_any W_13f64 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f68 : bv 32 := 0x00050863.
Lemma F_13f68 : fetch_word Plain.M.loaded_segments (0x14064 : word) = Some W_13f68.
Proof. vm_refl. Qed.
Lemma D_13f68 : decode_any W_13f68 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f6c : bv 32 := 0x00010513.
Lemma F_13f6c : fetch_word Plain.M.loaded_segments (0x14068 : word) = Some W_13f6c.
Proof. vm_refl. Qed.
Lemma D_13f6c : decode_any W_13f6c = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f70 : bv 32 := 0x15d000ef.
Lemma F_13f70 : fetch_word Plain.M.loaded_segments (0x1406c : word) = Some W_13f70.
Proof. vm_refl. Qed.
Lemma D_13f70 : decode_any W_13f70 = Some (Jal 1 2396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f74 : bv 32 := 0x02043823.
Lemma F_13f74 : fetch_word Plain.M.loaded_segments (0x14070 : word) = Some W_13f74.
Proof. vm_refl. Qed.
Lemma D_13f74 : decode_any W_13f74 = Some (Store SZ8 8 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f78 : bv 32 := 0x00040513.
Lemma F_13f78 : fetch_word Plain.M.loaded_segments (0x14074 : word) = Some W_13f78.
Proof. vm_refl. Qed.
Lemma D_13f78 : decode_any W_13f78 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f7c : bv 32 := 0x58c020ef.
Lemma F_13f7c : fetch_word Plain.M.loaded_segments (0x14078 : word) = Some W_13f7c.
Proof. vm_refl. Qed.
Lemma D_13f7c : decode_any W_13f7c = Some (Jal 1 9612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f80 : bv 32 := 0x00048513.
Lemma F_13f80 : fetch_word Plain.M.loaded_segments (0x1407c : word) = Some W_13f80.
Proof. vm_refl. Qed.
Lemma D_13f80 : decode_any W_13f80 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f84 : bv 32 := 0x00053023.
Lemma F_13f84 : fetch_word Plain.M.loaded_segments (0x14080 : word) = Some W_13f84.
Proof. vm_refl. Qed.
Lemma D_13f84 : decode_any W_13f84 = Some (Store SZ8 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f88 : bv 32 := 0x03c0006f.
Lemma F_13f88 : fetch_word Plain.M.loaded_segments (0x14084 : word) = Some W_13f88.
Proof. vm_refl. Qed.
Lemma D_13f88 : decode_any W_13f88 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fc4 : bv 32 := 0x01813083.
Lemma F_13fc4 : fetch_word Plain.M.loaded_segments (0x140c0 : word) = Some W_13fc4.
Proof. vm_refl. Qed.
Lemma D_13fc4 : decode_any W_13fc4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fc8 : bv 32 := 0x01013403.
Lemma F_13fc8 : fetch_word Plain.M.loaded_segments (0x140c4 : word) = Some W_13fc8.
Proof. vm_refl. Qed.
Lemma D_13fc8 : decode_any W_13fc8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fcc : bv 32 := 0x00813483.
Lemma F_13fcc : fetch_word Plain.M.loaded_segments (0x140c8 : word) = Some W_13fcc.
Proof. vm_refl. Qed.
Lemma D_13fcc : decode_any W_13fcc = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fd0 : bv 32 := 0x02010113.
Lemma F_13fd0 : fetch_word Plain.M.loaded_segments (0x140cc : word) = Some W_13fd0.
Proof. vm_refl. Qed.
Lemma D_13fd0 : decode_any W_13fd0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fd4 : bv 32 := 0x00008067.
Lemma F_13fd4 : fetch_word Plain.M.loaded_segments (0x140d0 : word) = Some W_13fd4.
Proof. vm_refl. Qed.
Lemma D_13fd4 : decode_any W_13fd4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fd8 : bv 32 := 0x00058463.
Lemma F_13fd8 : fetch_word Plain.M.loaded_segments (0x140d4 : word) = Some W_13fd8.
Proof. vm_refl. Qed.
Lemma D_13fd8 : decode_any W_13fd8 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fdc : bv 32 := 0x0005a023.
Lemma F_13fdc : fetch_word Plain.M.loaded_segments (0x140d8 : word) = Some W_13fdc.
Proof. vm_refl. Qed.
Lemma D_13fdc : decode_any W_13fdc = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fe0 : bv 32 := 0x00060463.
Lemma F_13fe0 : fetch_word Plain.M.loaded_segments (0x140dc : word) = Some W_13fe0.
Proof. vm_refl. Qed.
Lemma D_13fe0 : decode_any W_13fe0 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fe4 : bv 32 := 0x00062023.
Lemma F_13fe4 : fetch_word Plain.M.loaded_segments (0x140e0 : word) = Some W_13fe4.
Proof. vm_refl. Qed.
Lemma D_13fe4 : decode_any W_13fe4 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fe8 : bv 32 := 0x00068463.
Lemma F_13fe8 : fetch_word Plain.M.loaded_segments (0x140e4 : word) = Some W_13fe8.
Proof. vm_refl. Qed.
Lemma D_13fe8 : decode_any W_13fe8 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fec : bv 32 := 0x0006a023.
Lemma F_13fec : fetch_word Plain.M.loaded_segments (0x140e8 : word) = Some W_13fec.
Proof. vm_refl. Qed.
Lemma D_13fec : decode_any W_13fec = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ff0 : bv 32 := 0x02050a63.
Lemma F_13ff0 : fetch_word Plain.M.loaded_segments (0x140ec : word) = Some W_13ff0.
Proof. vm_refl. Qed.
Lemma D_13ff0 : decode_any W_13ff0 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ff4 : bv 32 := 0x00058663.
Lemma F_13ff4 : fetch_word Plain.M.loaded_segments (0x140f0 : word) = Some W_13ff4.
Proof. vm_refl. Qed.
Lemma D_13ff4 : decode_any W_13ff4 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ff8 : bv 32 := 0x00052703.
Lemma F_13ff8 : fetch_word Plain.M.loaded_segments (0x140f4 : word) = Some W_13ff8.
Proof. vm_refl. Qed.
Lemma D_13ff8 : decode_any W_13ff8 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ffc : bv 32 := 0x00e5a023.
Lemma F_13ffc : fetch_word Plain.M.loaded_segments (0x140f8 : word) = Some W_13ffc.
Proof. vm_refl. Qed.
Lemma D_13ffc : decode_any W_13ffc = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.
