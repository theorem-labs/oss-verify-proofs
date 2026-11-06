(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_63038 : bv 32 := 0x81010113.
Lemma F_63038 : fetch_word Asan.M.loaded_segments (0x63088 : word) = Some W_63038.
Proof. vm_refl. Qed.
Lemma D_63038 : decode_any W_63038 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6303c : bv 32 := 0x7e113423.
Lemma F_6303c : fetch_word Asan.M.loaded_segments (0x6308c : word) = Some W_6303c.
Proof. vm_refl. Qed.
Lemma D_6303c : decode_any W_6303c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63040 : bv 32 := 0x7e813023.
Lemma F_63040 : fetch_word Asan.M.loaded_segments (0x63090 : word) = Some W_63040.
Proof. vm_refl. Qed.
Lemma D_63040 : decode_any W_63040 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63044 : bv 32 := 0x7c913c23.
Lemma F_63044 : fetch_word Asan.M.loaded_segments (0x63094 : word) = Some W_63044.
Proof. vm_refl. Qed.
Lemma D_63044 : decode_any W_63044 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63048 : bv 32 := 0x7d213823.
Lemma F_63048 : fetch_word Asan.M.loaded_segments (0x63098 : word) = Some W_63048.
Proof. vm_refl. Qed.
Lemma D_63048 : decode_any W_63048 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6304c : bv 32 := 0x7d313423.
Lemma F_6304c : fetch_word Asan.M.loaded_segments (0x6309c : word) = Some W_6304c.
Proof. vm_refl. Qed.
Lemma D_6304c : decode_any W_6304c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63050 : bv 32 := 0x7d413023.
Lemma F_63050 : fetch_word Asan.M.loaded_segments (0x630a0 : word) = Some W_63050.
Proof. vm_refl. Qed.
Lemma D_63050 : decode_any W_63050 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63054 : bv 32 := 0x7b513c23.
Lemma F_63054 : fetch_word Asan.M.loaded_segments (0x630a4 : word) = Some W_63054.
Proof. vm_refl. Qed.
Lemma D_63054 : decode_any W_63054 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63058 : bv 32 := 0x7b613823.
Lemma F_63058 : fetch_word Asan.M.loaded_segments (0x630a8 : word) = Some W_63058.
Proof. vm_refl. Qed.
Lemma D_63058 : decode_any W_63058 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6305c : bv 32 := 0x7f010413.
Lemma F_6305c : fetch_word Asan.M.loaded_segments (0x630ac : word) = Some W_6305c.
Proof. vm_refl. Qed.
Lemma D_6305c : decode_any W_6305c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63060 : bv 32 := 0xf9010113.
Lemma F_63060 : fetch_word Asan.M.loaded_segments (0x630b0 : word) = Some W_63060.
Proof. vm_refl. Qed.
Lemma D_63060 : decode_any W_63060 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63064 : bv 32 := 0x00050913.
Lemma F_63064 : fetch_word Asan.M.loaded_segments (0x630b4 : word) = Some W_63064.
Proof. vm_refl. Qed.
Lemma D_63064 : decode_any W_63064 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63068 : bv 32 := 0x5551c0ef.
Lemma F_63068 : fetch_word Asan.M.loaded_segments (0x630b8 : word) = Some W_63068.
Proof. vm_refl. Qed.
Lemma D_63068 : decode_any W_63068 = Some (Jal 1 118100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6306c : bv 32 := 0x0a050863.
Lemma F_6306c : fetch_word Asan.M.loaded_segments (0x630bc : word) = Some W_6306c.
Proof. vm_refl. Qed.
Lemma D_6306c : decode_any W_6306c = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63070 : bv 32 := 0x45d1d0ef.
Lemma F_63070 : fetch_word Asan.M.loaded_segments (0x630c0 : word) = Some W_63070.
Proof. vm_refl. Qed.
Lemma D_63070 : decode_any W_63070 = Some (Jal 1 121948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63074 : bv 32 := 0x000d4597.
Lemma F_63074 : fetch_word Asan.M.loaded_segments (0x630c4 : word) = Some W_63074.
Proof. vm_refl. Qed.
Lemma D_63074 : decode_any W_63074 = Some (Auipc 11 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63078 : bv 32 := 0xd2c5b583.
Lemma F_63078 : fetch_word Asan.M.loaded_segments (0x630c8 : word) = Some W_63078.
Proof. vm_refl. Qed.
Lemma D_63078 : decode_any W_63078 = Some (Load SZ8 true 11 11 3372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6307c : bv 32 := 0x00050493.
Lemma F_6307c : fetch_word Asan.M.loaded_segments (0x630cc : word) = Some W_6307c.
Proof. vm_refl. Qed.
Lemma D_6307c : decode_any W_6307c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63080 : bv 32 := 0x00090513.
Lemma F_63080 : fetch_word Asan.M.loaded_segments (0x630d0 : word) = Some W_63080.
Proof. vm_refl. Qed.
Lemma D_63080 : decode_any W_63080 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63084 : bv 32 := 0x000580e7.
Lemma F_63084 : fetch_word Asan.M.loaded_segments (0x630d4 : word) = Some W_63084.
Proof. vm_refl. Qed.
Lemma D_63084 : decode_any W_63084 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63088 : bv 32 := 0x06048463.
Lemma F_63088 : fetch_word Asan.M.loaded_segments (0x630d8 : word) = Some W_63088.
Proof. vm_refl. Qed.
Lemma D_63088 : decode_any W_63088 = Some (Branch BC_EQ 9 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6308c : bv 32 := 0x000d2597.
Lemma F_6308c : fetch_word Asan.M.loaded_segments (0x630dc : word) = Some W_6308c.
Proof. vm_refl. Qed.
Lemma D_6308c : decode_any W_6308c = Some (Auipc 11 210, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63090 : bv 32 := 0xeec5b983.
Lemma F_63090 : fetch_word Asan.M.loaded_segments (0x630e0 : word) = Some W_63090.
Proof. vm_refl. Qed.
Lemma D_63090 : decode_any W_63090 = Some (Load SZ8 true 19 11 3820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63094 : bv 32 := 0x0fb9c583.
Lemma F_63094 : fetch_word Asan.M.loaded_segments (0x630e4 : word) = Some W_63094.
Proof. vm_refl. Qed.
Lemma D_63094 : decode_any W_63094 = Some (Load SZ1 false 11 19 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63098 : bv 32 := 0x04058c63.
Lemma F_63098 : fetch_word Asan.M.loaded_segments (0x630e8 : word) = Some W_63098.
Proof. vm_refl. Qed.
Lemma D_63098 : decode_any W_63098 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6309c : bv 32 := 0x00150493.
Lemma F_6309c : fetch_word Asan.M.loaded_segments (0x630ec : word) = Some W_6309c.
Proof. vm_refl. Qed.
Lemma D_6309c : decode_any W_6309c = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630a0 : bv 32 := 0xfff94593.
Lemma F_630a0 : fetch_word Asan.M.loaded_segments (0x630f0 : word) = Some W_630a0.
Proof. vm_refl. Qed.
Lemma D_630a0 : decode_any W_630a0 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630a4 : bv 32 := 0x80040a13.
Lemma F_630a4 : fetch_word Asan.M.loaded_segments (0x630f4 : word) = Some W_630a4.
Proof. vm_refl. Qed.
Lemma D_630a4 : decode_any W_630a4 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630a8 : bv 32 := 0xfa8a0a13.
Lemma F_630a8 : fetch_word Asan.M.loaded_segments (0x630f8 : word) = Some W_630a8.
Proof. vm_refl. Qed.
Lemma D_630a8 : decode_any W_630a8 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630ac : bv 32 := 0x0a95e063.
Lemma F_630ac : fetch_word Asan.M.loaded_segments (0x630fc : word) = Some W_630ac.
Proof. vm_refl. Qed.
Lemma D_630ac : decode_any W_630ac = Some (Branch BC_LTU 11 9 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630b0 : bv 32 := 0x04000593.
Lemma F_630b0 : fetch_word Asan.M.loaded_segments (0x63100 : word) = Some W_630b0.
Proof. vm_refl. Qed.
Lemma D_630b0 : decode_any W_630b0 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630b4 : bv 32 := 0x10b57263.
Lemma F_630b4 : fetch_word Asan.M.loaded_segments (0x63104 : word) = Some W_630b4.
Proof. vm_refl. Qed.
Lemma D_630b4 : decode_any W_630b4 = Some (Branch BC_GEU 10 11 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630b8 : bv 32 := 0x000d2597.
Lemma F_630b8 : fetch_word Asan.M.loaded_segments (0x63108 : word) = Some W_630b8.
Proof. vm_refl. Qed.
Lemma D_630b8 : decode_any W_630b8 = Some (Auipc 11 210, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630bc : bv 32 := 0xed05b583.
Lemma F_630bc : fetch_word Asan.M.loaded_segments (0x6310c : word) = Some W_630bc.
Proof. vm_refl. Qed.
Lemma D_630bc : decode_any W_630bc = Some (Load SZ8 true 11 11 3792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630c0 : bv 32 := 0x0005b603.
Lemma F_630c0 : fetch_word Asan.M.loaded_segments (0x63110 : word) = Some W_630c0.
Proof. vm_refl. Qed.
Lemma D_630c0 : decode_any W_630c0 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630c4 : bv 32 := 0x012506b3.
Lemma F_630c4 : fetch_word Asan.M.loaded_segments (0x63114 : word) = Some W_630c4.
Proof. vm_refl. Qed.
Lemma D_630c4 : decode_any W_630c4 = Some (Op ALU_ADD 13 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630c8 : bv 32 := 0x00395593.
Lemma F_630c8 : fetch_word Asan.M.loaded_segments (0x63118 : word) = Some W_630c8.
Proof. vm_refl. Qed.
Lemma D_630c8 : decode_any W_630c8 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630cc : bv 32 := 0x0036d713.
Lemma F_630cc : fetch_word Asan.M.loaded_segments (0x6311c : word) = Some W_630cc.
Proof. vm_refl. Qed.
Lemma D_630cc : decode_any W_630cc = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630d0 : bv 32 := 0x00b605b3.
Lemma F_630d0 : fetch_word Asan.M.loaded_segments (0x63120 : word) = Some W_630d0.
Proof. vm_refl. Qed.
Lemma D_630d0 : decode_any W_630d0 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630d4 : bv 32 := 0x00e60633.
Lemma F_630d4 : fetch_word Asan.M.loaded_segments (0x63124 : word) = Some W_630d4.
Proof. vm_refl. Qed.
Lemma D_630d4 : decode_any W_630d4 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630d8 : bv 32 := 0xff85f713.
Lemma F_630d8 : fetch_word Asan.M.loaded_segments (0x63128 : word) = Some W_630d8.
Proof. vm_refl. Qed.
Lemma D_630d8 : decode_any W_630d8 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630dc : bv 32 := 0xff867793.
Lemma F_630dc : fetch_word Asan.M.loaded_segments (0x6312c : word) = Some W_630dc.
Proof. vm_refl. Qed.
Lemma D_630dc : decode_any W_630dc = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630e0 : bv 32 := 0x00073703.
Lemma F_630e0 : fetch_word Asan.M.loaded_segments (0x63130 : word) = Some W_630e0.
Proof. vm_refl. Qed.
Lemma D_630e0 : decode_any W_630e0 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630e4 : bv 32 := 0x0007b783.
Lemma F_630e4 : fetch_word Asan.M.loaded_segments (0x63134 : word) = Some W_630e4.
Proof. vm_refl. Qed.
Lemma D_630e4 : decode_any W_630e4 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630e8 : bv 32 := 0x00e7e733.
Lemma F_630e8 : fetch_word Asan.M.loaded_segments (0x63138 : word) = Some W_630e8.
Proof. vm_refl. Qed.
Lemma D_630e8 : decode_any W_630e8 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630ec : bv 32 := 0x0c071e63.
Lemma F_630ec : fetch_word Asan.M.loaded_segments (0x6313c : word) = Some W_630ec.
Proof. vm_refl. Qed.
Lemma D_630ec : decode_any W_630ec = Some (Branch BC_NE 14 0 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630f0 : bv 32 := 0x07010113.
Lemma F_630f0 : fetch_word Asan.M.loaded_segments (0x63140 : word) = Some W_630f0.
Proof. vm_refl. Qed.
Lemma D_630f0 : decode_any W_630f0 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630f4 : bv 32 := 0x7e813083.
Lemma F_630f4 : fetch_word Asan.M.loaded_segments (0x63144 : word) = Some W_630f4.
Proof. vm_refl. Qed.
Lemma D_630f4 : decode_any W_630f4 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630f8 : bv 32 := 0x7e013403.
Lemma F_630f8 : fetch_word Asan.M.loaded_segments (0x63148 : word) = Some W_630f8.
Proof. vm_refl. Qed.
Lemma D_630f8 : decode_any W_630f8 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630fc : bv 32 := 0x7d813483.
Lemma F_630fc : fetch_word Asan.M.loaded_segments (0x6314c : word) = Some W_630fc.
Proof. vm_refl. Qed.
Lemma D_630fc : decode_any W_630fc = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63100 : bv 32 := 0x7d013903.
Lemma F_63100 : fetch_word Asan.M.loaded_segments (0x63150 : word) = Some W_63100.
Proof. vm_refl. Qed.
Lemma D_63100 : decode_any W_63100 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63104 : bv 32 := 0x7c813983.
Lemma F_63104 : fetch_word Asan.M.loaded_segments (0x63154 : word) = Some W_63104.
Proof. vm_refl. Qed.
Lemma D_63104 : decode_any W_63104 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63108 : bv 32 := 0x7c013a03.
Lemma F_63108 : fetch_word Asan.M.loaded_segments (0x63158 : word) = Some W_63108.
Proof. vm_refl. Qed.
Lemma D_63108 : decode_any W_63108 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6310c : bv 32 := 0x7b813a83.
Lemma F_6310c : fetch_word Asan.M.loaded_segments (0x6315c : word) = Some W_6310c.
Proof. vm_refl. Qed.
Lemma D_6310c : decode_any W_6310c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63110 : bv 32 := 0x7b013b03.
Lemma F_63110 : fetch_word Asan.M.loaded_segments (0x63160 : word) = Some W_63110.
Proof. vm_refl. Qed.
Lemma D_63110 : decode_any W_63110 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63114 : bv 32 := 0x7f010113.
Lemma F_63114 : fetch_word Asan.M.loaded_segments (0x63164 : word) = Some W_63114.
Proof. vm_refl. Qed.
Lemma D_63114 : decode_any W_63114 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63118 : bv 32 := 0x00008067.
Lemma F_63118 : fetch_word Asan.M.loaded_segments (0x63168 : word) = Some W_63118.
Proof. vm_refl. Qed.
Lemma D_63118 : decode_any W_63118 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631b8 : bv 32 := 0x00050a93.
Lemma F_631b8 : fetch_word Asan.M.loaded_segments (0x63208 : word) = Some W_631b8.
Proof. vm_refl. Qed.
Lemma D_631b8 : decode_any W_631b8 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631bc : bv 32 := 0x04049263.
Lemma F_631bc : fetch_word Asan.M.loaded_segments (0x6320c : word) = Some W_631bc.
Proof. vm_refl. Qed.
Lemma D_631bc : decode_any W_631bc = Some (Branch BC_NE 9 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631c8 : bv 32 := 0x00050a93.
Lemma F_631c8 : fetch_word Asan.M.loaded_segments (0x63218 : word) = Some W_631c8.
Proof. vm_refl. Qed.
Lemma D_631c8 : decode_any W_631c8 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631cc : bv 32 := 0x00060503.
Lemma F_631cc : fetch_word Asan.M.loaded_segments (0x6321c : word) = Some W_631cc.
Proof. vm_refl. Qed.
Lemma D_631cc : decode_any W_631cc = Some (Load SZ1 true 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631d0 : bv 32 := 0x0076f693.
Lemma F_631d0 : fetch_word Asan.M.loaded_segments (0x63220 : word) = Some W_631d0.
Proof. vm_refl. Qed.
Lemma D_631d0 : decode_any W_631d0 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631d4 : bv 32 := 0x00a03733.
Lemma F_631d4 : fetch_word Asan.M.loaded_segments (0x63224 : word) = Some W_631d4.
Proof. vm_refl. Qed.
Lemma D_631d4 : decode_any W_631d4 = Some (Op ALU_SLTU 14 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631d8 : bv 32 := 0x00a6a533.
Lemma F_631d8 : fetch_word Asan.M.loaded_segments (0x63228 : word) = Some W_631d8.
Proof. vm_refl. Qed.
Lemma D_631d8 : decode_any W_631d8 = Some (Op ALU_SLT 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631dc : bv 32 := 0x00154513.
Lemma F_631dc : fetch_word Asan.M.loaded_segments (0x6322c : word) = Some W_631dc.
Proof. vm_refl. Qed.
Lemma D_631dc : decode_any W_631dc = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631e0 : bv 32 := 0x00a77533.
Lemma F_631e0 : fetch_word Asan.M.loaded_segments (0x63230 : word) = Some W_631e0.
Proof. vm_refl. Qed.
Lemma D_631e0 : decode_any W_631e0 = Some (Op ALU_AND 10 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631e4 : bv 32 := 0x00c5fa63.
Lemma F_631e4 : fetch_word Asan.M.loaded_segments (0x63234 : word) = Some W_631e4.
Proof. vm_refl. Qed.
Lemma D_631e4 : decode_any W_631e4 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631e8 : bv 32 := 0x0005c683.
Lemma F_631e8 : fetch_word Asan.M.loaded_segments (0x63238 : word) = Some W_631e8.
Proof. vm_refl. Qed.
Lemma D_631e8 : decode_any W_631e8 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631ec : bv 32 := 0x00158593.
Lemma F_631ec : fetch_word Asan.M.loaded_segments (0x6323c : word) = Some W_631ec.
Proof. vm_refl. Qed.
Lemma D_631ec : decode_any W_631ec = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631f0 : bv 32 := 0x00a6e533.
Lemma F_631f0 : fetch_word Asan.M.loaded_segments (0x63240 : word) = Some W_631f0.
Proof. vm_refl. Qed.
Lemma D_631f0 : decode_any W_631f0 = Some (Op ALU_OR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631f4 : bv 32 := 0xfec59ae3.
Lemma F_631f4 : fetch_word Asan.M.loaded_segments (0x63244 : word) = Some W_631f4.
Proof. vm_refl. Qed.
Lemma D_631f4 : decode_any W_631f4 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631f8 : bv 32 := 0x0ff57513.
Lemma F_631f8 : fetch_word Asan.M.loaded_segments (0x63248 : word) = Some W_631f8.
Proof. vm_refl. Qed.
Lemma D_631f8 : decode_any W_631f8 = Some (OpImm ALU_AND 10 10 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631fc : bv 32 := 0x0c050463.
Lemma F_631fc : fetch_word Asan.M.loaded_segments (0x6324c : word) = Some W_631fc.
Proof. vm_refl. Qed.
Lemma D_631fc : decode_any W_631fc = Some (Branch BC_EQ 10 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63200 : bv 32 := 0x00090513.
Lemma F_63200 : fetch_word Asan.M.loaded_segments (0x63250 : word) = Some W_63200.
Proof. vm_refl. Qed.
Lemma D_63200 : decode_any W_63200 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63204 : bv 32 := 0x00048593.
Lemma F_63204 : fetch_word Asan.M.loaded_segments (0x63254 : word) = Some W_63204.
Proof. vm_refl. Qed.
Lemma D_63204 : decode_any W_63204 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63208 : bv 32 := 0x6a1170ef.
Lemma F_63208 : fetch_word Asan.M.loaded_segments (0x63258 : word) = Some W_63208.
Proof. vm_refl. Qed.
Lemma D_63208 : decode_any W_63208 = Some (Jal 1 97952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6320c : bv 32 := 0x0a050c63.
Lemma F_6320c : fetch_word Asan.M.loaded_segments (0x6325c : word) = Some W_6320c.
Proof. vm_refl. Qed.
Lemma D_6320c : decode_any W_6320c = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632c4 : bv 32 := 0x000a8513.
Lemma F_632c4 : fetch_word Asan.M.loaded_segments (0x63314 : word) = Some W_632c4.
Proof. vm_refl. Qed.
Lemma D_632c4 : decode_any W_632c4 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632c8 : bv 32 := 0xe29ff06f.
Lemma F_632c8 : fetch_word Asan.M.loaded_segments (0x63318 : word) = Some W_632c8.
Proof. vm_refl. Qed.
Lemma D_632c8 : decode_any W_632c8 = Some (Jal 0 2096680, 4%Z).
Proof. vm_refl. Qed.
