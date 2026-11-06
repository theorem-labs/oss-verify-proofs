(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6d5dc : bv 32 := 0x060a0063.
Lemma F_6d5dc : fetch_word Asan.M.loaded_segments (0x6d62c : word) = Some W_6d5dc.
Proof. vm_refl. Qed.
Lemma D_6d5dc : decode_any W_6d5dc = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5e0 : bv 32 := 0x0a051c63.
Lemma F_6d5e0 : fetch_word Asan.M.loaded_segments (0x6d630 : word) = Some W_6d5e0.
Proof. vm_refl. Qed.
Lemma D_6d5e0 : decode_any W_6d5e0 = Some (Branch BC_NE 10 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5f4 : bv 32 := 0xfbf48593.
Lemma F_6d5f4 : fetch_word Asan.M.loaded_segments (0x6d644 : word) = Some W_6d5f4.
Proof. vm_refl. Qed.
Lemma D_6d5f4 : decode_any W_6d5f4 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5f8 : bv 32 := 0xfbf00613.
Lemma F_6d5f8 : fetch_word Asan.M.loaded_segments (0x6d648 : word) = Some W_6d5f8.
Proof. vm_refl. Qed.
Lemma D_6d5f8 : decode_any W_6d5f8 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5fc : bv 32 := 0x12b67663.
Lemma F_6d5fc : fetch_word Asan.M.loaded_segments (0x6d64c : word) = Some W_6d5fc.
Proof. vm_refl. Qed.
Lemma D_6d5fc : decode_any W_6d5fc = Some (Branch BC_GEU 12 11 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d600 : bv 32 := 0x000f3597.
Lemma F_6d600 : fetch_word Asan.M.loaded_segments (0x6d650 : word) = Some W_6d600.
Proof. vm_refl. Qed.
Lemma D_6d600 : decode_any W_6d600 = Some (Auipc 11 243, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d604 : bv 32 := 0x5c85b583.
Lemma F_6d604 : fetch_word Asan.M.loaded_segments (0x6d654 : word) = Some W_6d604.
Proof. vm_refl. Qed.
Lemma D_6d604 : decode_any W_6d604 = Some (Load SZ8 true 11 11 1480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d608 : bv 32 := 0x009906b3.
Lemma F_6d608 : fetch_word Asan.M.loaded_segments (0x6d658 : word) = Some W_6d608.
Proof. vm_refl. Qed.
Lemma D_6d608 : decode_any W_6d608 = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d60c : bv 32 := 0x0005b603.
Lemma F_6d60c : fetch_word Asan.M.loaded_segments (0x6d65c : word) = Some W_6d60c.
Proof. vm_refl. Qed.
Lemma D_6d60c : decode_any W_6d60c = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d610 : bv 32 := 0x00395593.
Lemma F_6d610 : fetch_word Asan.M.loaded_segments (0x6d660 : word) = Some W_6d610.
Proof. vm_refl. Qed.
Lemma D_6d610 : decode_any W_6d610 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d614 : bv 32 := 0xfff68693.
Lemma F_6d614 : fetch_word Asan.M.loaded_segments (0x6d664 : word) = Some W_6d614.
Proof. vm_refl. Qed.
Lemma D_6d614 : decode_any W_6d614 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d618 : bv 32 := 0x0036d713.
Lemma F_6d618 : fetch_word Asan.M.loaded_segments (0x6d668 : word) = Some W_6d618.
Proof. vm_refl. Qed.
Lemma D_6d618 : decode_any W_6d618 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d61c : bv 32 := 0x00b605b3.
Lemma F_6d61c : fetch_word Asan.M.loaded_segments (0x6d66c : word) = Some W_6d61c.
Proof. vm_refl. Qed.
Lemma D_6d61c : decode_any W_6d61c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d620 : bv 32 := 0x00e60633.
Lemma F_6d620 : fetch_word Asan.M.loaded_segments (0x6d670 : word) = Some W_6d620.
Proof. vm_refl. Qed.
Lemma D_6d620 : decode_any W_6d620 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d624 : bv 32 := 0xff85f713.
Lemma F_6d624 : fetch_word Asan.M.loaded_segments (0x6d674 : word) = Some W_6d624.
Proof. vm_refl. Qed.
Lemma D_6d624 : decode_any W_6d624 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d628 : bv 32 := 0xff867793.
Lemma F_6d628 : fetch_word Asan.M.loaded_segments (0x6d678 : word) = Some W_6d628.
Proof. vm_refl. Qed.
Lemma D_6d628 : decode_any W_6d628 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d62c : bv 32 := 0x00073703.
Lemma F_6d62c : fetch_word Asan.M.loaded_segments (0x6d67c : word) = Some W_6d62c.
Proof. vm_refl. Qed.
Lemma D_6d62c : decode_any W_6d62c = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d630 : bv 32 := 0x0007b783.
Lemma F_6d630 : fetch_word Asan.M.loaded_segments (0x6d680 : word) = Some W_6d630.
Proof. vm_refl. Qed.
Lemma D_6d630 : decode_any W_6d630 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d634 : bv 32 := 0x00e7e733.
Lemma F_6d634 : fetch_word Asan.M.loaded_segments (0x6d684 : word) = Some W_6d634.
Proof. vm_refl. Qed.
Lemma D_6d634 : decode_any W_6d634 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d638 : bv 32 := 0x0e071c63.
Lemma F_6d638 : fetch_word Asan.M.loaded_segments (0x6d688 : word) = Some W_6d638.
Proof. vm_refl. Qed.
Lemma D_6d638 : decode_any W_6d638 = Some (Branch BC_NE 14 0 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d698 : bv 32 := 0x412504b3.
Lemma F_6d698 : fetch_word Asan.M.loaded_segments (0x6d6e8 : word) = Some W_6d698.
Proof. vm_refl. Qed.
Lemma D_6d698 : decode_any W_6d698 = Some (Op ALU_SUB 9 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d69c : bv 32 := 0x00148493.
Lemma F_6d69c : fetch_word Asan.M.loaded_segments (0x6d6ec : word) = Some W_6d69c.
Proof. vm_refl. Qed.
Lemma D_6d69c : decode_any W_6d69c = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d6a0 : bv 32 := 0xfff94593.
Lemma F_6d6a0 : fetch_word Asan.M.loaded_segments (0x6d6f0 : word) = Some W_6d6a0.
Proof. vm_refl. Qed.
Lemma D_6d6a0 : decode_any W_6d6a0 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d6a4 : bv 32 := 0x80040a13.
Lemma F_6d6a4 : fetch_word Asan.M.loaded_segments (0x6d6f4 : word) = Some W_6d6a4.
Proof. vm_refl. Qed.
Lemma D_6d6a4 : decode_any W_6d6a4 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d6a8 : bv 32 := 0xfb0a0a13.
Lemma F_6d6a8 : fetch_word Asan.M.loaded_segments (0x6d6f8 : word) = Some W_6d6a8.
Proof. vm_refl. Qed.
Lemma D_6d6a8 : decode_any W_6d6a8 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d6ac : bv 32 := 0xf495f4e3.
Lemma F_6d6ac : fetch_word Asan.M.loaded_segments (0x6d6fc : word) = Some W_6d6ac.
Proof. vm_refl. Qed.
Lemma D_6d6ac : decode_any W_6d6ac = Some (Branch BC_GEU 11 9 8008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d728 : bv 32 := 0x02049e63.
Lemma F_6d728 : fetch_word Asan.M.loaded_segments (0x6d778 : word) = Some W_6d728.
Proof. vm_refl. Qed.
Lemma D_6d728 : decode_any W_6d728 = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d764 : bv 32 := 0x00050a93.
Lemma F_6d764 : fetch_word Asan.M.loaded_segments (0x6d7b4 : word) = Some W_6d764.
Proof. vm_refl. Qed.
Lemma D_6d764 : decode_any W_6d764 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d768 : bv 32 := 0x00090513.
Lemma F_6d768 : fetch_word Asan.M.loaded_segments (0x6d7b8 : word) = Some W_6d768.
Proof. vm_refl. Qed.
Lemma D_6d768 : decode_any W_6d768 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d76c : bv 32 := 0x00048593.
Lemma F_6d76c : fetch_word Asan.M.loaded_segments (0x6d7bc : word) = Some W_6d76c.
Proof. vm_refl. Qed.
Lemma D_6d76c : decode_any W_6d76c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d770 : bv 32 := 0x2ac160ef.
Lemma F_6d770 : fetch_word Asan.M.loaded_segments (0x6d7c0 : word) = Some W_6d770.
Proof. vm_refl. Qed.
Lemma D_6d770 : decode_any W_6d770 = Some (Jal 1 90796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d774 : bv 32 := 0x00050913.
Lemma F_6d774 : fetch_word Asan.M.loaded_segments (0x6d7c4 : word) = Some W_6d774.
Proof. vm_refl. Qed.
Lemma D_6d774 : decode_any W_6d774 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d778 : bv 32 := 0x000a8513.
Lemma F_6d778 : fetch_word Asan.M.loaded_segments (0x6d7c8 : word) = Some W_6d778.
Proof. vm_refl. Qed.
Lemma D_6d778 : decode_any W_6d778 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d77c : bv 32 := 0xec0900e3.
Lemma F_6d77c : fetch_word Asan.M.loaded_segments (0x6d7cc : word) = Some W_6d77c.
Proof. vm_refl. Qed.
Lemma D_6d77c : decode_any W_6d77c = Some (Branch BC_EQ 18 0 7872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dac8 : bv 32 := 0x81010113.
Lemma F_6dac8 : fetch_word Asan.M.loaded_segments (0x6db18 : word) = Some W_6dac8.
Proof. vm_refl. Qed.
Lemma D_6dac8 : decode_any W_6dac8 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dacc : bv 32 := 0x7e113423.
Lemma F_6dacc : fetch_word Asan.M.loaded_segments (0x6db1c : word) = Some W_6dacc.
Proof. vm_refl. Qed.
Lemma D_6dacc : decode_any W_6dacc = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dad0 : bv 32 := 0x7e813023.
Lemma F_6dad0 : fetch_word Asan.M.loaded_segments (0x6db20 : word) = Some W_6dad0.
Proof. vm_refl. Qed.
Lemma D_6dad0 : decode_any W_6dad0 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dad4 : bv 32 := 0x7c913c23.
Lemma F_6dad4 : fetch_word Asan.M.loaded_segments (0x6db24 : word) = Some W_6dad4.
Proof. vm_refl. Qed.
Lemma D_6dad4 : decode_any W_6dad4 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dad8 : bv 32 := 0x7d213823.
Lemma F_6dad8 : fetch_word Asan.M.loaded_segments (0x6db28 : word) = Some W_6dad8.
Proof. vm_refl. Qed.
Lemma D_6dad8 : decode_any W_6dad8 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dadc : bv 32 := 0x7d313423.
Lemma F_6dadc : fetch_word Asan.M.loaded_segments (0x6db2c : word) = Some W_6dadc.
Proof. vm_refl. Qed.
Lemma D_6dadc : decode_any W_6dadc = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dae0 : bv 32 := 0x7d413023.
Lemma F_6dae0 : fetch_word Asan.M.loaded_segments (0x6db30 : word) = Some W_6dae0.
Proof. vm_refl. Qed.
Lemma D_6dae0 : decode_any W_6dae0 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dae4 : bv 32 := 0x7f010413.
Lemma F_6dae4 : fetch_word Asan.M.loaded_segments (0x6db34 : word) = Some W_6dae4.
Proof. vm_refl. Qed.
Lemma D_6dae4 : decode_any W_6dae4 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dae8 : bv 32 := 0xfa010113.
Lemma F_6dae8 : fetch_word Asan.M.loaded_segments (0x6db38 : word) = Some W_6dae8.
Proof. vm_refl. Qed.
Lemma D_6dae8 : decode_any W_6dae8 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6daec : bv 32 := 0x00060913.
Lemma F_6daec : fetch_word Asan.M.loaded_segments (0x6db3c : word) = Some W_6daec.
Proof. vm_refl. Qed.
Lemma D_6daec : decode_any W_6daec = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6daf0 : bv 32 := 0x00058493.
Lemma F_6daf0 : fetch_word Asan.M.loaded_segments (0x6db40 : word) = Some W_6daf0.
Proof. vm_refl. Qed.
Lemma D_6daf0 : decode_any W_6daf0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6daf4 : bv 32 := 0x00050993.
Lemma F_6daf4 : fetch_word Asan.M.loaded_segments (0x6db44 : word) = Some W_6daf4.
Proof. vm_refl. Qed.
Lemma D_6daf4 : decode_any W_6daf4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6daf8 : bv 32 := 0x3491b0ef.
Lemma F_6daf8 : fetch_word Asan.M.loaded_segments (0x6db48 : word) = Some W_6daf8.
Proof. vm_refl. Qed.
Lemma D_6daf8 : decode_any W_6daf8 = Some (Jal 1 113480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dafc : bv 32 := 0x000f5597.
Lemma F_6dafc : fetch_word Asan.M.loaded_segments (0x6db4c : word) = Some W_6dafc.
Proof. vm_refl. Qed.
Lemma D_6dafc : decode_any W_6dafc = Some (Auipc 11 245, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db00 : bv 32 := 0xf4c5b683.
Lemma F_6db00 : fetch_word Asan.M.loaded_segments (0x6db50 : word) = Some W_6db00.
Proof. vm_refl. Qed.
Lemma D_6db00 : decode_any W_6db00 = Some (Load SZ8 true 13 11 3916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db04 : bv 32 := 0x00050a13.
Lemma F_6db04 : fetch_word Asan.M.loaded_segments (0x6db54 : word) = Some W_6db04.
Proof. vm_refl. Qed.
Lemma D_6db04 : decode_any W_6db04 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db08 : bv 32 := 0x00098513.
Lemma F_6db08 : fetch_word Asan.M.loaded_segments (0x6db58 : word) = Some W_6db08.
Proof. vm_refl. Qed.
Lemma D_6db08 : decode_any W_6db08 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db0c : bv 32 := 0x00048593.
Lemma F_6db0c : fetch_word Asan.M.loaded_segments (0x6db5c : word) = Some W_6db0c.
Proof. vm_refl. Qed.
Lemma D_6db0c : decode_any W_6db0c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db10 : bv 32 := 0x00090613.
Lemma F_6db10 : fetch_word Asan.M.loaded_segments (0x6db60 : word) = Some W_6db10.
Proof. vm_refl. Qed.
Lemma D_6db10 : decode_any W_6db10 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db14 : bv 32 := 0x000680e7.
Lemma F_6db14 : fetch_word Asan.M.loaded_segments (0x6db64 : word) = Some W_6db14.
Proof. vm_refl. Qed.
Lemma D_6db14 : decode_any W_6db14 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db18 : bv 32 := 0x060a0063.
Lemma F_6db18 : fetch_word Asan.M.loaded_segments (0x6db68 : word) = Some W_6db18.
Proof. vm_refl. Qed.
Lemma D_6db18 : decode_any W_6db18 = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db1c : bv 32 := 0x04a05e63.
Lemma F_6db1c : fetch_word Asan.M.loaded_segments (0x6db6c : word) = Some W_6db1c.
Proof. vm_refl. Qed.
Lemma D_6db1c : decode_any W_6db1c = Some (Branch BC_GE 0 10 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db20 : bv 32 := 0xfff4c593.
Lemma F_6db20 : fetch_word Asan.M.loaded_segments (0x6db70 : word) = Some W_6db20.
Proof. vm_refl. Qed.
Lemma D_6db20 : decode_any W_6db20 = Some (OpImm ALU_XOR 11 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db24 : bv 32 := 0x80040a13.
Lemma F_6db24 : fetch_word Asan.M.loaded_segments (0x6db74 : word) = Some W_6db24.
Proof. vm_refl. Qed.
Lemma D_6db24 : decode_any W_6db24 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db28 : bv 32 := 0xfb8a0a13.
Lemma F_6db28 : fetch_word Asan.M.loaded_segments (0x6db78 : word) = Some W_6db28.
Proof. vm_refl. Qed.
Lemma D_6db28 : decode_any W_6db28 = Some (OpImm ALU_ADD 20 20 4024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db2c : bv 32 := 0x06a5e863.
Lemma F_6db2c : fetch_word Asan.M.loaded_segments (0x6db7c : word) = Some W_6db2c.
Proof. vm_refl. Qed.
Lemma D_6db2c : decode_any W_6db2c = Some (Branch BC_LTU 11 10 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db30 : bv 32 := 0xfbf50593.
Lemma F_6db30 : fetch_word Asan.M.loaded_segments (0x6db80 : word) = Some W_6db30.
Proof. vm_refl. Qed.
Lemma D_6db30 : decode_any W_6db30 = Some (OpImm ALU_ADD 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db34 : bv 32 := 0xfc000613.
Lemma F_6db34 : fetch_word Asan.M.loaded_segments (0x6db84 : word) = Some W_6db34.
Proof. vm_refl. Qed.
Lemma D_6db34 : decode_any W_6db34 = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db38 : bv 32 := 0x0cc5ee63.
Lemma F_6db38 : fetch_word Asan.M.loaded_segments (0x6db88 : word) = Some W_6db38.
Proof. vm_refl. Qed.
Lemma D_6db38 : decode_any W_6db38 = Some (Branch BC_LTU 11 12 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db3c : bv 32 := 0x000f3597.
Lemma F_6db3c : fetch_word Asan.M.loaded_segments (0x6db8c : word) = Some W_6db3c.
Proof. vm_refl. Qed.
Lemma D_6db3c : decode_any W_6db3c = Some (Auipc 11 243, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db40 : bv 32 := 0x08c5b583.
Lemma F_6db40 : fetch_word Asan.M.loaded_segments (0x6db90 : word) = Some W_6db40.
Proof. vm_refl. Qed.
Lemma D_6db40 : decode_any W_6db40 = Some (Load SZ8 true 11 11 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db44 : bv 32 := 0x00a486b3.
Lemma F_6db44 : fetch_word Asan.M.loaded_segments (0x6db94 : word) = Some W_6db44.
Proof. vm_refl. Qed.
Lemma D_6db44 : decode_any W_6db44 = Some (Op ALU_ADD 13 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db48 : bv 32 := 0x0005b603.
Lemma F_6db48 : fetch_word Asan.M.loaded_segments (0x6db98 : word) = Some W_6db48.
Proof. vm_refl. Qed.
Lemma D_6db48 : decode_any W_6db48 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db4c : bv 32 := 0x0034d593.
Lemma F_6db4c : fetch_word Asan.M.loaded_segments (0x6db9c : word) = Some W_6db4c.
Proof. vm_refl. Qed.
Lemma D_6db4c : decode_any W_6db4c = Some (ShiftImm ALU_SRL 11 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db50 : bv 32 := 0xfff68693.
Lemma F_6db50 : fetch_word Asan.M.loaded_segments (0x6dba0 : word) = Some W_6db50.
Proof. vm_refl. Qed.
Lemma D_6db50 : decode_any W_6db50 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db54 : bv 32 := 0x0036d713.
Lemma F_6db54 : fetch_word Asan.M.loaded_segments (0x6dba4 : word) = Some W_6db54.
Proof. vm_refl. Qed.
Lemma D_6db54 : decode_any W_6db54 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db58 : bv 32 := 0x00b605b3.
Lemma F_6db58 : fetch_word Asan.M.loaded_segments (0x6dba8 : word) = Some W_6db58.
Proof. vm_refl. Qed.
Lemma D_6db58 : decode_any W_6db58 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db5c : bv 32 := 0x00e60633.
Lemma F_6db5c : fetch_word Asan.M.loaded_segments (0x6dbac : word) = Some W_6db5c.
Proof. vm_refl. Qed.
Lemma D_6db5c : decode_any W_6db5c = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db60 : bv 32 := 0xff85f713.
Lemma F_6db60 : fetch_word Asan.M.loaded_segments (0x6dbb0 : word) = Some W_6db60.
Proof. vm_refl. Qed.
Lemma D_6db60 : decode_any W_6db60 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db64 : bv 32 := 0xff867793.
Lemma F_6db64 : fetch_word Asan.M.loaded_segments (0x6dbb4 : word) = Some W_6db64.
Proof. vm_refl. Qed.
Lemma D_6db64 : decode_any W_6db64 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db68 : bv 32 := 0x00073703.
Lemma F_6db68 : fetch_word Asan.M.loaded_segments (0x6dbb8 : word) = Some W_6db68.
Proof. vm_refl. Qed.
Lemma D_6db68 : decode_any W_6db68 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db6c : bv 32 := 0x0007b783.
Lemma F_6db6c : fetch_word Asan.M.loaded_segments (0x6dbbc : word) = Some W_6db6c.
Proof. vm_refl. Qed.
Lemma D_6db6c : decode_any W_6db6c = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db70 : bv 32 := 0x00e7e733.
Lemma F_6db70 : fetch_word Asan.M.loaded_segments (0x6dbc0 : word) = Some W_6db70.
Proof. vm_refl. Qed.
Lemma D_6db70 : decode_any W_6db70 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db74 : bv 32 := 0x14071663.
Lemma F_6db74 : fetch_word Asan.M.loaded_segments (0x6dbc4 : word) = Some W_6db74.
Proof. vm_refl. Qed.
Lemma D_6db74 : decode_any W_6db74 = Some (Branch BC_NE 14 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db78 : bv 32 := 0x06010113.
Lemma F_6db78 : fetch_word Asan.M.loaded_segments (0x6dbc8 : word) = Some W_6db78.
Proof. vm_refl. Qed.
Lemma D_6db78 : decode_any W_6db78 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db7c : bv 32 := 0x7e813083.
Lemma F_6db7c : fetch_word Asan.M.loaded_segments (0x6dbcc : word) = Some W_6db7c.
Proof. vm_refl. Qed.
Lemma D_6db7c : decode_any W_6db7c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db80 : bv 32 := 0x7e013403.
Lemma F_6db80 : fetch_word Asan.M.loaded_segments (0x6dbd0 : word) = Some W_6db80.
Proof. vm_refl. Qed.
Lemma D_6db80 : decode_any W_6db80 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db84 : bv 32 := 0x7d813483.
Lemma F_6db84 : fetch_word Asan.M.loaded_segments (0x6dbd4 : word) = Some W_6db84.
Proof. vm_refl. Qed.
Lemma D_6db84 : decode_any W_6db84 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db88 : bv 32 := 0x7d013903.
Lemma F_6db88 : fetch_word Asan.M.loaded_segments (0x6dbd8 : word) = Some W_6db88.
Proof. vm_refl. Qed.
Lemma D_6db88 : decode_any W_6db88 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db8c : bv 32 := 0x7c813983.
Lemma F_6db8c : fetch_word Asan.M.loaded_segments (0x6dbdc : word) = Some W_6db8c.
Proof. vm_refl. Qed.
Lemma D_6db8c : decode_any W_6db8c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db90 : bv 32 := 0x7c013a03.
Lemma F_6db90 : fetch_word Asan.M.loaded_segments (0x6dbe0 : word) = Some W_6db90.
Proof. vm_refl. Qed.
Lemma D_6db90 : decode_any W_6db90 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db94 : bv 32 := 0x7f010113.
Lemma F_6db94 : fetch_word Asan.M.loaded_segments (0x6dbe4 : word) = Some W_6db94.
Proof. vm_refl. Qed.
Lemma D_6db94 : decode_any W_6db94 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6db98 : bv 32 := 0x00008067.
Lemma F_6db98 : fetch_word Asan.M.loaded_segments (0x6dbe8 : word) = Some W_6db98.
Proof. vm_refl. Qed.
Lemma D_6db98 : decode_any W_6db98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dc14 : bv 32 := 0x00050913.
Lemma F_6dc14 : fetch_word Asan.M.loaded_segments (0x6dc64 : word) = Some W_6dc14.
Proof. vm_refl. Qed.
Lemma D_6dc14 : decode_any W_6dc14 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dc18 : bv 32 := 0x00048513.
Lemma F_6dc18 : fetch_word Asan.M.loaded_segments (0x6dc68 : word) = Some W_6dc18.
Proof. vm_refl. Qed.
Lemma D_6dc18 : decode_any W_6dc18 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dc1c : bv 32 := 0x00090593.
Lemma F_6dc1c : fetch_word Asan.M.loaded_segments (0x6dc6c : word) = Some W_6dc1c.
Proof. vm_refl. Qed.
Lemma D_6dc1c : decode_any W_6dc1c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dc20 : bv 32 := 0x5fd150ef.
Lemma F_6dc20 : fetch_word Asan.M.loaded_segments (0x6dc70 : word) = Some W_6dc20.
Proof. vm_refl. Qed.
Lemma D_6dc20 : decode_any W_6dc20 = Some (Jal 1 89596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dc24 : bv 32 := 0x00050493.
Lemma F_6dc24 : fetch_word Asan.M.loaded_segments (0x6dc74 : word) = Some W_6dc24.
Proof. vm_refl. Qed.
Lemma D_6dc24 : decode_any W_6dc24 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dc28 : bv 32 := 0x00090513.
Lemma F_6dc28 : fetch_word Asan.M.loaded_segments (0x6dc78 : word) = Some W_6dc28.
Proof. vm_refl. Qed.
Lemma D_6dc28 : decode_any W_6dc28 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dc2c : bv 32 := 0xf40486e3.
Lemma F_6dc2c : fetch_word Asan.M.loaded_segments (0x6dc7c : word) = Some W_6dc2c.
Proof. vm_refl. Qed.
Lemma D_6dc2c : decode_any W_6dc2c = Some (Branch BC_EQ 9 0 8012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dcc0 : bv 32 := 0x00060703.
Lemma F_6dcc0 : fetch_word Asan.M.loaded_segments (0x6dd10 : word) = Some W_6dcc0.
Proof. vm_refl. Qed.
Lemma D_6dcc0 : decode_any W_6dcc0 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dcc4 : bv 32 := 0x0076f693.
Lemma F_6dcc4 : fetch_word Asan.M.loaded_segments (0x6dd14 : word) = Some W_6dcc4.
Proof. vm_refl. Qed.
Lemma D_6dcc4 : decode_any W_6dcc4 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dcc8 : bv 32 := 0x00e037b3.
Lemma F_6dcc8 : fetch_word Asan.M.loaded_segments (0x6dd18 : word) = Some W_6dcc8.
Proof. vm_refl. Qed.
Lemma D_6dcc8 : decode_any W_6dcc8 = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dccc : bv 32 := 0x00e6a6b3.
Lemma F_6dccc : fetch_word Asan.M.loaded_segments (0x6dd1c : word) = Some W_6dccc.
Proof. vm_refl. Qed.
Lemma D_6dccc : decode_any W_6dccc = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dcd0 : bv 32 := 0x0016c693.
Lemma F_6dcd0 : fetch_word Asan.M.loaded_segments (0x6dd20 : word) = Some W_6dcd0.
Proof. vm_refl. Qed.
Lemma D_6dcd0 : decode_any W_6dcd0 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dcd4 : bv 32 := 0x00d7f6b3.
Lemma F_6dcd4 : fetch_word Asan.M.loaded_segments (0x6dd24 : word) = Some W_6dcd4.
Proof. vm_refl. Qed.
Lemma D_6dcd4 : decode_any W_6dcd4 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dcd8 : bv 32 := 0x00c5fa63.
Lemma F_6dcd8 : fetch_word Asan.M.loaded_segments (0x6dd28 : word) = Some W_6dcd8.
Proof. vm_refl. Qed.
Lemma D_6dcd8 : decode_any W_6dcd8 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dcdc : bv 32 := 0x0005c703.
Lemma F_6dcdc : fetch_word Asan.M.loaded_segments (0x6dd2c : word) = Some W_6dcdc.
Proof. vm_refl. Qed.
Lemma D_6dcdc : decode_any W_6dcdc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dce0 : bv 32 := 0x00158593.
Lemma F_6dce0 : fetch_word Asan.M.loaded_segments (0x6dd30 : word) = Some W_6dce0.
Proof. vm_refl. Qed.
Lemma D_6dce0 : decode_any W_6dce0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dce4 : bv 32 := 0x00d766b3.
Lemma F_6dce4 : fetch_word Asan.M.loaded_segments (0x6dd34 : word) = Some W_6dce4.
Proof. vm_refl. Qed.
Lemma D_6dce4 : decode_any W_6dce4 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dce8 : bv 32 := 0xfec59ae3.
Lemma F_6dce8 : fetch_word Asan.M.loaded_segments (0x6dd38 : word) = Some W_6dce8.
Proof. vm_refl. Qed.
Lemma D_6dce8 : decode_any W_6dce8 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dcec : bv 32 := 0x0ff6f593.
Lemma F_6dcec : fetch_word Asan.M.loaded_segments (0x6dd3c : word) = Some W_6dcec.
Proof. vm_refl. Qed.
Lemma D_6dcec : decode_any W_6dcec = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dcf0 : bv 32 := 0xe80584e3.
Lemma F_6dcf0 : fetch_word Asan.M.loaded_segments (0x6dd40 : word) = Some W_6dcf0.
Proof. vm_refl. Qed.
Lemma D_6dcf0 : decode_any W_6dcf0 = Some (Branch BC_EQ 11 0 7816, 4%Z).
Proof. vm_refl. Qed.

