(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6c210 : bv 32 := 0x060a0063.
Lemma F_6c210 : fetch_word Asan.M.loaded_segments (0x6c260 : word) = Some W_6c210.
Proof. vm_refl. Qed.
Lemma D_6c210 : decode_any W_6c210 = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c214 : bv 32 := 0x0a051c63.
Lemma F_6c214 : fetch_word Asan.M.loaded_segments (0x6c264 : word) = Some W_6c214.
Proof. vm_refl. Qed.
Lemma D_6c214 : decode_any W_6c214 = Some (Branch BC_NE 10 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c228 : bv 32 := 0xfbf48593.
Lemma F_6c228 : fetch_word Asan.M.loaded_segments (0x6c278 : word) = Some W_6c228.
Proof. vm_refl. Qed.
Lemma D_6c228 : decode_any W_6c228 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c22c : bv 32 := 0xfbf00613.
Lemma F_6c22c : fetch_word Asan.M.loaded_segments (0x6c27c : word) = Some W_6c22c.
Proof. vm_refl. Qed.
Lemma D_6c22c : decode_any W_6c22c = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c230 : bv 32 := 0x12b67663.
Lemma F_6c230 : fetch_word Asan.M.loaded_segments (0x6c280 : word) = Some W_6c230.
Proof. vm_refl. Qed.
Lemma D_6c230 : decode_any W_6c230 = Some (Branch BC_GEU 12 11 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c234 : bv 32 := 0x000e7597.
Lemma F_6c234 : fetch_word Asan.M.loaded_segments (0x6c284 : word) = Some W_6c234.
Proof. vm_refl. Qed.
Lemma D_6c234 : decode_any W_6c234 = Some (Auipc 11 231, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c238 : bv 32 := 0xeb45b583.
Lemma F_6c238 : fetch_word Asan.M.loaded_segments (0x6c288 : word) = Some W_6c238.
Proof. vm_refl. Qed.
Lemma D_6c238 : decode_any W_6c238 = Some (Load SZ8 true 11 11 3764, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c23c : bv 32 := 0x009906b3.
Lemma F_6c23c : fetch_word Asan.M.loaded_segments (0x6c28c : word) = Some W_6c23c.
Proof. vm_refl. Qed.
Lemma D_6c23c : decode_any W_6c23c = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c240 : bv 32 := 0x0005b603.
Lemma F_6c240 : fetch_word Asan.M.loaded_segments (0x6c290 : word) = Some W_6c240.
Proof. vm_refl. Qed.
Lemma D_6c240 : decode_any W_6c240 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c244 : bv 32 := 0x00395593.
Lemma F_6c244 : fetch_word Asan.M.loaded_segments (0x6c294 : word) = Some W_6c244.
Proof. vm_refl. Qed.
Lemma D_6c244 : decode_any W_6c244 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c248 : bv 32 := 0xfff68693.
Lemma F_6c248 : fetch_word Asan.M.loaded_segments (0x6c298 : word) = Some W_6c248.
Proof. vm_refl. Qed.
Lemma D_6c248 : decode_any W_6c248 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c24c : bv 32 := 0x0036d713.
Lemma F_6c24c : fetch_word Asan.M.loaded_segments (0x6c29c : word) = Some W_6c24c.
Proof. vm_refl. Qed.
Lemma D_6c24c : decode_any W_6c24c = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c250 : bv 32 := 0x00b605b3.
Lemma F_6c250 : fetch_word Asan.M.loaded_segments (0x6c2a0 : word) = Some W_6c250.
Proof. vm_refl. Qed.
Lemma D_6c250 : decode_any W_6c250 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c254 : bv 32 := 0x00e60633.
Lemma F_6c254 : fetch_word Asan.M.loaded_segments (0x6c2a4 : word) = Some W_6c254.
Proof. vm_refl. Qed.
Lemma D_6c254 : decode_any W_6c254 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c258 : bv 32 := 0xff85f713.
Lemma F_6c258 : fetch_word Asan.M.loaded_segments (0x6c2a8 : word) = Some W_6c258.
Proof. vm_refl. Qed.
Lemma D_6c258 : decode_any W_6c258 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c25c : bv 32 := 0xff867793.
Lemma F_6c25c : fetch_word Asan.M.loaded_segments (0x6c2ac : word) = Some W_6c25c.
Proof. vm_refl. Qed.
Lemma D_6c25c : decode_any W_6c25c = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c260 : bv 32 := 0x00073703.
Lemma F_6c260 : fetch_word Asan.M.loaded_segments (0x6c2b0 : word) = Some W_6c260.
Proof. vm_refl. Qed.
Lemma D_6c260 : decode_any W_6c260 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c264 : bv 32 := 0x0007b783.
Lemma F_6c264 : fetch_word Asan.M.loaded_segments (0x6c2b4 : word) = Some W_6c264.
Proof. vm_refl. Qed.
Lemma D_6c264 : decode_any W_6c264 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c268 : bv 32 := 0x00e7e733.
Lemma F_6c268 : fetch_word Asan.M.loaded_segments (0x6c2b8 : word) = Some W_6c268.
Proof. vm_refl. Qed.
Lemma D_6c268 : decode_any W_6c268 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c26c : bv 32 := 0x0e071c63.
Lemma F_6c26c : fetch_word Asan.M.loaded_segments (0x6c2bc : word) = Some W_6c26c.
Proof. vm_refl. Qed.
Lemma D_6c26c : decode_any W_6c26c = Some (Branch BC_NE 14 0 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2cc : bv 32 := 0x412504b3.
Lemma F_6c2cc : fetch_word Asan.M.loaded_segments (0x6c31c : word) = Some W_6c2cc.
Proof. vm_refl. Qed.
Lemma D_6c2cc : decode_any W_6c2cc = Some (Op ALU_SUB 9 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2d0 : bv 32 := 0x00148493.
Lemma F_6c2d0 : fetch_word Asan.M.loaded_segments (0x6c320 : word) = Some W_6c2d0.
Proof. vm_refl. Qed.
Lemma D_6c2d0 : decode_any W_6c2d0 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2d4 : bv 32 := 0xfff94593.
Lemma F_6c2d4 : fetch_word Asan.M.loaded_segments (0x6c324 : word) = Some W_6c2d4.
Proof. vm_refl. Qed.
Lemma D_6c2d4 : decode_any W_6c2d4 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2d8 : bv 32 := 0x80040a13.
Lemma F_6c2d8 : fetch_word Asan.M.loaded_segments (0x6c328 : word) = Some W_6c2d8.
Proof. vm_refl. Qed.
Lemma D_6c2d8 : decode_any W_6c2d8 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2dc : bv 32 := 0xfb0a0a13.
Lemma F_6c2dc : fetch_word Asan.M.loaded_segments (0x6c32c : word) = Some W_6c2dc.
Proof. vm_refl. Qed.
Lemma D_6c2dc : decode_any W_6c2dc = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2e0 : bv 32 := 0xf495f4e3.
Lemma F_6c2e0 : fetch_word Asan.M.loaded_segments (0x6c330 : word) = Some W_6c2e0.
Proof. vm_refl. Qed.
Lemma D_6c2e0 : decode_any W_6c2e0 = Some (Branch BC_GEU 11 9 8008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c35c : bv 32 := 0x02049e63.
Lemma F_6c35c : fetch_word Asan.M.loaded_segments (0x6c3ac : word) = Some W_6c35c.
Proof. vm_refl. Qed.
Lemma D_6c35c : decode_any W_6c35c = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c398 : bv 32 := 0x00050a93.
Lemma F_6c398 : fetch_word Asan.M.loaded_segments (0x6c3e8 : word) = Some W_6c398.
Proof. vm_refl. Qed.
Lemma D_6c398 : decode_any W_6c398 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c39c : bv 32 := 0x00090513.
Lemma F_6c39c : fetch_word Asan.M.loaded_segments (0x6c3ec : word) = Some W_6c39c.
Proof. vm_refl. Qed.
Lemma D_6c39c : decode_any W_6c39c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3a0 : bv 32 := 0x00048593.
Lemma F_6c3a0 : fetch_word Asan.M.loaded_segments (0x6c3f0 : word) = Some W_6c3a0.
Proof. vm_refl. Qed.
Lemma D_6c3a0 : decode_any W_6c3a0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3a4 : bv 32 := 0x2ac160ef.
Lemma F_6c3a4 : fetch_word Asan.M.loaded_segments (0x6c3f4 : word) = Some W_6c3a4.
Proof. vm_refl. Qed.
Lemma D_6c3a4 : decode_any W_6c3a4 = Some (Jal 1 90796, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3a8 : bv 32 := 0x00050913.
Lemma F_6c3a8 : fetch_word Asan.M.loaded_segments (0x6c3f8 : word) = Some W_6c3a8.
Proof. vm_refl. Qed.
Lemma D_6c3a8 : decode_any W_6c3a8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3ac : bv 32 := 0x000a8513.
Lemma F_6c3ac : fetch_word Asan.M.loaded_segments (0x6c3fc : word) = Some W_6c3ac.
Proof. vm_refl. Qed.
Lemma D_6c3ac : decode_any W_6c3ac = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3b0 : bv 32 := 0xec0900e3.
Lemma F_6c3b0 : fetch_word Asan.M.loaded_segments (0x6c400 : word) = Some W_6c3b0.
Proof. vm_refl. Qed.
Lemma D_6c3b0 : decode_any W_6c3b0 = Some (Branch BC_EQ 18 0 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c6fc : bv 32 := 0x81010113.
Lemma F_6c6fc : fetch_word Asan.M.loaded_segments (0x6c74c : word) = Some W_6c6fc.
Proof. vm_refl. Qed.
Lemma D_6c6fc : decode_any W_6c6fc = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c700 : bv 32 := 0x7e113423.
Lemma F_6c700 : fetch_word Asan.M.loaded_segments (0x6c750 : word) = Some W_6c700.
Proof. vm_refl. Qed.
Lemma D_6c700 : decode_any W_6c700 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c704 : bv 32 := 0x7e813023.
Lemma F_6c704 : fetch_word Asan.M.loaded_segments (0x6c754 : word) = Some W_6c704.
Proof. vm_refl. Qed.
Lemma D_6c704 : decode_any W_6c704 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c708 : bv 32 := 0x7c913c23.
Lemma F_6c708 : fetch_word Asan.M.loaded_segments (0x6c758 : word) = Some W_6c708.
Proof. vm_refl. Qed.
Lemma D_6c708 : decode_any W_6c708 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c70c : bv 32 := 0x7d213823.
Lemma F_6c70c : fetch_word Asan.M.loaded_segments (0x6c75c : word) = Some W_6c70c.
Proof. vm_refl. Qed.
Lemma D_6c70c : decode_any W_6c70c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c710 : bv 32 := 0x7d313423.
Lemma F_6c710 : fetch_word Asan.M.loaded_segments (0x6c760 : word) = Some W_6c710.
Proof. vm_refl. Qed.
Lemma D_6c710 : decode_any W_6c710 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c714 : bv 32 := 0x7d413023.
Lemma F_6c714 : fetch_word Asan.M.loaded_segments (0x6c764 : word) = Some W_6c714.
Proof. vm_refl. Qed.
Lemma D_6c714 : decode_any W_6c714 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c718 : bv 32 := 0x7f010413.
Lemma F_6c718 : fetch_word Asan.M.loaded_segments (0x6c768 : word) = Some W_6c718.
Proof. vm_refl. Qed.
Lemma D_6c718 : decode_any W_6c718 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c71c : bv 32 := 0xfa010113.
Lemma F_6c71c : fetch_word Asan.M.loaded_segments (0x6c76c : word) = Some W_6c71c.
Proof. vm_refl. Qed.
Lemma D_6c71c : decode_any W_6c71c = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c720 : bv 32 := 0x00060913.
Lemma F_6c720 : fetch_word Asan.M.loaded_segments (0x6c770 : word) = Some W_6c720.
Proof. vm_refl. Qed.
Lemma D_6c720 : decode_any W_6c720 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c724 : bv 32 := 0x00058493.
Lemma F_6c724 : fetch_word Asan.M.loaded_segments (0x6c774 : word) = Some W_6c724.
Proof. vm_refl. Qed.
Lemma D_6c724 : decode_any W_6c724 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c728 : bv 32 := 0x00050993.
Lemma F_6c728 : fetch_word Asan.M.loaded_segments (0x6c778 : word) = Some W_6c728.
Proof. vm_refl. Qed.
Lemma D_6c728 : decode_any W_6c728 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c72c : bv 32 := 0x3491b0ef.
Lemma F_6c72c : fetch_word Asan.M.loaded_segments (0x6c77c : word) = Some W_6c72c.
Proof. vm_refl. Qed.
Lemma D_6c72c : decode_any W_6c72c = Some (Jal 1 113480, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c730 : bv 32 := 0x000e9597.
Lemma F_6c730 : fetch_word Asan.M.loaded_segments (0x6c780 : word) = Some W_6c730.
Proof. vm_refl. Qed.
Lemma D_6c730 : decode_any W_6c730 = Some (Auipc 11 233, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c734 : bv 32 := 0x8285b683.
Lemma F_6c734 : fetch_word Asan.M.loaded_segments (0x6c784 : word) = Some W_6c734.
Proof. vm_refl. Qed.
Lemma D_6c734 : decode_any W_6c734 = Some (Load SZ8 true 13 11 2088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c738 : bv 32 := 0x00050a13.
Lemma F_6c738 : fetch_word Asan.M.loaded_segments (0x6c788 : word) = Some W_6c738.
Proof. vm_refl. Qed.
Lemma D_6c738 : decode_any W_6c738 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c73c : bv 32 := 0x00098513.
Lemma F_6c73c : fetch_word Asan.M.loaded_segments (0x6c78c : word) = Some W_6c73c.
Proof. vm_refl. Qed.
Lemma D_6c73c : decode_any W_6c73c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c740 : bv 32 := 0x00048593.
Lemma F_6c740 : fetch_word Asan.M.loaded_segments (0x6c790 : word) = Some W_6c740.
Proof. vm_refl. Qed.
Lemma D_6c740 : decode_any W_6c740 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c744 : bv 32 := 0x00090613.
Lemma F_6c744 : fetch_word Asan.M.loaded_segments (0x6c794 : word) = Some W_6c744.
Proof. vm_refl. Qed.
Lemma D_6c744 : decode_any W_6c744 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c748 : bv 32 := 0x000680e7.
Lemma F_6c748 : fetch_word Asan.M.loaded_segments (0x6c798 : word) = Some W_6c748.
Proof. vm_refl. Qed.
Lemma D_6c748 : decode_any W_6c748 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c74c : bv 32 := 0x060a0063.
Lemma F_6c74c : fetch_word Asan.M.loaded_segments (0x6c79c : word) = Some W_6c74c.
Proof. vm_refl. Qed.
Lemma D_6c74c : decode_any W_6c74c = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c750 : bv 32 := 0x04a05e63.
Lemma F_6c750 : fetch_word Asan.M.loaded_segments (0x6c7a0 : word) = Some W_6c750.
Proof. vm_refl. Qed.
Lemma D_6c750 : decode_any W_6c750 = Some (Branch BC_GE 0 10 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c754 : bv 32 := 0xfff4c593.
Lemma F_6c754 : fetch_word Asan.M.loaded_segments (0x6c7a4 : word) = Some W_6c754.
Proof. vm_refl. Qed.
Lemma D_6c754 : decode_any W_6c754 = Some (OpImm ALU_XOR 11 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c758 : bv 32 := 0x80040a13.
Lemma F_6c758 : fetch_word Asan.M.loaded_segments (0x6c7a8 : word) = Some W_6c758.
Proof. vm_refl. Qed.
Lemma D_6c758 : decode_any W_6c758 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c75c : bv 32 := 0xfb8a0a13.
Lemma F_6c75c : fetch_word Asan.M.loaded_segments (0x6c7ac : word) = Some W_6c75c.
Proof. vm_refl. Qed.
Lemma D_6c75c : decode_any W_6c75c = Some (OpImm ALU_ADD 20 20 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c760 : bv 32 := 0x06a5e863.
Lemma F_6c760 : fetch_word Asan.M.loaded_segments (0x6c7b0 : word) = Some W_6c760.
Proof. vm_refl. Qed.
Lemma D_6c760 : decode_any W_6c760 = Some (Branch BC_LTU 11 10 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c764 : bv 32 := 0xfbf50593.
Lemma F_6c764 : fetch_word Asan.M.loaded_segments (0x6c7b4 : word) = Some W_6c764.
Proof. vm_refl. Qed.
Lemma D_6c764 : decode_any W_6c764 = Some (OpImm ALU_ADD 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c768 : bv 32 := 0xfc000613.
Lemma F_6c768 : fetch_word Asan.M.loaded_segments (0x6c7b8 : word) = Some W_6c768.
Proof. vm_refl. Qed.
Lemma D_6c768 : decode_any W_6c768 = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c76c : bv 32 := 0x0cc5ee63.
Lemma F_6c76c : fetch_word Asan.M.loaded_segments (0x6c7bc : word) = Some W_6c76c.
Proof. vm_refl. Qed.
Lemma D_6c76c : decode_any W_6c76c = Some (Branch BC_LTU 11 12 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c770 : bv 32 := 0x000e7597.
Lemma F_6c770 : fetch_word Asan.M.loaded_segments (0x6c7c0 : word) = Some W_6c770.
Proof. vm_refl. Qed.
Lemma D_6c770 : decode_any W_6c770 = Some (Auipc 11 231, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c774 : bv 32 := 0x9785b583.
Lemma F_6c774 : fetch_word Asan.M.loaded_segments (0x6c7c4 : word) = Some W_6c774.
Proof. vm_refl. Qed.
Lemma D_6c774 : decode_any W_6c774 = Some (Load SZ8 true 11 11 2424, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c778 : bv 32 := 0x00a486b3.
Lemma F_6c778 : fetch_word Asan.M.loaded_segments (0x6c7c8 : word) = Some W_6c778.
Proof. vm_refl. Qed.
Lemma D_6c778 : decode_any W_6c778 = Some (Op ALU_ADD 13 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c77c : bv 32 := 0x0005b603.
Lemma F_6c77c : fetch_word Asan.M.loaded_segments (0x6c7cc : word) = Some W_6c77c.
Proof. vm_refl. Qed.
Lemma D_6c77c : decode_any W_6c77c = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c780 : bv 32 := 0x0034d593.
Lemma F_6c780 : fetch_word Asan.M.loaded_segments (0x6c7d0 : word) = Some W_6c780.
Proof. vm_refl. Qed.
Lemma D_6c780 : decode_any W_6c780 = Some (ShiftImm ALU_SRL 11 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c784 : bv 32 := 0xfff68693.
Lemma F_6c784 : fetch_word Asan.M.loaded_segments (0x6c7d4 : word) = Some W_6c784.
Proof. vm_refl. Qed.
Lemma D_6c784 : decode_any W_6c784 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c788 : bv 32 := 0x0036d713.
Lemma F_6c788 : fetch_word Asan.M.loaded_segments (0x6c7d8 : word) = Some W_6c788.
Proof. vm_refl. Qed.
Lemma D_6c788 : decode_any W_6c788 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c78c : bv 32 := 0x00b605b3.
Lemma F_6c78c : fetch_word Asan.M.loaded_segments (0x6c7dc : word) = Some W_6c78c.
Proof. vm_refl. Qed.
Lemma D_6c78c : decode_any W_6c78c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c790 : bv 32 := 0x00e60633.
Lemma F_6c790 : fetch_word Asan.M.loaded_segments (0x6c7e0 : word) = Some W_6c790.
Proof. vm_refl. Qed.
Lemma D_6c790 : decode_any W_6c790 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c794 : bv 32 := 0xff85f713.
Lemma F_6c794 : fetch_word Asan.M.loaded_segments (0x6c7e4 : word) = Some W_6c794.
Proof. vm_refl. Qed.
Lemma D_6c794 : decode_any W_6c794 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c798 : bv 32 := 0xff867793.
Lemma F_6c798 : fetch_word Asan.M.loaded_segments (0x6c7e8 : word) = Some W_6c798.
Proof. vm_refl. Qed.
Lemma D_6c798 : decode_any W_6c798 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c79c : bv 32 := 0x00073703.
Lemma F_6c79c : fetch_word Asan.M.loaded_segments (0x6c7ec : word) = Some W_6c79c.
Proof. vm_refl. Qed.
Lemma D_6c79c : decode_any W_6c79c = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c7a0 : bv 32 := 0x0007b783.
Lemma F_6c7a0 : fetch_word Asan.M.loaded_segments (0x6c7f0 : word) = Some W_6c7a0.
Proof. vm_refl. Qed.
Lemma D_6c7a0 : decode_any W_6c7a0 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c7a4 : bv 32 := 0x00e7e733.
Lemma F_6c7a4 : fetch_word Asan.M.loaded_segments (0x6c7f4 : word) = Some W_6c7a4.
Proof. vm_refl. Qed.
Lemma D_6c7a4 : decode_any W_6c7a4 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c7a8 : bv 32 := 0x14071663.
Lemma F_6c7a8 : fetch_word Asan.M.loaded_segments (0x6c7f8 : word) = Some W_6c7a8.
Proof. vm_refl. Qed.
Lemma D_6c7a8 : decode_any W_6c7a8 = Some (Branch BC_NE 14 0 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c7ac : bv 32 := 0x06010113.
Lemma F_6c7ac : fetch_word Asan.M.loaded_segments (0x6c7fc : word) = Some W_6c7ac.
Proof. vm_refl. Qed.
Lemma D_6c7ac : decode_any W_6c7ac = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c7b0 : bv 32 := 0x7e813083.
Lemma F_6c7b0 : fetch_word Asan.M.loaded_segments (0x6c800 : word) = Some W_6c7b0.
Proof. vm_refl. Qed.
Lemma D_6c7b0 : decode_any W_6c7b0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c7b4 : bv 32 := 0x7e013403.
Lemma F_6c7b4 : fetch_word Asan.M.loaded_segments (0x6c804 : word) = Some W_6c7b4.
Proof. vm_refl. Qed.
Lemma D_6c7b4 : decode_any W_6c7b4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c7b8 : bv 32 := 0x7d813483.
Lemma F_6c7b8 : fetch_word Asan.M.loaded_segments (0x6c808 : word) = Some W_6c7b8.
Proof. vm_refl. Qed.
Lemma D_6c7b8 : decode_any W_6c7b8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c7bc : bv 32 := 0x7d013903.
Lemma F_6c7bc : fetch_word Asan.M.loaded_segments (0x6c80c : word) = Some W_6c7bc.
Proof. vm_refl. Qed.
Lemma D_6c7bc : decode_any W_6c7bc = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c7c0 : bv 32 := 0x7c813983.
Lemma F_6c7c0 : fetch_word Asan.M.loaded_segments (0x6c810 : word) = Some W_6c7c0.
Proof. vm_refl. Qed.
Lemma D_6c7c0 : decode_any W_6c7c0 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c7c4 : bv 32 := 0x7c013a03.
Lemma F_6c7c4 : fetch_word Asan.M.loaded_segments (0x6c814 : word) = Some W_6c7c4.
Proof. vm_refl. Qed.
Lemma D_6c7c4 : decode_any W_6c7c4 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c7c8 : bv 32 := 0x7f010113.
Lemma F_6c7c8 : fetch_word Asan.M.loaded_segments (0x6c818 : word) = Some W_6c7c8.
Proof. vm_refl. Qed.
Lemma D_6c7c8 : decode_any W_6c7c8 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c7cc : bv 32 := 0x00008067.
Lemma F_6c7cc : fetch_word Asan.M.loaded_segments (0x6c81c : word) = Some W_6c7cc.
Proof. vm_refl. Qed.
Lemma D_6c7cc : decode_any W_6c7cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c848 : bv 32 := 0x00050913.
Lemma F_6c848 : fetch_word Asan.M.loaded_segments (0x6c898 : word) = Some W_6c848.
Proof. vm_refl. Qed.
Lemma D_6c848 : decode_any W_6c848 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c84c : bv 32 := 0x00048513.
Lemma F_6c84c : fetch_word Asan.M.loaded_segments (0x6c89c : word) = Some W_6c84c.
Proof. vm_refl. Qed.
Lemma D_6c84c : decode_any W_6c84c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c850 : bv 32 := 0x00090593.
Lemma F_6c850 : fetch_word Asan.M.loaded_segments (0x6c8a0 : word) = Some W_6c850.
Proof. vm_refl. Qed.
Lemma D_6c850 : decode_any W_6c850 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c854 : bv 32 := 0x5fd150ef.
Lemma F_6c854 : fetch_word Asan.M.loaded_segments (0x6c8a4 : word) = Some W_6c854.
Proof. vm_refl. Qed.
Lemma D_6c854 : decode_any W_6c854 = Some (Jal 1 89596, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c858 : bv 32 := 0x00050493.
Lemma F_6c858 : fetch_word Asan.M.loaded_segments (0x6c8a8 : word) = Some W_6c858.
Proof. vm_refl. Qed.
Lemma D_6c858 : decode_any W_6c858 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c85c : bv 32 := 0x00090513.
Lemma F_6c85c : fetch_word Asan.M.loaded_segments (0x6c8ac : word) = Some W_6c85c.
Proof. vm_refl. Qed.
Lemma D_6c85c : decode_any W_6c85c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c860 : bv 32 := 0xf40486e3.
Lemma F_6c860 : fetch_word Asan.M.loaded_segments (0x6c8b0 : word) = Some W_6c860.
Proof. vm_refl. Qed.
Lemma D_6c860 : decode_any W_6c860 = Some (Branch BC_EQ 9 0 8012, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c8f4 : bv 32 := 0x00060703.
Lemma F_6c8f4 : fetch_word Asan.M.loaded_segments (0x6c944 : word) = Some W_6c8f4.
Proof. vm_refl. Qed.
Lemma D_6c8f4 : decode_any W_6c8f4 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c8f8 : bv 32 := 0x0076f693.
Lemma F_6c8f8 : fetch_word Asan.M.loaded_segments (0x6c948 : word) = Some W_6c8f8.
Proof. vm_refl. Qed.
Lemma D_6c8f8 : decode_any W_6c8f8 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c8fc : bv 32 := 0x00e037b3.
Lemma F_6c8fc : fetch_word Asan.M.loaded_segments (0x6c94c : word) = Some W_6c8fc.
Proof. vm_refl. Qed.
Lemma D_6c8fc : decode_any W_6c8fc = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c900 : bv 32 := 0x00e6a6b3.
Lemma F_6c900 : fetch_word Asan.M.loaded_segments (0x6c950 : word) = Some W_6c900.
Proof. vm_refl. Qed.
Lemma D_6c900 : decode_any W_6c900 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c904 : bv 32 := 0x0016c693.
Lemma F_6c904 : fetch_word Asan.M.loaded_segments (0x6c954 : word) = Some W_6c904.
Proof. vm_refl. Qed.
Lemma D_6c904 : decode_any W_6c904 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c908 : bv 32 := 0x00d7f6b3.
Lemma F_6c908 : fetch_word Asan.M.loaded_segments (0x6c958 : word) = Some W_6c908.
Proof. vm_refl. Qed.
Lemma D_6c908 : decode_any W_6c908 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c90c : bv 32 := 0x00c5fa63.
Lemma F_6c90c : fetch_word Asan.M.loaded_segments (0x6c95c : word) = Some W_6c90c.
Proof. vm_refl. Qed.
Lemma D_6c90c : decode_any W_6c90c = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c910 : bv 32 := 0x0005c703.
Lemma F_6c910 : fetch_word Asan.M.loaded_segments (0x6c960 : word) = Some W_6c910.
Proof. vm_refl. Qed.
Lemma D_6c910 : decode_any W_6c910 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c914 : bv 32 := 0x00158593.
Lemma F_6c914 : fetch_word Asan.M.loaded_segments (0x6c964 : word) = Some W_6c914.
Proof. vm_refl. Qed.
Lemma D_6c914 : decode_any W_6c914 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c918 : bv 32 := 0x00d766b3.
Lemma F_6c918 : fetch_word Asan.M.loaded_segments (0x6c968 : word) = Some W_6c918.
Proof. vm_refl. Qed.
Lemma D_6c918 : decode_any W_6c918 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c91c : bv 32 := 0xfec59ae3.
Lemma F_6c91c : fetch_word Asan.M.loaded_segments (0x6c96c : word) = Some W_6c91c.
Proof. vm_refl. Qed.
Lemma D_6c91c : decode_any W_6c91c = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c920 : bv 32 := 0x0ff6f593.
Lemma F_6c920 : fetch_word Asan.M.loaded_segments (0x6c970 : word) = Some W_6c920.
Proof. vm_refl. Qed.
Lemma D_6c920 : decode_any W_6c920 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c924 : bv 32 := 0xe80584e3.
Lemma F_6c924 : fetch_word Asan.M.loaded_segments (0x6c974 : word) = Some W_6c924.
Proof. vm_refl. Qed.
Lemma D_6c924 : decode_any W_6c924 = Some (Branch BC_EQ 11 0 7816, 4%Z).
Proof. vm_refl. Qed.

