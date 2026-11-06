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
Definition W_16000 : bv 32 := 0x00052503.
Lemma F_16000 : fetch_word Ubsan.M.loaded_segments (0x160fc : word) = Some W_16000.
Proof. vm_refl. Qed.
Lemma D_16000 : decode_any W_16000 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16004 : bv 32 := 0x00500593.
Lemma F_16004 : fetch_word Ubsan.M.loaded_segments (0x16100 : word) = Some W_16004.
Proof. vm_refl. Qed.
Lemma D_16004 : decode_any W_16004 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16008 : bv 32 := 0x04a5c463.
Lemma F_16008 : fetch_word Ubsan.M.loaded_segments (0x16104 : word) = Some W_16008.
Proof. vm_refl. Qed.
Lemma D_16008 : decode_any W_16008 = Some (Branch BC_LT 11 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1600c : bv 32 := 0xffffa517.
Lemma F_1600c : fetch_word Ubsan.M.loaded_segments (0x16108 : word) = Some W_1600c.
Proof. vm_refl. Qed.
Lemma D_1600c : decode_any W_1600c = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16010 : bv 32 := 0xffffa597.
Lemma F_16010 : fetch_word Ubsan.M.loaded_segments (0x1610c : word) = Some W_16010.
Proof. vm_refl. Qed.
Lemma D_16010 : decode_any W_16010 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16014 : bv 32 := 0x2ec50513.
Lemma F_16014 : fetch_word Ubsan.M.loaded_segments (0x16110 : word) = Some W_16014.
Proof. vm_refl. Qed.
Lemma D_16014 : decode_any W_16014 = Some (OpImm ALU_ADD 10 10 748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16018 : bv 32 := 0x44c58593.
Lemma F_16018 : fetch_word Ubsan.M.loaded_segments (0x16114 : word) = Some W_16018.
Proof. vm_refl. Qed.
Lemma D_16018 : decode_any W_16018 = Some (OpImm ALU_ADD 11 11 1100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1601c : bv 32 := 0x00100613.
Lemma F_1601c : fetch_word Ubsan.M.loaded_segments (0x16118 : word) = Some W_1601c.
Proof. vm_refl. Qed.
Lemma D_1601c : decode_any W_1601c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16020 : bv 32 := 0x9b9fd06f.
Lemma F_16020 : fetch_word Ubsan.M.loaded_segments (0x1611c : word) = Some W_16020.
Proof. vm_refl. Qed.
Lemma D_16020 : decode_any W_16020 = Some (Jal 0 2087352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1605c : bv 32 := 0xfc010113.
Lemma F_1605c : fetch_word Ubsan.M.loaded_segments (0x16158 : word) = Some W_1605c.
Proof. vm_refl. Qed.
Lemma D_1605c : decode_any W_1605c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16060 : bv 32 := 0x02113c23.
Lemma F_16060 : fetch_word Ubsan.M.loaded_segments (0x1615c : word) = Some W_16060.
Proof. vm_refl. Qed.
Lemma D_16060 : decode_any W_16060 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16064 : bv 32 := 0x02813823.
Lemma F_16064 : fetch_word Ubsan.M.loaded_segments (0x16160 : word) = Some W_16064.
Proof. vm_refl. Qed.
Lemma D_16064 : decode_any W_16064 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16068 : bv 32 := 0x02913423.
Lemma F_16068 : fetch_word Ubsan.M.loaded_segments (0x16164 : word) = Some W_16068.
Proof. vm_refl. Qed.
Lemma D_16068 : decode_any W_16068 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1606c : bv 32 := 0x03213023.
Lemma F_1606c : fetch_word Ubsan.M.loaded_segments (0x16168 : word) = Some W_1606c.
Proof. vm_refl. Qed.
Lemma D_1606c : decode_any W_1606c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16070 : bv 32 := 0x01313c23.
Lemma F_16070 : fetch_word Ubsan.M.loaded_segments (0x1616c : word) = Some W_16070.
Proof. vm_refl. Qed.
Lemma D_16070 : decode_any W_16070 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16074 : bv 32 := 0x06050263.
Lemma F_16074 : fetch_word Ubsan.M.loaded_segments (0x16170 : word) = Some W_16074.
Proof. vm_refl. Qed.
Lemma D_16074 : decode_any W_16074 = Some (Branch BC_EQ 10 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16078 : bv 32 := 0x00060913.
Lemma F_16078 : fetch_word Ubsan.M.loaded_segments (0x16174 : word) = Some W_16078.
Proof. vm_refl. Qed.
Lemma D_16078 : decode_any W_16078 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1607c : bv 32 := 0x00058993.
Lemma F_1607c : fetch_word Ubsan.M.loaded_segments (0x16178 : word) = Some W_1607c.
Proof. vm_refl. Qed.
Lemma D_1607c : decode_any W_1607c = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16080 : bv 32 := 0x00050413.
Lemma F_16080 : fetch_word Ubsan.M.loaded_segments (0x1617c : word) = Some W_16080.
Proof. vm_refl. Qed.
Lemma D_16080 : decode_any W_16080 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16084 : bv 32 := 0x01410593.
Lemma F_16084 : fetch_word Ubsan.M.loaded_segments (0x16180 : word) = Some W_16084.
Proof. vm_refl. Qed.
Lemma D_16084 : decode_any W_16084 = Some (OpImm ALU_ADD 11 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16088 : bv 32 := 0x01010613.
Lemma F_16088 : fetch_word Ubsan.M.loaded_segments (0x16184 : word) = Some W_16088.
Proof. vm_refl. Qed.
Lemma D_16088 : decode_any W_16088 = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1608c : bv 32 := 0x00c10693.
Lemma F_1608c : fetch_word Ubsan.M.loaded_segments (0x16188 : word) = Some W_1608c.
Proof. vm_refl. Qed.
Lemma D_1608c : decode_any W_1608c = Some (OpImm ALU_ADD 13 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16090 : bv 32 := 0x8b8fe0ef.
Lemma F_16090 : fetch_word Ubsan.M.loaded_segments (0x1618c : word) = Some W_16090.
Proof. vm_refl. Qed.
Lemma D_16090 : decode_any W_16090 = Some (Jal 1 2089144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16094 : bv 32 := 0x00c12503.
Lemma F_16094 : fetch_word Ubsan.M.loaded_segments (0x16190 : word) = Some W_16094.
Proof. vm_refl. Qed.
Lemma D_16094 : decode_any W_16094 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16098 : bv 32 := 0x00800593.
Lemma F_16098 : fetch_word Ubsan.M.loaded_segments (0x16194 : word) = Some W_16098.
Proof. vm_refl. Qed.
Lemma D_16098 : decode_any W_16098 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1609c : bv 32 := 0x08b51063.
Lemma F_1609c : fetch_word Ubsan.M.loaded_segments (0x16198 : word) = Some W_1609c.
Proof. vm_refl. Qed.
Lemma D_1609c : decode_any W_1609c = Some (Branch BC_NE 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160a0 : bv 32 := 0x01396533.
Lemma F_160a0 : fetch_word Ubsan.M.loaded_segments (0x1619c : word) = Some W_160a0.
Proof. vm_refl. Qed.
Lemma D_160a0 : decode_any W_160a0 = Some (Op ALU_OR 10 18 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160a4 : bv 32 := 0x0a054063.
Lemma F_160a4 : fetch_word Ubsan.M.loaded_segments (0x161a0 : word) = Some W_160a4.
Proof. vm_refl. Qed.
Lemma D_160a4 : decode_any W_160a4 = Some (Branch BC_LT 10 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160a8 : bv 32 := 0x01012503.
Lemma F_160a8 : fetch_word Ubsan.M.loaded_segments (0x161a4 : word) = Some W_160a8.
Proof. vm_refl. Qed.
Lemma D_160a8 : decode_any W_160a8 = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160ac : bv 32 := 0x08a9dc63.
Lemma F_160ac : fetch_word Ubsan.M.loaded_segments (0x161a8 : word) = Some W_160ac.
Proof. vm_refl. Qed.
Lemma D_160ac : decode_any W_160ac = Some (Branch BC_GE 19 10 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160b0 : bv 32 := 0x01412583.
Lemma F_160b0 : fetch_word Ubsan.M.loaded_segments (0x161ac : word) = Some W_160b0.
Proof. vm_refl. Qed.
Lemma D_160b0 : decode_any W_160b0 = Some (Load SZ4 true 11 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160b4 : bv 32 := 0x08b95863.
Lemma F_160b4 : fetch_word Ubsan.M.loaded_segments (0x161b0 : word) = Some W_160b4.
Proof. vm_refl. Qed.
Lemma D_160b4 : decode_any W_160b4 = Some (Branch BC_GE 18 11 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160b8 : bv 32 := 0xaedff0ef.
Lemma F_160b8 : fetch_word Ubsan.M.loaded_segments (0x161b4 : word) = Some W_160b8.
Proof. vm_refl. Qed.
Lemma D_160b8 : decode_any W_160b8 = Some (Jal 1 2095852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160bc : bv 32 := 0x00050493.
Lemma F_160bc : fetch_word Ubsan.M.loaded_segments (0x161b8 : word) = Some W_160bc.
Proof. vm_refl. Qed.
Lemma D_160bc : decode_any W_160bc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160c0 : bv 32 := 0x0c050e63.
Lemma F_160c0 : fetch_word Ubsan.M.loaded_segments (0x161bc : word) = Some W_160c0.
Proof. vm_refl. Qed.
Lemma D_160c0 : decode_any W_160c0 = Some (Branch BC_EQ 10 0 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160c4 : bv 32 := 0x0074f513.
Lemma F_160c4 : fetch_word Ubsan.M.loaded_segments (0x161c0 : word) = Some W_160c4.
Proof. vm_refl. Qed.
Lemma D_160c4 : decode_any W_160c4 = Some (OpImm ALU_AND 10 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160c8 : bv 32 := 0x16051263.
Lemma F_160c8 : fetch_word Ubsan.M.loaded_segments (0x161c4 : word) = Some W_160c8.
Proof. vm_refl. Qed.
Lemma D_160c8 : decode_any W_160c8 = Some (Branch BC_NE 10 0 356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160cc : bv 32 := 0x0134a423.
Lemma F_160cc : fetch_word Ubsan.M.loaded_segments (0x161c8 : word) = Some W_160cc.
Proof. vm_refl. Qed.
Lemma D_160cc : decode_any W_160cc = Some (Store SZ4 9 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160d0 : bv 32 := 0x0124a623.
Lemma F_160d0 : fetch_word Ubsan.M.loaded_segments (0x161cc : word) = Some W_160d0.
Proof. vm_refl. Qed.
Lemma D_160d0 : decode_any W_160d0 = Some (Store SZ4 9 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160d4 : bv 32 := 0x0f40006f.
Lemma F_160d4 : fetch_word Ubsan.M.loaded_segments (0x161d0 : word) = Some W_160d4.
Proof. vm_refl. Qed.
Lemma D_160d4 : decode_any W_160d4 = Some (Jal 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1611c : bv 32 := 0x00009517.
Lemma F_1611c : fetch_word Ubsan.M.loaded_segments (0x16218 : word) = Some W_1611c.
Proof. vm_refl. Qed.
Lemma D_1611c : decode_any W_1611c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16120 : bv 32 := 0x7b853503.
Lemma F_16120 : fetch_word Ubsan.M.loaded_segments (0x1621c : word) = Some W_16120.
Proof. vm_refl. Qed.
Lemma D_16120 : decode_any W_16120 = Some (Load SZ8 true 10 10 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16124 : bv 32 := 0x00052503.
Lemma F_16124 : fetch_word Ubsan.M.loaded_segments (0x16220 : word) = Some W_16124.
Proof. vm_refl. Qed.
Lemma D_16124 : decode_any W_16124 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16128 : bv 32 := 0x00500593.
Lemma F_16128 : fetch_word Ubsan.M.loaded_segments (0x16224 : word) = Some W_16128.
Proof. vm_refl. Qed.
Lemma D_16128 : decode_any W_16128 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1612c : bv 32 := 0x04a5c663.
Lemma F_1612c : fetch_word Ubsan.M.loaded_segments (0x16228 : word) = Some W_1612c.
Proof. vm_refl. Qed.
Lemma D_1612c : decode_any W_1612c = Some (Branch BC_LT 11 10 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16130 : bv 32 := 0xffffb517.
Lemma F_16130 : fetch_word Ubsan.M.loaded_segments (0x1622c : word) = Some W_16130.
Proof. vm_refl. Qed.
Lemma D_16130 : decode_any W_16130 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16134 : bv 32 := 0xffffb597.
Lemma F_16134 : fetch_word Ubsan.M.loaded_segments (0x16230 : word) = Some W_16134.
Proof. vm_refl. Qed.
Lemma D_16134 : decode_any W_16134 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16138 : bv 32 := 0x9ca50513.
Lemma F_16138 : fetch_word Ubsan.M.loaded_segments (0x16234 : word) = Some W_16138.
Proof. vm_refl. Qed.
Lemma D_16138 : decode_any W_16138 = Some (OpImm ALU_ADD 10 10 2506, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1613c : bv 32 := 0x93d58593.
Lemma F_1613c : fetch_word Ubsan.M.loaded_segments (0x16238 : word) = Some W_1613c.
Proof. vm_refl. Qed.
Lemma D_1613c : decode_any W_1613c = Some (OpImm ALU_ADD 11 11 2365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16140 : bv 32 := 0x0280006f.
Lemma F_16140 : fetch_word Ubsan.M.loaded_segments (0x1623c : word) = Some W_16140.
Proof. vm_refl. Qed.
Lemma D_16140 : decode_any W_16140 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16144 : bv 32 := 0x00009517.
Lemma F_16144 : fetch_word Ubsan.M.loaded_segments (0x16240 : word) = Some W_16144.
Proof. vm_refl. Qed.
Lemma D_16144 : decode_any W_16144 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16148 : bv 32 := 0x79053503.
Lemma F_16148 : fetch_word Ubsan.M.loaded_segments (0x16244 : word) = Some W_16148.
Proof. vm_refl. Qed.
Lemma D_16148 : decode_any W_16148 = Some (Load SZ8 true 10 10 1936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1614c : bv 32 := 0x00052503.
Lemma F_1614c : fetch_word Ubsan.M.loaded_segments (0x16248 : word) = Some W_1614c.
Proof. vm_refl. Qed.
Lemma D_1614c : decode_any W_1614c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16150 : bv 32 := 0x00500593.
Lemma F_16150 : fetch_word Ubsan.M.loaded_segments (0x1624c : word) = Some W_16150.
Proof. vm_refl. Qed.
Lemma D_16150 : decode_any W_16150 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16154 : bv 32 := 0x02a5c263.
Lemma F_16154 : fetch_word Ubsan.M.loaded_segments (0x16250 : word) = Some W_16154.
Proof. vm_refl. Qed.
Lemma D_16154 : decode_any W_16154 = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16158 : bv 32 := 0xffffb517.
Lemma F_16158 : fetch_word Ubsan.M.loaded_segments (0x16254 : word) = Some W_16158.
Proof. vm_refl. Qed.
Lemma D_16158 : decode_any W_16158 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1615c : bv 32 := 0xffffb597.
Lemma F_1615c : fetch_word Ubsan.M.loaded_segments (0x16258 : word) = Some W_1615c.
Proof. vm_refl. Qed.
Lemma D_1615c : decode_any W_1615c = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16160 : bv 32 := 0x87650513.
Lemma F_16160 : fetch_word Ubsan.M.loaded_segments (0x1625c : word) = Some W_16160.
Proof. vm_refl. Qed.
Lemma D_16160 : decode_any W_16160 = Some (OpImm ALU_ADD 10 10 2166, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16164 : bv 32 := 0x91558593.
Lemma F_16164 : fetch_word Ubsan.M.loaded_segments (0x16260 : word) = Some W_16164.
Proof. vm_refl. Qed.
Lemma D_16164 : decode_any W_16164 = Some (OpImm ALU_ADD 11 11 2325, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16168 : bv 32 := 0x00000613.
Lemma F_16168 : fetch_word Ubsan.M.loaded_segments (0x16264 : word) = Some W_16168.
Proof. vm_refl. Qed.
Lemma D_16168 : decode_any W_16168 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1616c : bv 32 := 0x93dfd0ef.
Lemma F_1616c : fetch_word Ubsan.M.loaded_segments (0x16268 : word) = Some W_1616c.
Proof. vm_refl. Qed.
Lemma D_1616c : decode_any W_1616c = Some (Jal 1 2087228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16170 : bv 32 := 0x00050493.
Lemma F_16170 : fetch_word Ubsan.M.loaded_segments (0x1626c : word) = Some W_16170.
Proof. vm_refl. Qed.
Lemma D_16170 : decode_any W_16170 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16174 : bv 32 := 0x0080006f.
Lemma F_16174 : fetch_word Ubsan.M.loaded_segments (0x16270 : word) = Some W_16174.
Proof. vm_refl. Qed.
Lemma D_16174 : decode_any W_16174 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1617c : bv 32 := 0x00048513.
Lemma F_1617c : fetch_word Ubsan.M.loaded_segments (0x16278 : word) = Some W_1617c.
Proof. vm_refl. Qed.
Lemma D_1617c : decode_any W_1617c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16180 : bv 32 := 0x03813083.
Lemma F_16180 : fetch_word Ubsan.M.loaded_segments (0x1627c : word) = Some W_16180.
Proof. vm_refl. Qed.
Lemma D_16180 : decode_any W_16180 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16184 : bv 32 := 0x03013403.
Lemma F_16184 : fetch_word Ubsan.M.loaded_segments (0x16280 : word) = Some W_16184.
Proof. vm_refl. Qed.
Lemma D_16184 : decode_any W_16184 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16188 : bv 32 := 0x02813483.
Lemma F_16188 : fetch_word Ubsan.M.loaded_segments (0x16284 : word) = Some W_16188.
Proof. vm_refl. Qed.
Lemma D_16188 : decode_any W_16188 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1618c : bv 32 := 0x02013903.
Lemma F_1618c : fetch_word Ubsan.M.loaded_segments (0x16288 : word) = Some W_1618c.
Proof. vm_refl. Qed.
Lemma D_1618c : decode_any W_1618c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16190 : bv 32 := 0x01813983.
Lemma F_16190 : fetch_word Ubsan.M.loaded_segments (0x1628c : word) = Some W_16190.
Proof. vm_refl. Qed.
Lemma D_16190 : decode_any W_16190 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16194 : bv 32 := 0x04010113.
Lemma F_16194 : fetch_word Ubsan.M.loaded_segments (0x16290 : word) = Some W_16194.
Proof. vm_refl. Qed.
Lemma D_16194 : decode_any W_16194 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16198 : bv 32 := 0x00008067.
Lemma F_16198 : fetch_word Ubsan.M.loaded_segments (0x16294 : word) = Some W_16198.
Proof. vm_refl. Qed.
Lemma D_16198 : decode_any W_16198 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1619c : bv 32 := 0x00009517.
Lemma F_1619c : fetch_word Ubsan.M.loaded_segments (0x16298 : word) = Some W_1619c.
Proof. vm_refl. Qed.
Lemma D_1619c : decode_any W_1619c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161a0 : bv 32 := 0x73853503.
Lemma F_161a0 : fetch_word Ubsan.M.loaded_segments (0x1629c : word) = Some W_161a0.
Proof. vm_refl. Qed.
Lemma D_161a0 : decode_any W_161a0 = Some (Load SZ8 true 10 10 1848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161a4 : bv 32 := 0x00052503.
Lemma F_161a4 : fetch_word Ubsan.M.loaded_segments (0x162a0 : word) = Some W_161a4.
Proof. vm_refl. Qed.
Lemma D_161a4 : decode_any W_161a4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161a8 : bv 32 := 0x00500593.
Lemma F_161a8 : fetch_word Ubsan.M.loaded_segments (0x162a4 : word) = Some W_161a8.
Proof. vm_refl. Qed.
Lemma D_161a8 : decode_any W_161a8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161ac : bv 32 := 0x00a5ce63.
Lemma F_161ac : fetch_word Ubsan.M.loaded_segments (0x162a8 : word) = Some W_161ac.
Proof. vm_refl. Qed.
Lemma D_161ac : decode_any W_161ac = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161b0 : bv 32 := 0xffffa517.
Lemma F_161b0 : fetch_word Ubsan.M.loaded_segments (0x162ac : word) = Some W_161b0.
Proof. vm_refl. Qed.
Lemma D_161b0 : decode_any W_161b0 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161b4 : bv 32 := 0xffffa597.
Lemma F_161b4 : fetch_word Ubsan.M.loaded_segments (0x162b0 : word) = Some W_161b4.
Proof. vm_refl. Qed.
Lemma D_161b4 : decode_any W_161b4 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161b8 : bv 32 := 0x14850513.
Lemma F_161b8 : fetch_word Ubsan.M.loaded_segments (0x162b4 : word) = Some W_161b8.
Proof. vm_refl. Qed.
Lemma D_161b8 : decode_any W_161b8 = Some (OpImm ALU_ADD 10 10 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161bc : bv 32 := 0x20758593.
Lemma F_161bc : fetch_word Ubsan.M.loaded_segments (0x162b8 : word) = Some W_161bc.
Proof. vm_refl. Qed.
Lemma D_161bc : decode_any W_161bc = Some (OpImm ALU_ADD 11 11 519, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161c0 : bv 32 := 0x00100613.
Lemma F_161c0 : fetch_word Ubsan.M.loaded_segments (0x162bc : word) = Some W_161c0.
Proof. vm_refl. Qed.
Lemma D_161c0 : decode_any W_161c0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161c4 : bv 32 := 0x815fd0ef.
Lemma F_161c4 : fetch_word Ubsan.M.loaded_segments (0x162c0 : word) = Some W_161c4.
Proof. vm_refl. Qed.
Lemma D_161c4 : decode_any W_161c4 = Some (Jal 1 2086932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161c8 : bv 32 := 0x01012503.
Lemma F_161c8 : fetch_word Ubsan.M.loaded_segments (0x162c4 : word) = Some W_161c8.
Proof. vm_refl. Qed.
Lemma D_161c8 : decode_any W_161c8 = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161cc : bv 32 := 0xfaa058e3.
Lemma F_161cc : fetch_word Ubsan.M.loaded_segments (0x162c8 : word) = Some W_161cc.
Proof. vm_refl. Qed.
Lemma D_161cc : decode_any W_161cc = Some (Branch BC_GE 0 10 8112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161d0 : bv 32 := 0x01412503.
Lemma F_161d0 : fetch_word Ubsan.M.loaded_segments (0x162cc : word) = Some W_161d0.
Proof. vm_refl. Qed.
Lemma D_161d0 : decode_any W_161d0 = Some (Load SZ4 true 10 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161d4 : bv 32 := 0x00000913.
Lemma F_161d4 : fetch_word Ubsan.M.loaded_segments (0x162d0 : word) = Some W_161d4.
Proof. vm_refl. Qed.
Lemma D_161d4 : decode_any W_161d4 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161d8 : bv 32 := 0x0100006f.
Lemma F_161d8 : fetch_word Ubsan.M.loaded_segments (0x162d4 : word) = Some W_161d8.
Proof. vm_refl. Qed.
Lemma D_161d8 : decode_any W_161d8 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161dc : bv 32 := 0x01012583.
Lemma F_161dc : fetch_word Ubsan.M.loaded_segments (0x162d8 : word) = Some W_161dc.
Proof. vm_refl. Qed.
Lemma D_161dc : decode_any W_161dc = Some (Load SZ4 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161e0 : bv 32 := 0x0019091b.
Lemma F_161e0 : fetch_word Ubsan.M.loaded_segments (0x162dc : word) = Some W_161e0.
Proof. vm_refl. Qed.
Lemma D_161e0 : decode_any W_161e0 = Some (OpImm32 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161e4 : bv 32 := 0xf8b95ce3.
Lemma F_161e4 : fetch_word Ubsan.M.loaded_segments (0x162e0 : word) = Some W_161e4.
Proof. vm_refl. Qed.
Lemma D_161e4 : decode_any W_161e4 = Some (Branch BC_GE 18 11 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161e8 : bv 32 := 0xfea05ae3.
Lemma F_161e8 : fetch_word Ubsan.M.loaded_segments (0x162e4 : word) = Some W_161e8.
Proof. vm_refl. Qed.
Lemma D_161e8 : decode_any W_161e8 = Some (Branch BC_GE 0 10 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161ec : bv 32 := 0x00000993.
Lemma F_161ec : fetch_word Ubsan.M.loaded_segments (0x162e8 : word) = Some W_161ec.
Proof. vm_refl. Qed.
Lemma D_161ec : decode_any W_161ec = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161f0 : bv 32 := 0x00810693.
Lemma F_161f0 : fetch_word Ubsan.M.loaded_segments (0x162ec : word) = Some W_161f0.
Proof. vm_refl. Qed.
Lemma D_161f0 : decode_any W_161f0 = Some (OpImm ALU_ADD 13 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161f4 : bv 32 := 0x00040513.
Lemma F_161f4 : fetch_word Ubsan.M.loaded_segments (0x162f0 : word) = Some W_161f4.
Proof. vm_refl. Qed.
Lemma D_161f4 : decode_any W_161f4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161f8 : bv 32 := 0x00098593.
Lemma F_161f8 : fetch_word Ubsan.M.loaded_segments (0x162f4 : word) = Some W_161f8.
Proof. vm_refl. Qed.
Lemma D_161f8 : decode_any W_161f8 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161fc : bv 32 := 0x00090613.
Lemma F_161fc : fetch_word Ubsan.M.loaded_segments (0x162f8 : word) = Some W_161fc.
Proof. vm_refl. Qed.
Lemma D_161fc : decode_any W_161fc = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16200 : bv 32 := 0xbb4fe0ef.
Lemma F_16200 : fetch_word Ubsan.M.loaded_segments (0x162fc : word) = Some W_16200.
Proof. vm_refl. Qed.
Lemma D_16200 : decode_any W_16200 = Some (Jal 1 2089908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16204 : bv 32 := 0x00816503.
Lemma F_16204 : fetch_word Ubsan.M.loaded_segments (0x16300 : word) = Some W_16204.
Proof. vm_refl. Qed.
Lemma D_16204 : decode_any W_16204 = Some (Load SZ4 false 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16208 : bv 32 := 0xd0157553.
Lemma F_16208 : fetch_word Ubsan.M.loaded_segments (0x16304 : word) = Some W_16208.
Proof. vm_refl. Qed.
Lemma D_16208 : decode_any W_16208 = Some (Fcvt FC_S FC_WU 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1620c : bv 32 := 0x00048513.
Lemma F_1620c : fetch_word Ubsan.M.loaded_segments (0x16308 : word) = Some W_1620c.
Proof. vm_refl. Qed.
Lemma D_1620c : decode_any W_1620c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16210 : bv 32 := 0x00090593.
Lemma F_16210 : fetch_word Ubsan.M.loaded_segments (0x1630c : word) = Some W_16210.
Proof. vm_refl. Qed.
Lemma D_16210 : decode_any W_16210 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16214 : bv 32 := 0x00098613.
Lemma F_16214 : fetch_word Ubsan.M.loaded_segments (0x16310 : word) = Some W_16214.
Proof. vm_refl. Qed.
Lemma D_16214 : decode_any W_16214 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16218 : bv 32 := 0xd31ff0ef.
Lemma F_16218 : fetch_word Ubsan.M.loaded_segments (0x16314 : word) = Some W_16218.
Proof. vm_refl. Qed.
Lemma D_16218 : decode_any W_16218 = Some (Jal 1 2096432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1621c : bv 32 := 0x01412503.
Lemma F_1621c : fetch_word Ubsan.M.loaded_segments (0x16318 : word) = Some W_1621c.
Proof. vm_refl. Qed.
Lemma D_1621c : decode_any W_1621c = Some (Load SZ4 true 10 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16220 : bv 32 := 0x0019899b.
Lemma F_16220 : fetch_word Ubsan.M.loaded_segments (0x1631c : word) = Some W_16220.
Proof. vm_refl. Qed.
Lemma D_16220 : decode_any W_16220 = Some (OpImm32 19 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16224 : bv 32 := 0xfca9c6e3.
Lemma F_16224 : fetch_word Ubsan.M.loaded_segments (0x16320 : word) = Some W_16224.
Proof. vm_refl. Qed.
Lemma D_16224 : decode_any W_16224 = Some (Branch BC_LT 19 10 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16228 : bv 32 := 0xfb5ff06f.
Lemma F_16228 : fetch_word Ubsan.M.loaded_segments (0x16324 : word) = Some W_16228.
Proof. vm_refl. Qed.
Lemma D_16228 : decode_any W_16228 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.
