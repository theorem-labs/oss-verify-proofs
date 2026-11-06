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
Definition W_1603c : bv 32 := 0xfe010113.
Lemma F_1603c : fetch_word Plain.M.loaded_segments (0x16138 : word) = Some W_1603c.
Proof. vm_refl. Qed.
Lemma D_1603c : decode_any W_1603c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16040 : bv 32 := 0x00113c23.
Lemma F_16040 : fetch_word Plain.M.loaded_segments (0x1613c : word) = Some W_16040.
Proof. vm_refl. Qed.
Lemma D_16040 : decode_any W_16040 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16044 : bv 32 := 0x00813823.
Lemma F_16044 : fetch_word Plain.M.loaded_segments (0x16140 : word) = Some W_16044.
Proof. vm_refl. Qed.
Lemma D_16044 : decode_any W_16044 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16048 : bv 32 := 0x00913423.
Lemma F_16048 : fetch_word Plain.M.loaded_segments (0x16144 : word) = Some W_16048.
Proof. vm_refl. Qed.
Lemma D_16048 : decode_any W_16048 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1604c : bv 32 := 0x02050a63.
Lemma F_1604c : fetch_word Plain.M.loaded_segments (0x16148 : word) = Some W_1604c.
Proof. vm_refl. Qed.
Lemma D_1604c : decode_any W_1604c = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16050 : bv 32 := 0x00050493.
Lemma F_16050 : fetch_word Plain.M.loaded_segments (0x1614c : word) = Some W_16050.
Proof. vm_refl. Qed.
Lemma D_16050 : decode_any W_16050 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16054 : bv 32 := 0x00052503.
Lemma F_16054 : fetch_word Plain.M.loaded_segments (0x16150 : word) = Some W_16054.
Proof. vm_refl. Qed.
Lemma D_16054 : decode_any W_16054 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16058 : bv 32 := 0x0044a583.
Lemma F_16058 : fetch_word Plain.M.loaded_segments (0x16154 : word) = Some W_16058.
Proof. vm_refl. Qed.
Lemma D_16058 : decode_any W_16058 = Some (Load SZ4 true 11 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1605c : bv 32 := 0x0084a603.
Lemma F_1605c : fetch_word Plain.M.loaded_segments (0x16158 : word) = Some W_1605c.
Proof. vm_refl. Qed.
Lemma D_1605c : decode_any W_1605c = Some (Load SZ4 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16060 : bv 32 := 0x9e1ff0ef.
Lemma F_16060 : fetch_word Plain.M.loaded_segments (0x1615c : word) = Some W_16060.
Proof. vm_refl. Qed.
Lemma D_16060 : decode_any W_16060 = Some (Jal 1 2095584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16064 : bv 32 := 0x04050263.
Lemma F_16064 : fetch_word Plain.M.loaded_segments (0x16160 : word) = Some W_16064.
Proof. vm_refl. Qed.
Lemma D_16064 : decode_any W_16064 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16068 : bv 32 := 0x00050413.
Lemma F_16068 : fetch_word Plain.M.loaded_segments (0x16164 : word) = Some W_16068.
Proof. vm_refl. Qed.
Lemma D_16068 : decode_any W_16068 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1606c : bv 32 := 0x08a48063.
Lemma F_1606c : fetch_word Plain.M.loaded_segments (0x16168 : word) = Some W_1606c.
Proof. vm_refl. Qed.
Lemma D_1606c : decode_any W_1606c = Some (Branch BC_EQ 9 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16070 : bv 32 := 0x00c4a503.
Lemma F_16070 : fetch_word Plain.M.loaded_segments (0x1616c : word) = Some W_16070.
Proof. vm_refl. Qed.
Lemma D_16070 : decode_any W_16070 = Some (Load SZ4 true 10 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16074 : bv 32 := 0x08a05463.
Lemma F_16074 : fetch_word Plain.M.loaded_segments (0x16170 : word) = Some W_16074.
Proof. vm_refl. Qed.
Lemma D_16074 : decode_any W_16074 = Some (Branch BC_GE 0 10 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16078 : bv 32 := 0x00a42623.
Lemma F_16078 : fetch_word Plain.M.loaded_segments (0x16174 : word) = Some W_16078.
Proof. vm_refl. Qed.
Lemma D_16078 : decode_any W_16078 = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1607c : bv 32 := 0x0ac0006f.
Lemma F_1607c : fetch_word Plain.M.loaded_segments (0x16178 : word) = Some W_1607c.
Proof. vm_refl. Qed.
Lemma D_1607c : decode_any W_1607c = Some (Jal 0 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160a8 : bv 32 := 0x00016517.
Lemma F_160a8 : fetch_word Plain.M.loaded_segments (0x161a4 : word) = Some W_160a8.
Proof. vm_refl. Qed.
Lemma D_160a8 : decode_any W_160a8 = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160ac : bv 32 := 0x87453503.
Lemma F_160ac : fetch_word Plain.M.loaded_segments (0x161a8 : word) = Some W_160ac.
Proof. vm_refl. Qed.
Lemma D_160ac : decode_any W_160ac = Some (Load SZ8 true 10 10 2164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160b0 : bv 32 := 0x00052503.
Lemma F_160b0 : fetch_word Plain.M.loaded_segments (0x161ac : word) = Some W_160b0.
Proof. vm_refl. Qed.
Lemma D_160b0 : decode_any W_160b0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160b4 : bv 32 := 0x00500593.
Lemma F_160b4 : fetch_word Plain.M.loaded_segments (0x161b0 : word) = Some W_160b4.
Proof. vm_refl. Qed.
Lemma D_160b4 : decode_any W_160b4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160b8 : bv 32 := 0x02a5c663.
Lemma F_160b8 : fetch_word Plain.M.loaded_segments (0x161b4 : word) = Some W_160b8.
Proof. vm_refl. Qed.
Lemma D_160b8 : decode_any W_160b8 = Some (Branch BC_LT 11 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160bc : bv 32 := 0xffffa517.
Lemma F_160bc : fetch_word Plain.M.loaded_segments (0x161b8 : word) = Some W_160bc.
Proof. vm_refl. Qed.
Lemma D_160bc : decode_any W_160bc = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160c0 : bv 32 := 0xffffb597.
Lemma F_160c0 : fetch_word Plain.M.loaded_segments (0x161bc : word) = Some W_160c0.
Proof. vm_refl. Qed.
Lemma D_160c0 : decode_any W_160c0 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160c4 : bv 32 := 0x39250513.
Lemma F_160c4 : fetch_word Plain.M.loaded_segments (0x161c0 : word) = Some W_160c4.
Proof. vm_refl. Qed.
Lemma D_160c4 : decode_any W_160c4 = Some (OpImm ALU_ADD 10 10 914, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160c8 : bv 32 := 0x06c58593.
Lemma F_160c8 : fetch_word Plain.M.loaded_segments (0x161c4 : word) = Some W_160c8.
Proof. vm_refl. Qed.
Lemma D_160c8 : decode_any W_160c8 = Some (OpImm ALU_ADD 11 11 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160cc : bv 32 := 0x00000613.
Lemma F_160cc : fetch_word Plain.M.loaded_segments (0x161c8 : word) = Some W_160cc.
Proof. vm_refl. Qed.
Lemma D_160cc : decode_any W_160cc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160d0 : bv 32 := 0x01813083.
Lemma F_160d0 : fetch_word Plain.M.loaded_segments (0x161cc : word) = Some W_160d0.
Proof. vm_refl. Qed.
Lemma D_160d0 : decode_any W_160d0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160d4 : bv 32 := 0x01013403.
Lemma F_160d4 : fetch_word Plain.M.loaded_segments (0x161d0 : word) = Some W_160d4.
Proof. vm_refl. Qed.
Lemma D_160d4 : decode_any W_160d4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160d8 : bv 32 := 0x00813483.
Lemma F_160d8 : fetch_word Plain.M.loaded_segments (0x161d4 : word) = Some W_160d8.
Proof. vm_refl. Qed.
Lemma D_160d8 : decode_any W_160d8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160dc : bv 32 := 0x02010113.
Lemma F_160dc : fetch_word Plain.M.loaded_segments (0x161d8 : word) = Some W_160dc.
Proof. vm_refl. Qed.
Lemma D_160dc : decode_any W_160dc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160e0 : bv 32 := 0xd60ff06f.
Lemma F_160e0 : fetch_word Plain.M.loaded_segments (0x161dc : word) = Some W_160e0.
Proof. vm_refl. Qed.
Lemma D_160e0 : decode_any W_160e0 = Some (Jal 0 2094432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16128 : bv 32 := 0x0184b503.
Lemma F_16128 : fetch_word Plain.M.loaded_segments (0x16224 : word) = Some W_16128.
Proof. vm_refl. Qed.
Lemma D_16128 : decode_any W_16128 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1612c : bv 32 := 0x00a43c23.
Lemma F_1612c : fetch_word Plain.M.loaded_segments (0x16228 : word) = Some W_1612c.
Proof. vm_refl. Qed.
Lemma D_1612c : decode_any W_1612c = Some (Store SZ8 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16130 : bv 32 := 0x00040513.
Lemma F_16130 : fetch_word Plain.M.loaded_segments (0x1622c : word) = Some W_16130.
Proof. vm_refl. Qed.
Lemma D_16130 : decode_any W_16130 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16134 : bv 32 := 0x00048593.
Lemma F_16134 : fetch_word Plain.M.loaded_segments (0x16230 : word) = Some W_16134.
Proof. vm_refl. Qed.
Lemma D_16134 : decode_any W_16134 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16138 : bv 32 := 0x214000ef.
Lemma F_16138 : fetch_word Plain.M.loaded_segments (0x16234 : word) = Some W_16138.
Proof. vm_refl. Qed.
Lemma D_16138 : decode_any W_16138 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1613c : bv 32 := 0x0284b583.
Lemma F_1613c : fetch_word Plain.M.loaded_segments (0x16238 : word) = Some W_1613c.
Proof. vm_refl. Qed.
Lemma D_1613c : decode_any W_1613c = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16140 : bv 32 := 0x02840513.
Lemma F_16140 : fetch_word Plain.M.loaded_segments (0x1623c : word) = Some W_16140.
Proof. vm_refl. Qed.
Lemma D_16140 : decode_any W_16140 = Some (OpImm ALU_ADD 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16144 : bv 32 := 0xea4ff0ef.
Lemma F_16144 : fetch_word Plain.M.loaded_segments (0x16240 : word) = Some W_16144.
Proof. vm_refl. Qed.
Lemma D_16144 : decode_any W_16144 = Some (Jal 1 2094756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16148 : bv 32 := 0x0204a503.
Lemma F_16148 : fetch_word Plain.M.loaded_segments (0x16244 : word) = Some W_16148.
Proof. vm_refl. Qed.
Lemma D_16148 : decode_any W_16148 = Some (Load SZ4 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1614c : bv 32 := 0x02a42023.
Lemma F_1614c : fetch_word Plain.M.loaded_segments (0x16248 : word) = Some W_1614c.
Proof. vm_refl. Qed.
Lemma D_1614c : decode_any W_1614c = Some (Store SZ4 8 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16150 : bv 32 := 0x00040513.
Lemma F_16150 : fetch_word Plain.M.loaded_segments (0x1624c : word) = Some W_16150.
Proof. vm_refl. Qed.
Lemma D_16150 : decode_any W_16150 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16154 : bv 32 := 0x00000593.
Lemma F_16154 : fetch_word Plain.M.loaded_segments (0x16250 : word) = Some W_16154.
Proof. vm_refl. Qed.
Lemma D_16154 : decode_any W_16154 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16158 : bv 32 := 0x3b0010ef.
Lemma F_16158 : fetch_word Plain.M.loaded_segments (0x16254 : word) = Some W_16158.
Proof. vm_refl. Qed.
Lemma D_16158 : decode_any W_16158 = Some (Jal 1 5040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1615c : bv 32 := 0x00040513.
Lemma F_1615c : fetch_word Plain.M.loaded_segments (0x16258 : word) = Some W_1615c.
Proof. vm_refl. Qed.
Lemma D_1615c : decode_any W_1615c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16160 : bv 32 := 0x01813083.
Lemma F_16160 : fetch_word Plain.M.loaded_segments (0x1625c : word) = Some W_16160.
Proof. vm_refl. Qed.
Lemma D_16160 : decode_any W_16160 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16164 : bv 32 := 0x01013403.
Lemma F_16164 : fetch_word Plain.M.loaded_segments (0x16260 : word) = Some W_16164.
Proof. vm_refl. Qed.
Lemma D_16164 : decode_any W_16164 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16168 : bv 32 := 0x00813483.
Lemma F_16168 : fetch_word Plain.M.loaded_segments (0x16264 : word) = Some W_16168.
Proof. vm_refl. Qed.
Lemma D_16168 : decode_any W_16168 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1616c : bv 32 := 0x02010113.
Lemma F_1616c : fetch_word Plain.M.loaded_segments (0x16268 : word) = Some W_1616c.
Proof. vm_refl. Qed.
Lemma D_1616c : decode_any W_1616c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16170 : bv 32 := 0x00008067.
Lemma F_16170 : fetch_word Plain.M.loaded_segments (0x1626c : word) = Some W_16170.
Proof. vm_refl. Qed.
Lemma D_16170 : decode_any W_16170 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16174 : bv 32 := 0x00058463.
Lemma F_16174 : fetch_word Plain.M.loaded_segments (0x16270 : word) = Some W_16174.
Proof. vm_refl. Qed.
Lemma D_16174 : decode_any W_16174 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16178 : bv 32 := 0x0005a023.
Lemma F_16178 : fetch_word Plain.M.loaded_segments (0x16274 : word) = Some W_16178.
Proof. vm_refl. Qed.
Lemma D_16178 : decode_any W_16178 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1617c : bv 32 := 0x00060463.
Lemma F_1617c : fetch_word Plain.M.loaded_segments (0x16278 : word) = Some W_1617c.
Proof. vm_refl. Qed.
Lemma D_1617c : decode_any W_1617c = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16180 : bv 32 := 0x00062023.
Lemma F_16180 : fetch_word Plain.M.loaded_segments (0x1627c : word) = Some W_16180.
Proof. vm_refl. Qed.
Lemma D_16180 : decode_any W_16180 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16184 : bv 32 := 0x00068463.
Lemma F_16184 : fetch_word Plain.M.loaded_segments (0x16280 : word) = Some W_16184.
Proof. vm_refl. Qed.
Lemma D_16184 : decode_any W_16184 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16188 : bv 32 := 0x0006a023.
Lemma F_16188 : fetch_word Plain.M.loaded_segments (0x16284 : word) = Some W_16188.
Proof. vm_refl. Qed.
Lemma D_16188 : decode_any W_16188 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1618c : bv 32 := 0x02050a63.
Lemma F_1618c : fetch_word Plain.M.loaded_segments (0x16288 : word) = Some W_1618c.
Proof. vm_refl. Qed.
Lemma D_1618c : decode_any W_1618c = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16190 : bv 32 := 0x00058663.
Lemma F_16190 : fetch_word Plain.M.loaded_segments (0x1628c : word) = Some W_16190.
Proof. vm_refl. Qed.
Lemma D_16190 : decode_any W_16190 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16194 : bv 32 := 0x00052703.
Lemma F_16194 : fetch_word Plain.M.loaded_segments (0x16290 : word) = Some W_16194.
Proof. vm_refl. Qed.
Lemma D_16194 : decode_any W_16194 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16198 : bv 32 := 0x00e5a023.
Lemma F_16198 : fetch_word Plain.M.loaded_segments (0x16294 : word) = Some W_16198.
Proof. vm_refl. Qed.
Lemma D_16198 : decode_any W_16198 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1619c : bv 32 := 0x00060663.
Lemma F_1619c : fetch_word Plain.M.loaded_segments (0x16298 : word) = Some W_1619c.
Proof. vm_refl. Qed.
Lemma D_1619c : decode_any W_1619c = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161a0 : bv 32 := 0x00452583.
Lemma F_161a0 : fetch_word Plain.M.loaded_segments (0x1629c : word) = Some W_161a0.
Proof. vm_refl. Qed.
Lemma D_161a0 : decode_any W_161a0 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161a4 : bv 32 := 0x00b62023.
Lemma F_161a4 : fetch_word Plain.M.loaded_segments (0x162a0 : word) = Some W_161a4.
Proof. vm_refl. Qed.
Lemma D_161a4 : decode_any W_161a4 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161a8 : bv 32 := 0x00000593.
Lemma F_161a8 : fetch_word Plain.M.loaded_segments (0x162a4 : word) = Some W_161a8.
Proof. vm_refl. Qed.
Lemma D_161a8 : decode_any W_161a8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161ac : bv 32 := 0x00068663.
Lemma F_161ac : fetch_word Plain.M.loaded_segments (0x162a8 : word) = Some W_161ac.
Proof. vm_refl. Qed.
Lemma D_161ac : decode_any W_161ac = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161b0 : bv 32 := 0x00852503.
Lemma F_161b0 : fetch_word Plain.M.loaded_segments (0x162ac : word) = Some W_161b0.
Proof. vm_refl. Qed.
Lemma D_161b0 : decode_any W_161b0 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161b4 : bv 32 := 0x00a6a023.
Lemma F_161b4 : fetch_word Plain.M.loaded_segments (0x162b0 : word) = Some W_161b4.
Proof. vm_refl. Qed.
Lemma D_161b4 : decode_any W_161b4 = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161b8 : bv 32 := 0x00058513.
Lemma F_161b8 : fetch_word Plain.M.loaded_segments (0x162b4 : word) = Some W_161b8.
Proof. vm_refl. Qed.
Lemma D_161b8 : decode_any W_161b8 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161bc : bv 32 := 0x00008067.
Lemma F_161bc : fetch_word Plain.M.loaded_segments (0x162b8 : word) = Some W_161bc.
Proof. vm_refl. Qed.
Lemma D_161bc : decode_any W_161bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1634c : bv 32 := 0xfd010113.
Lemma F_1634c : fetch_word Plain.M.loaded_segments (0x16448 : word) = Some W_1634c.
Proof. vm_refl. Qed.
Lemma D_1634c : decode_any W_1634c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16350 : bv 32 := 0x02113423.
Lemma F_16350 : fetch_word Plain.M.loaded_segments (0x1644c : word) = Some W_16350.
Proof. vm_refl. Qed.
Lemma D_16350 : decode_any W_16350 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16354 : bv 32 := 0x02813023.
Lemma F_16354 : fetch_word Plain.M.loaded_segments (0x16450 : word) = Some W_16354.
Proof. vm_refl. Qed.
Lemma D_16354 : decode_any W_16354 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16358 : bv 32 := 0x00913c23.
Lemma F_16358 : fetch_word Plain.M.loaded_segments (0x16454 : word) = Some W_16358.
Proof. vm_refl. Qed.
Lemma D_16358 : decode_any W_16358 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1635c : bv 32 := 0x0e058063.
Lemma F_1635c : fetch_word Plain.M.loaded_segments (0x16458 : word) = Some W_1635c.
Proof. vm_refl. Qed.
Lemma D_1635c : decode_any W_1635c = Some (Branch BC_EQ 11 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16360 : bv 32 := 0x10050263.
Lemma F_16360 : fetch_word Plain.M.loaded_segments (0x1645c : word) = Some W_16360.
Proof. vm_refl. Qed.
Lemma D_16360 : decode_any W_16360 = Some (Branch BC_EQ 10 0 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16364 : bv 32 := 0x0ca58863.
Lemma F_16364 : fetch_word Plain.M.loaded_segments (0x16460 : word) = Some W_16364.
Proof. vm_refl. Qed.
Lemma D_16364 : decode_any W_16364 = Some (Branch BC_EQ 11 10 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16368 : bv 32 := 0x0085a603.
Lemma F_16368 : fetch_word Plain.M.loaded_segments (0x16464 : word) = Some W_16368.
Proof. vm_refl. Qed.
Lemma D_16368 : decode_any W_16368 = Some (Load SZ4 true 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1636c : bv 32 := 0x00852683.
Lemma F_1636c : fetch_word Plain.M.loaded_segments (0x16468 : word) = Some W_1636c.
Proof. vm_refl. Qed.
Lemma D_1636c : decode_any W_1636c = Some (Load SZ4 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16370 : bv 32 := 0x10d61e63.
Lemma F_16370 : fetch_word Plain.M.loaded_segments (0x1646c : word) = Some W_16370.
Proof. vm_refl. Qed.
Lemma D_16370 : decode_any W_16370 = Some (Branch BC_NE 12 13 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16374 : bv 32 := 0x03053603.
Lemma F_16374 : fetch_word Plain.M.loaded_segments (0x16470 : word) = Some W_16374.
Proof. vm_refl. Qed.
Lemma D_16374 : decode_any W_16374 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16378 : bv 32 := 0x00c13823.
Lemma F_16378 : fetch_word Plain.M.loaded_segments (0x16474 : word) = Some W_16378.
Proof. vm_refl. Qed.
Lemma D_16378 : decode_any W_16378 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1637c : bv 32 := 0x02060063.
Lemma F_1637c : fetch_word Plain.M.loaded_segments (0x16478 : word) = Some W_1637c.
Proof. vm_refl. Qed.
Lemma D_1637c : decode_any W_1637c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1639c : bv 32 := 0x0305b403.
Lemma F_1639c : fetch_word Plain.M.loaded_segments (0x16498 : word) = Some W_1639c.
Proof. vm_refl. Qed.
Lemma D_1639c : decode_any W_1639c = Some (Load SZ8 true 8 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163a0 : bv 32 := 0x08040a63.
Lemma F_163a0 : fetch_word Plain.M.loaded_segments (0x1649c : word) = Some W_163a0.
Proof. vm_refl. Qed.
Lemma D_163a0 : decode_any W_163a0 = Some (Branch BC_EQ 8 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163a4 : bv 32 := 0x00050493.
Lemma F_163a4 : fetch_word Plain.M.loaded_segments (0x164a0 : word) = Some W_163a4.
Proof. vm_refl. Qed.
Lemma D_163a4 : decode_any W_163a4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163a8 : bv 32 := 0x00c10613.
Lemma F_163a8 : fetch_word Plain.M.loaded_segments (0x164a4 : word) = Some W_163a8.
Proof. vm_refl. Qed.
Lemma D_163a8 : decode_any W_163a8 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163ac : bv 32 := 0x00040513.
Lemma F_163ac : fetch_word Plain.M.loaded_segments (0x164a8 : word) = Some W_163ac.
Proof. vm_refl. Qed.
Lemma D_163ac : decode_any W_163ac = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163b0 : bv 32 := 0x00000593.
Lemma F_163b0 : fetch_word Plain.M.loaded_segments (0x164ac : word) = Some W_163b0.
Proof. vm_refl. Qed.
Lemma D_163b0 : decode_any W_163b0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163b4 : bv 32 := 0x558020ef.
Lemma F_163b4 : fetch_word Plain.M.loaded_segments (0x164b0 : word) = Some W_163b4.
Proof. vm_refl. Qed.
Lemma D_163b4 : decode_any W_163b4 = Some (Jal 1 9560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163b8 : bv 32 := 0x00c12503.
Lemma F_163b8 : fetch_word Plain.M.loaded_segments (0x164b4 : word) = Some W_163b8.
Proof. vm_refl. Qed.
Lemma D_163b8 : decode_any W_163b8 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163bc : bv 32 := 0x10050663.
Lemma F_163bc : fetch_word Plain.M.loaded_segments (0x164b8 : word) = Some W_163bc.
Proof. vm_refl. Qed.
Lemma D_163bc : decode_any W_163bc = Some (Branch BC_EQ 10 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163c0 : bv 32 := 0x00040513.
Lemma F_163c0 : fetch_word Plain.M.loaded_segments (0x164bc : word) = Some W_163c0.
Proof. vm_refl. Qed.
Lemma D_163c0 : decode_any W_163c0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163c4 : bv 32 := 0x44c020ef.
Lemma F_163c4 : fetch_word Plain.M.loaded_segments (0x164c0 : word) = Some W_163c4.
Proof. vm_refl. Qed.
Lemma D_163c4 : decode_any W_163c4 = Some (Jal 1 9292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163c8 : bv 32 := 0x12050463.
Lemma F_163c8 : fetch_word Plain.M.loaded_segments (0x164c4 : word) = Some W_163c8.
Proof. vm_refl. Qed.
Lemma D_163c8 : decode_any W_163c8 = Some (Branch BC_EQ 10 0 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163cc : bv 32 := 0x00048593.
Lemma F_163cc : fetch_word Plain.M.loaded_segments (0x164c8 : word) = Some W_163cc.
Proof. vm_refl. Qed.
Lemma D_163cc : decode_any W_163cc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163d0 : bv 32 := 0x0304b603.
Lemma F_163d0 : fetch_word Plain.M.loaded_segments (0x164cc : word) = Some W_163d0.
Proof. vm_refl. Qed.
Lemma D_163d0 : decode_any W_163d0 = Some (Load SZ8 true 12 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163d4 : bv 32 := 0x00c13823.
Lemma F_163d4 : fetch_word Plain.M.loaded_segments (0x164d0 : word) = Some W_163d4.
Proof. vm_refl. Qed.
Lemma D_163d4 : decode_any W_163d4 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163d8 : bv 32 := 0x00060c63.
Lemma F_163d8 : fetch_word Plain.M.loaded_segments (0x164d4 : word) = Some W_163d8.
Proof. vm_refl. Qed.
Lemma D_163d8 : decode_any W_163d8 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163f0 : bv 32 := 0x02a5b823.
Lemma F_163f0 : fetch_word Plain.M.loaded_segments (0x164ec : word) = Some W_163f0.
Proof. vm_refl. Qed.
Lemma D_163f0 : decode_any W_163f0 = Some (Store SZ8 11 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163f4 : bv 32 := 0x01010613.
Lemma F_163f4 : fetch_word Plain.M.loaded_segments (0x164f0 : word) = Some W_163f4.
Proof. vm_refl. Qed.
Lemma D_163f4 : decode_any W_163f4 = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163f8 : bv 32 := 0x00000593.
Lemma F_163f8 : fetch_word Plain.M.loaded_segments (0x164f4 : word) = Some W_163f8.
Proof. vm_refl. Qed.
Lemma D_163f8 : decode_any W_163f8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163fc : bv 32 := 0x510020ef.
Lemma F_163fc : fetch_word Plain.M.loaded_segments (0x164f8 : word) = Some W_163fc.
Proof. vm_refl. Qed.
Lemma D_163fc : decode_any W_163fc = Some (Jal 1 9488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16400 : bv 32 := 0x01012503.
Lemma F_16400 : fetch_word Plain.M.loaded_segments (0x164fc : word) = Some W_16400.
Proof. vm_refl. Qed.
Lemma D_16400 : decode_any W_16400 = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16404 : bv 32 := 0x02051863.
Lemma F_16404 : fetch_word Plain.M.loaded_segments (0x16500 : word) = Some W_16404.
Proof. vm_refl. Qed.
Lemma D_16404 : decode_any W_16404 = Some (Branch BC_NE 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16434 : bv 32 := 0x00000513.
Lemma F_16434 : fetch_word Plain.M.loaded_segments (0x16530 : word) = Some W_16434.
Proof. vm_refl. Qed.
Lemma D_16434 : decode_any W_16434 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16438 : bv 32 := 0x0ec0006f.
Lemma F_16438 : fetch_word Plain.M.loaded_segments (0x16534 : word) = Some W_16438.
Proof. vm_refl. Qed.
Lemma D_16438 : decode_any W_16438 = Some (Jal 0 236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164f0 : bv 32 := 0x00015517.
Lemma F_164f0 : fetch_word Plain.M.loaded_segments (0x165ec : word) = Some W_164f0.
Proof. vm_refl. Qed.
Lemma D_164f0 : decode_any W_164f0 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164f4 : bv 32 := 0x42c53503.
Lemma F_164f4 : fetch_word Plain.M.loaded_segments (0x165f0 : word) = Some W_164f4.
Proof. vm_refl. Qed.
Lemma D_164f4 : decode_any W_164f4 = Some (Load SZ8 true 10 10 1068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164f8 : bv 32 := 0x00052503.
Lemma F_164f8 : fetch_word Plain.M.loaded_segments (0x165f4 : word) = Some W_164f8.
Proof. vm_refl. Qed.
Lemma D_164f8 : decode_any W_164f8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164fc : bv 32 := 0x00500593.
Lemma F_164fc : fetch_word Plain.M.loaded_segments (0x165f8 : word) = Some W_164fc.
Proof. vm_refl. Qed.
Lemma D_164fc : decode_any W_164fc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16500 : bv 32 := 0x02a5c063.
Lemma F_16500 : fetch_word Plain.M.loaded_segments (0x165fc : word) = Some W_16500.
Proof. vm_refl. Qed.
Lemma D_16500 : decode_any W_16500 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16504 : bv 32 := 0xffffa517.
Lemma F_16504 : fetch_word Plain.M.loaded_segments (0x16600 : word) = Some W_16504.
Proof. vm_refl. Qed.
Lemma D_16504 : decode_any W_16504 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16508 : bv 32 := 0xffffa597.
Lemma F_16508 : fetch_word Plain.M.loaded_segments (0x16604 : word) = Some W_16508.
Proof. vm_refl. Qed.
Lemma D_16508 : decode_any W_16508 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1650c : bv 32 := 0xf5850513.
Lemma F_1650c : fetch_word Plain.M.loaded_segments (0x16608 : word) = Some W_1650c.
Proof. vm_refl. Qed.
Lemma D_1650c : decode_any W_1650c = Some (OpImm ALU_ADD 10 10 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16510 : bv 32 := 0x04758593.
Lemma F_16510 : fetch_word Plain.M.loaded_segments (0x1660c : word) = Some W_16510.
Proof. vm_refl. Qed.
Lemma D_16510 : decode_any W_16510 = Some (OpImm ALU_ADD 11 11 71, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16514 : bv 32 := 0x00100613.
Lemma F_16514 : fetch_word Plain.M.loaded_segments (0x16610 : word) = Some W_16514.
Proof. vm_refl. Qed.
Lemma D_16514 : decode_any W_16514 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16518 : bv 32 := 0x858ff0ef.
Lemma F_16518 : fetch_word Plain.M.loaded_segments (0x16614 : word) = Some W_16518.
Proof. vm_refl. Qed.
Lemma D_16518 : decode_any W_16518 = Some (Jal 1 2093144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1651c : bv 32 := 0x0080006f.
Lemma F_1651c : fetch_word Plain.M.loaded_segments (0x16618 : word) = Some W_1651c.
Proof. vm_refl. Qed.
Lemma D_1651c : decode_any W_1651c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16524 : bv 32 := 0x02813083.
Lemma F_16524 : fetch_word Plain.M.loaded_segments (0x16620 : word) = Some W_16524.
Proof. vm_refl. Qed.
Lemma D_16524 : decode_any W_16524 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16528 : bv 32 := 0x02013403.
Lemma F_16528 : fetch_word Plain.M.loaded_segments (0x16624 : word) = Some W_16528.
Proof. vm_refl. Qed.
Lemma D_16528 : decode_any W_16528 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1652c : bv 32 := 0x01813483.
Lemma F_1652c : fetch_word Plain.M.loaded_segments (0x16628 : word) = Some W_1652c.
Proof. vm_refl. Qed.
Lemma D_1652c : decode_any W_1652c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16530 : bv 32 := 0x03010113.
Lemma F_16530 : fetch_word Plain.M.loaded_segments (0x1662c : word) = Some W_16530.
Proof. vm_refl. Qed.
Lemma D_16530 : decode_any W_16530 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16534 : bv 32 := 0x00008067.
Lemma F_16534 : fetch_word Plain.M.loaded_segments (0x16630 : word) = Some W_16534.
Proof. vm_refl. Qed.
Lemma D_16534 : decode_any W_16534 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16764 : bv 32 := 0xfd010113.
Lemma F_16764 : fetch_word Plain.M.loaded_segments (0x16860 : word) = Some W_16764.
Proof. vm_refl. Qed.
Lemma D_16764 : decode_any W_16764 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16768 : bv 32 := 0x02113423.
Lemma F_16768 : fetch_word Plain.M.loaded_segments (0x16864 : word) = Some W_16768.
Proof. vm_refl. Qed.
Lemma D_16768 : decode_any W_16768 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1676c : bv 32 := 0x02813023.
Lemma F_1676c : fetch_word Plain.M.loaded_segments (0x16868 : word) = Some W_1676c.
Proof. vm_refl. Qed.
Lemma D_1676c : decode_any W_1676c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16770 : bv 32 := 0x00913c23.
Lemma F_16770 : fetch_word Plain.M.loaded_segments (0x1686c : word) = Some W_16770.
Proof. vm_refl. Qed.
Lemma D_16770 : decode_any W_16770 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16774 : bv 32 := 0x01213823.
Lemma F_16774 : fetch_word Plain.M.loaded_segments (0x16870 : word) = Some W_16774.
Proof. vm_refl. Qed.
Lemma D_16774 : decode_any W_16774 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16778 : bv 32 := 0x01313423.
Lemma F_16778 : fetch_word Plain.M.loaded_segments (0x16874 : word) = Some W_16778.
Proof. vm_refl. Qed.
Lemma D_16778 : decode_any W_16778 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1677c : bv 32 := 0x00050413.
Lemma F_1677c : fetch_word Plain.M.loaded_segments (0x16878 : word) = Some W_1677c.
Proof. vm_refl. Qed.
Lemma D_1677c : decode_any W_1677c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16780 : bv 32 := 0x06058063.
Lemma F_16780 : fetch_word Plain.M.loaded_segments (0x1687c : word) = Some W_16780.
Proof. vm_refl. Qed.
Lemma D_16780 : decode_any W_16780 = Some (Branch BC_EQ 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16784 : bv 32 := 0x00058493.
Lemma F_16784 : fetch_word Plain.M.loaded_segments (0x16880 : word) = Some W_16784.
Proof. vm_refl. Qed.
Lemma D_16784 : decode_any W_16784 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16788 : bv 32 := 0x18858e63.
Lemma F_16788 : fetch_word Plain.M.loaded_segments (0x16884 : word) = Some W_16788.
Proof. vm_refl. Qed.
Lemma D_16788 : decode_any W_16788 = Some (Branch BC_EQ 11 8 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1678c : bv 32 := 0x0044a503.
Lemma F_1678c : fetch_word Plain.M.loaded_segments (0x16888 : word) = Some W_1678c.
Proof. vm_refl. Qed.
Lemma D_1678c : decode_any W_1678c = Some (Load SZ4 true 10 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16790 : bv 32 := 0x0104a583.
Lemma F_16790 : fetch_word Plain.M.loaded_segments (0x1688c : word) = Some W_16790.
Proof. vm_refl. Qed.
Lemma D_16790 : decode_any W_16790 = Some (Load SZ4 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16794 : bv 32 := 0x02a58533.
Lemma F_16794 : fetch_word Plain.M.loaded_segments (0x16890 : word) = Some W_16794.
Proof. vm_refl. Qed.
Lemma D_16794 : decode_any W_16794 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16798 : bv 32 := 0x0025191b.
Lemma F_16798 : fetch_word Plain.M.loaded_segments (0x16894 : word) = Some W_16798.
Proof. vm_refl. Qed.
Lemma D_16798 : decode_any W_16798 = Some (ShiftImm32 ALU_SLL 18 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1679c : bv 32 := 0x08040463.
Lemma F_1679c : fetch_word Plain.M.loaded_segments (0x16898 : word) = Some W_1679c.
Proof. vm_refl. Qed.
Lemma D_1679c : decode_any W_1679c = Some (Branch BC_EQ 8 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167d8 : bv 32 := 0x00000613.
Lemma F_167d8 : fetch_word Plain.M.loaded_segments (0x168d4 : word) = Some W_167d8.
Proof. vm_refl. Qed.
Lemma D_167d8 : decode_any W_167d8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167dc : bv 32 := 0x02c0006f.
Lemma F_167dc : fetch_word Plain.M.loaded_segments (0x168d8 : word) = Some W_167dc.
Proof. vm_refl. Qed.
Lemma D_167dc : decode_any W_167dc = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16808 : bv 32 := 0x02813083.
Lemma F_16808 : fetch_word Plain.M.loaded_segments (0x16904 : word) = Some W_16808.
Proof. vm_refl. Qed.
Lemma D_16808 : decode_any W_16808 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1680c : bv 32 := 0x02013403.
Lemma F_1680c : fetch_word Plain.M.loaded_segments (0x16908 : word) = Some W_1680c.
Proof. vm_refl. Qed.
Lemma D_1680c : decode_any W_1680c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16810 : bv 32 := 0x01813483.
Lemma F_16810 : fetch_word Plain.M.loaded_segments (0x1690c : word) = Some W_16810.
Proof. vm_refl. Qed.
Lemma D_16810 : decode_any W_16810 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16814 : bv 32 := 0x01013903.
Lemma F_16814 : fetch_word Plain.M.loaded_segments (0x16910 : word) = Some W_16814.
Proof. vm_refl. Qed.
Lemma D_16814 : decode_any W_16814 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16818 : bv 32 := 0x00813983.
Lemma F_16818 : fetch_word Plain.M.loaded_segments (0x16914 : word) = Some W_16818.
Proof. vm_refl. Qed.
Lemma D_16818 : decode_any W_16818 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1681c : bv 32 := 0x03010113.
Lemma F_1681c : fetch_word Plain.M.loaded_segments (0x16918 : word) = Some W_1681c.
Proof. vm_refl. Qed.
Lemma D_1681c : decode_any W_1681c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16820 : bv 32 := 0xe21fe06f.
Lemma F_16820 : fetch_word Plain.M.loaded_segments (0x1691c : word) = Some W_16820.
Proof. vm_refl. Qed.
Lemma D_16820 : decode_any W_16820 = Some (Jal 0 2092576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16824 : bv 32 := 0x00048513.
Lemma F_16824 : fetch_word Plain.M.loaded_segments (0x16920 : word) = Some W_16824.
Proof. vm_refl. Qed.
Lemma D_16824 : decode_any W_16824 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16828 : bv 32 := 0x815ff0ef.
Lemma F_16828 : fetch_word Plain.M.loaded_segments (0x16924 : word) = Some W_16828.
Proof. vm_refl. Qed.
Lemma D_16828 : decode_any W_16828 = Some (Jal 1 2095124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1682c : bv 32 := 0x04050263.
Lemma F_1682c : fetch_word Plain.M.loaded_segments (0x16928 : word) = Some W_1682c.
Proof. vm_refl. Qed.
Lemma D_1682c : decode_any W_1682c = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16830 : bv 32 := 0x00050413.
Lemma F_16830 : fetch_word Plain.M.loaded_segments (0x1692c : word) = Some W_16830.
Proof. vm_refl. Qed.
Lemma D_16830 : decode_any W_16830 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16834 : bv 32 := 0x00456583.
Lemma F_16834 : fetch_word Plain.M.loaded_segments (0x16930 : word) = Some W_16834.
Proof. vm_refl. Qed.
Lemma D_16834 : decode_any W_16834 = Some (Load SZ4 false 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16838 : bv 32 := 0x01056603.
Lemma F_16838 : fetch_word Plain.M.loaded_segments (0x16934 : word) = Some W_16838.
Proof. vm_refl. Qed.
Lemma D_16838 : decode_any W_16838 = Some (Load SZ4 false 12 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1683c : bv 32 := 0x03853503.
Lemma F_1683c : fetch_word Plain.M.loaded_segments (0x16938 : word) = Some W_1683c.
Proof. vm_refl. Qed.
Lemma D_1683c : decode_any W_1683c = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16840 : bv 32 := 0x02b60633.
Lemma F_16840 : fetch_word Plain.M.loaded_segments (0x1693c : word) = Some W_16840.
Proof. vm_refl. Qed.
Lemma D_16840 : decode_any W_16840 = Some (Mul M_MUL 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16844 : bv 32 := 0x00261613.
Lemma F_16844 : fetch_word Plain.M.loaded_segments (0x16940 : word) = Some W_16844.
Proof. vm_refl. Qed.
Lemma D_16844 : decode_any W_16844 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16848 : bv 32 := 0x00000593.
Lemma F_16848 : fetch_word Plain.M.loaded_segments (0x16944 : word) = Some W_16848.
Proof. vm_refl. Qed.
Lemma D_16848 : decode_any W_16848 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1684c : bv 32 := 0x285130ef.
Lemma F_1684c : fetch_word Plain.M.loaded_segments (0x16948 : word) = Some W_1684c.
Proof. vm_refl. Qed.
Lemma D_1684c : decode_any W_1684c = Some (Jal 1 80516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16850 : bv 32 := 0x0c40006f.
Lemma F_16850 : fetch_word Plain.M.loaded_segments (0x1694c : word) = Some W_16850.
Proof. vm_refl. Qed.
Lemma D_16850 : decode_any W_16850 = Some (Jal 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16870 : bv 32 := 0x00015517.
Lemma F_16870 : fetch_word Plain.M.loaded_segments (0x1696c : word) = Some W_16870.
Proof. vm_refl. Qed.
Lemma D_16870 : decode_any W_16870 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16874 : bv 32 := 0x0ac53983.
Lemma F_16874 : fetch_word Plain.M.loaded_segments (0x16970 : word) = Some W_16874.
Proof. vm_refl. Qed.
Lemma D_16874 : decode_any W_16874 = Some (Load SZ8 true 19 10 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16878 : bv 32 := 0x0009a503.
Lemma F_16878 : fetch_word Plain.M.loaded_segments (0x16974 : word) = Some W_16878.
Proof. vm_refl. Qed.
Lemma D_16878 : decode_any W_16878 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1687c : bv 32 := 0x00600593.
Lemma F_1687c : fetch_word Plain.M.loaded_segments (0x16978 : word) = Some W_1687c.
Proof. vm_refl. Qed.
Lemma D_1687c : decode_any W_1687c = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16880 : bv 32 := 0x04b55263.
Lemma F_16880 : fetch_word Plain.M.loaded_segments (0x1697c : word) = Some W_16880.
Proof. vm_refl. Qed.
Lemma D_16880 : decode_any W_16880 = Some (Branch BC_GE 10 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16884 : bv 32 := 0xffffa517.
Lemma F_16884 : fetch_word Plain.M.loaded_segments (0x16980 : word) = Some W_16884.
Proof. vm_refl. Qed.
Lemma D_16884 : decode_any W_16884 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16888 : bv 32 := 0xffffa597.
Lemma F_16888 : fetch_word Plain.M.loaded_segments (0x16984 : word) = Some W_16888.
Proof. vm_refl. Qed.
Lemma D_16888 : decode_any W_16888 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1688c : bv 32 := 0xbca50513.
Lemma F_1688c : fetch_word Plain.M.loaded_segments (0x16988 : word) = Some W_1688c.
Proof. vm_refl. Qed.
Lemma D_1688c : decode_any W_1688c = Some (OpImm ALU_ADD 10 10 3018, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16890 : bv 32 := 0x5a858593.
Lemma F_16890 : fetch_word Plain.M.loaded_segments (0x1698c : word) = Some W_16890.
Proof. vm_refl. Qed.
Lemma D_16890 : decode_any W_16890 = Some (OpImm ALU_ADD 11 11 1448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16894 : bv 32 := 0x00000613.
Lemma F_16894 : fetch_word Plain.M.loaded_segments (0x16990 : word) = Some W_16894.
Proof. vm_refl. Qed.
Lemma D_16894 : decode_any W_16894 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16898 : bv 32 := 0xda9fe0ef.
Lemma F_16898 : fetch_word Plain.M.loaded_segments (0x16994 : word) = Some W_16898.
Proof. vm_refl. Qed.
Lemma D_16898 : decode_any W_16898 = Some (Jal 1 2092456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1689c : bv 32 := 0x00050413.
Lemma F_1689c : fetch_word Plain.M.loaded_segments (0x16998 : word) = Some W_1689c.
Proof. vm_refl. Qed.
Lemma D_1689c : decode_any W_1689c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_168a0 : bv 32 := 0x06051a63.
Lemma F_168a0 : fetch_word Plain.M.loaded_segments (0x1699c : word) = Some W_168a0.
Proof. vm_refl. Qed.
Lemma D_168a0 : decode_any W_168a0 = Some (Branch BC_NE 10 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_168a4 : bv 32 := 0x0009a503.
Lemma F_168a4 : fetch_word Plain.M.loaded_segments (0x169a0 : word) = Some W_168a4.
Proof. vm_refl. Qed.
Lemma D_168a4 : decode_any W_168a4 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_168a8 : bv 32 := 0x00500593.
Lemma F_168a8 : fetch_word Plain.M.loaded_segments (0x169a4 : word) = Some W_168a8.
Proof. vm_refl. Qed.
Lemma D_168a8 : decode_any W_168a8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_168ac : bv 32 := 0x00a5cc63.
Lemma F_168ac : fetch_word Plain.M.loaded_segments (0x169a8 : word) = Some W_168ac.
Proof. vm_refl. Qed.
Lemma D_168ac : decode_any W_168ac = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_168b0 : bv 32 := 0xffffa517.
Lemma F_168b0 : fetch_word Plain.M.loaded_segments (0x169ac : word) = Some W_168b0.
Proof. vm_refl. Qed.
Lemma D_168b0 : decode_any W_168b0 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_168b4 : bv 32 := 0xffffa597.
Lemma F_168b4 : fetch_word Plain.M.loaded_segments (0x169b0 : word) = Some W_168b4.
Proof. vm_refl. Qed.
Lemma D_168b4 : decode_any W_168b4 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_168b8 : bv 32 := 0xb9e50513.
Lemma F_168b8 : fetch_word Plain.M.loaded_segments (0x169b4 : word) = Some W_168b8.
Proof. vm_refl. Qed.
Lemma D_168b8 : decode_any W_168b8 = Some (OpImm ALU_ADD 10 10 2974, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_168bc : bv 32 := 0x53158593.
Lemma F_168bc : fetch_word Plain.M.loaded_segments (0x169b8 : word) = Some W_168bc.
Proof. vm_refl. Qed.
Lemma D_168bc : decode_any W_168bc = Some (OpImm ALU_ADD 11 11 1329, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_168c0 : bv 32 := 0xf19ff06f.
Lemma F_168c0 : fetch_word Plain.M.loaded_segments (0x169bc : word) = Some W_168c0.
Proof. vm_refl. Qed.
Lemma D_168c0 : decode_any W_168c0 = Some (Jal 0 2096920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16914 : bv 32 := 0x03843503.
Lemma F_16914 : fetch_word Plain.M.loaded_segments (0x16a10 : word) = Some W_16914.
Proof. vm_refl. Qed.
Lemma D_16914 : decode_any W_16914 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16918 : bv 32 := 0x0384b583.
Lemma F_16918 : fetch_word Plain.M.loaded_segments (0x16a14 : word) = Some W_16918.
Proof. vm_refl. Qed.
Lemma D_16918 : decode_any W_16918 = Some (Load SZ8 true 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1691c : bv 32 := 0x00090613.
Lemma F_1691c : fetch_word Plain.M.loaded_segments (0x16a18 : word) = Some W_1691c.
Proof. vm_refl. Qed.
Lemma D_1691c : decode_any W_1691c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16920 : bv 32 := 0x5ac130ef.
Lemma F_16920 : fetch_word Plain.M.loaded_segments (0x16a1c : word) = Some W_16920.
Proof. vm_refl. Qed.
Lemma D_16920 : decode_any W_16920 = Some (Jal 1 79276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16924 : bv 32 := 0x00040513.
Lemma F_16924 : fetch_word Plain.M.loaded_segments (0x16a20 : word) = Some W_16924.
Proof. vm_refl. Qed.
Lemma D_16924 : decode_any W_16924 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16928 : bv 32 := 0x02813083.
Lemma F_16928 : fetch_word Plain.M.loaded_segments (0x16a24 : word) = Some W_16928.
Proof. vm_refl. Qed.
Lemma D_16928 : decode_any W_16928 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1692c : bv 32 := 0x02013403.
Lemma F_1692c : fetch_word Plain.M.loaded_segments (0x16a28 : word) = Some W_1692c.
Proof. vm_refl. Qed.
Lemma D_1692c : decode_any W_1692c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16930 : bv 32 := 0x01813483.
Lemma F_16930 : fetch_word Plain.M.loaded_segments (0x16a2c : word) = Some W_16930.
Proof. vm_refl. Qed.
Lemma D_16930 : decode_any W_16930 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16934 : bv 32 := 0x01013903.
Lemma F_16934 : fetch_word Plain.M.loaded_segments (0x16a30 : word) = Some W_16934.
Proof. vm_refl. Qed.
Lemma D_16934 : decode_any W_16934 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16938 : bv 32 := 0x00813983.
Lemma F_16938 : fetch_word Plain.M.loaded_segments (0x16a34 : word) = Some W_16938.
Proof. vm_refl. Qed.
Lemma D_16938 : decode_any W_16938 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1693c : bv 32 := 0x03010113.
Lemma F_1693c : fetch_word Plain.M.loaded_segments (0x16a38 : word) = Some W_1693c.
Proof. vm_refl. Qed.
Lemma D_1693c : decode_any W_1693c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16940 : bv 32 := 0x00008067.
Lemma F_16940 : fetch_word Plain.M.loaded_segments (0x16a3c : word) = Some W_16940.
Proof. vm_refl. Qed.
Lemma D_16940 : decode_any W_16940 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
