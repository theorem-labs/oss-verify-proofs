(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_19094 : bv 32 := 0xfd010113.
Lemma F_19094 : fetch_word Plain.M.loaded_segments (0x190ec : word) = Some W_19094.
Proof. vm_refl. Qed.
Lemma D_19094 : decode_any W_19094 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19098 : bv 32 := 0x02113423.
Lemma F_19098 : fetch_word Plain.M.loaded_segments (0x190f0 : word) = Some W_19098.
Proof. vm_refl. Qed.
Lemma D_19098 : decode_any W_19098 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1909c : bv 32 := 0x02813023.
Lemma F_1909c : fetch_word Plain.M.loaded_segments (0x190f4 : word) = Some W_1909c.
Proof. vm_refl. Qed.
Lemma D_1909c : decode_any W_1909c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190a0 : bv 32 := 0x00913c23.
Lemma F_190a0 : fetch_word Plain.M.loaded_segments (0x190f8 : word) = Some W_190a0.
Proof. vm_refl. Qed.
Lemma D_190a0 : decode_any W_190a0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190a4 : bv 32 := 0x01213823.
Lemma F_190a4 : fetch_word Plain.M.loaded_segments (0x190fc : word) = Some W_190a4.
Proof. vm_refl. Qed.
Lemma D_190a4 : decode_any W_190a4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190a8 : bv 32 := 0x01313423.
Lemma F_190a8 : fetch_word Plain.M.loaded_segments (0x19100 : word) = Some W_190a8.
Proof. vm_refl. Qed.
Lemma D_190a8 : decode_any W_190a8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190ac : bv 32 := 0x01413023.
Lemma F_190ac : fetch_word Plain.M.loaded_segments (0x19104 : word) = Some W_190ac.
Proof. vm_refl. Qed.
Lemma D_190ac : decode_any W_190ac = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190b0 : bv 32 := 0x02000693.
Lemma F_190b0 : fetch_word Plain.M.loaded_segments (0x19108 : word) = Some W_190b0.
Proof. vm_refl. Qed.
Lemma D_190b0 : decode_any W_190b0 = Some (OpImm ALU_ADD 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190b4 : bv 32 := 0x14c6ea63.
Lemma F_190b4 : fetch_word Plain.M.loaded_segments (0x1910c : word) = Some W_190b4.
Proof. vm_refl. Qed.
Lemma D_190b4 : decode_any W_190b4 = Some (Branch BC_LTU 13 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190b8 : bv 32 := 0x101016b7.
Lemma F_190b8 : fetch_word Plain.M.loaded_segments (0x19110 : word) = Some W_190b8.
Proof. vm_refl. Qed.
Lemma D_190b8 : decode_any W_190b8 = Some (Lui 13 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190bc : bv 32 := 0x00469693.
Lemma F_190bc : fetch_word Plain.M.loaded_segments (0x19114 : word) = Some W_190bc.
Proof. vm_refl. Qed.
Lemma D_190bc : decode_any W_190bc = Some (ShiftImm ALU_SLL 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190c0 : bv 32 := 0x11668693.
Lemma F_190c0 : fetch_word Plain.M.loaded_segments (0x19118 : word) = Some W_190c0.
Proof. vm_refl. Qed.
Lemma D_190c0 : decode_any W_190c0 = Some (OpImm ALU_ADD 13 13 278, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190c4 : bv 32 := 0x00c6d6b3.
Lemma F_190c4 : fetch_word Plain.M.loaded_segments (0x1911c : word) = Some W_190c4.
Proof. vm_refl. Qed.
Lemma D_190c4 : decode_any W_190c4 = Some (Op ALU_SRL 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190c8 : bv 32 := 0x0016f693.
Lemma F_190c8 : fetch_word Plain.M.loaded_segments (0x19120 : word) = Some W_190c8.
Proof. vm_refl. Qed.
Lemma D_190c8 : decode_any W_190c8 = Some (OpImm ALU_AND 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190cc : bv 32 := 0x12068e63.
Lemma F_190cc : fetch_word Plain.M.loaded_segments (0x19124 : word) = Some W_190cc.
Proof. vm_refl. Qed.
Lemma D_190cc : decode_any W_190cc = Some (Branch BC_EQ 13 0 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190d0 : bv 32 := 0x06a05a63.
Lemma F_190d0 : fetch_word Plain.M.loaded_segments (0x19128 : word) = Some W_190d0.
Proof. vm_refl. Qed.
Lemma D_190d0 : decode_any W_190d0 = Some (Branch BC_GE 0 10 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190d4 : bv 32 := 0x08b05c63.
Lemma F_190d4 : fetch_word Plain.M.loaded_segments (0x1912c : word) = Some W_190d4.
Proof. vm_refl. Qed.
Lemma D_190d4 : decode_any W_190d4 = Some (Branch BC_GE 0 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190d8 : bv 32 := 0x02a606b3.
Lemma F_190d8 : fetch_word Plain.M.loaded_segments (0x19130 : word) = Some W_190d8.
Proof. vm_refl. Qed.
Lemma D_190d8 : decode_any W_190d8 = Some (Mul M_MUL 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190dc : bv 32 := 0x20000737.
Lemma F_190dc : fetch_word Plain.M.loaded_segments (0x19134 : word) = Some W_190dc.
Proof. vm_refl. Qed.
Lemma D_190dc : decode_any W_190dc = Some (Lui 14 131072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190e0 : bv 32 := 0xfe17071b.
Lemma F_190e0 : fetch_word Plain.M.loaded_segments (0x19138 : word) = Some W_190e0.
Proof. vm_refl. Qed.
Lemma D_190e0 : decode_any W_190e0 = Some (OpImm32 14 14 4065, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190e4 : bv 32 := 0x0ae6e863.
Lemma F_190e4 : fetch_word Plain.M.loaded_segments (0x1913c : word) = Some W_190e4.
Proof. vm_refl. Qed.
Lemma D_190e4 : decode_any W_190e4 = Some (Branch BC_LTU 13 14 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19194 : bv 32 := 0x01f68693.
Lemma F_19194 : fetch_word Plain.M.loaded_segments (0x191ec : word) = Some W_19194.
Proof. vm_refl. Qed.
Lemma D_19194 : decode_any W_19194 = Some (OpImm ALU_ADD 13 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19198 : bv 32 := 0x0056d413.
Lemma F_19198 : fetch_word Plain.M.loaded_segments (0x191f0 : word) = Some W_19198.
Proof. vm_refl. Qed.
Lemma D_19198 : decode_any W_19198 = Some (ShiftImm ALU_SRL 8 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1919c : bv 32 := 0x02b406b3.
Lemma F_1919c : fetch_word Plain.M.loaded_segments (0x191f4 : word) = Some W_1919c.
Proof. vm_refl. Qed.
Lemma D_1919c : decode_any W_1919c = Some (Mul M_MUL 13 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_191a0 : bv 32 := 0x00269693.
Lemma F_191a0 : fetch_word Plain.M.loaded_segments (0x191f8 : word) = Some W_191a0.
Proof. vm_refl. Qed.
Lemma D_191a0 : decode_any W_191a0 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_191a4 : bv 32 := 0x01f6d713.
Lemma F_191a4 : fetch_word Plain.M.loaded_segments (0x191fc : word) = Some W_191a4.
Proof. vm_refl. Qed.
Lemma D_191a4 : decode_any W_191a4 = Some (ShiftImm ALU_SRL 14 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_191a8 : bv 32 := 0x0a070463.
Lemma F_191a8 : fetch_word Plain.M.loaded_segments (0x19200 : word) = Some W_191a8.
Proof. vm_refl. Qed.
Lemma D_191a8 : decode_any W_191a8 = Some (Branch BC_EQ 14 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19208 : bv 32 := 0x0001f517.
Lemma F_19208 : fetch_word Plain.M.loaded_segments (0x19260 : word) = Some W_19208.
Proof. vm_refl. Qed.
Lemma D_19208 : decode_any W_19208 = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1920c : bv 32 := 0x21053503.
Lemma F_1920c : fetch_word Plain.M.loaded_segments (0x19264 : word) = Some W_1920c.
Proof. vm_refl. Qed.
Lemma D_1920c : decode_any W_1920c = Some (Load SZ8 true 10 10 528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19210 : bv 32 := 0x00052503.
Lemma F_19210 : fetch_word Plain.M.loaded_segments (0x19268 : word) = Some W_19210.
Proof. vm_refl. Qed.
Lemma D_19210 : decode_any W_19210 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19214 : bv 32 := 0x00500593.
Lemma F_19214 : fetch_word Plain.M.loaded_segments (0x1926c : word) = Some W_19214.
Proof. vm_refl. Qed.
Lemma D_19214 : decode_any W_19214 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19218 : bv 32 := 0x0ca5c663.
Lemma F_19218 : fetch_word Plain.M.loaded_segments (0x19270 : word) = Some W_19218.
Proof. vm_refl. Qed.
Lemma D_19218 : decode_any W_19218 = Some (Branch BC_LT 11 10 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1921c : bv 32 := 0xffff7517.
Lemma F_1921c : fetch_word Plain.M.loaded_segments (0x19274 : word) = Some W_1921c.
Proof. vm_refl. Qed.
Lemma D_1921c : decode_any W_1921c = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19220 : bv 32 := 0xffff8597.
Lemma F_19220 : fetch_word Plain.M.loaded_segments (0x19278 : word) = Some W_19220.
Proof. vm_refl. Qed.
Lemma D_19220 : decode_any W_19220 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19224 : bv 32 := 0x63850513.
Lemma F_19224 : fetch_word Plain.M.loaded_segments (0x1927c : word) = Some W_19224.
Proof. vm_refl. Qed.
Lemma D_19224 : decode_any W_19224 = Some (OpImm ALU_ADD 10 10 1592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19228 : bv 32 := 0xd6758593.
Lemma F_19228 : fetch_word Plain.M.loaded_segments (0x19280 : word) = Some W_19228.
Proof. vm_refl. Qed.
Lemma D_19228 : decode_any W_19228 = Some (OpImm ALU_ADD 11 11 3431, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1922c : bv 32 := 0x00000613.
Lemma F_1922c : fetch_word Plain.M.loaded_segments (0x19284 : word) = Some W_1922c.
Proof. vm_refl. Qed.
Lemma D_1922c : decode_any W_1922c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19230 : bv 32 := 0x02813083.
Lemma F_19230 : fetch_word Plain.M.loaded_segments (0x19288 : word) = Some W_19230.
Proof. vm_refl. Qed.
Lemma D_19230 : decode_any W_19230 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19234 : bv 32 := 0x02013403.
Lemma F_19234 : fetch_word Plain.M.loaded_segments (0x1928c : word) = Some W_19234.
Proof. vm_refl. Qed.
Lemma D_19234 : decode_any W_19234 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19238 : bv 32 := 0x01813483.
Lemma F_19238 : fetch_word Plain.M.loaded_segments (0x19290 : word) = Some W_19238.
Proof. vm_refl. Qed.
Lemma D_19238 : decode_any W_19238 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1923c : bv 32 := 0x01013903.
Lemma F_1923c : fetch_word Plain.M.loaded_segments (0x19294 : word) = Some W_1923c.
Proof. vm_refl. Qed.
Lemma D_1923c : decode_any W_1923c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19240 : bv 32 := 0x00813983.
Lemma F_19240 : fetch_word Plain.M.loaded_segments (0x19298 : word) = Some W_19240.
Proof. vm_refl. Qed.
Lemma D_19240 : decode_any W_19240 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19244 : bv 32 := 0x00013a03.
Lemma F_19244 : fetch_word Plain.M.loaded_segments (0x1929c : word) = Some W_19244.
Proof. vm_refl. Qed.
Lemma D_19244 : decode_any W_19244 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19248 : bv 32 := 0x03010113.
Lemma F_19248 : fetch_word Plain.M.loaded_segments (0x192a0 : word) = Some W_19248.
Proof. vm_refl. Qed.
Lemma D_19248 : decode_any W_19248 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1924c : bv 32 := 0x9d1fe06f.
Lemma F_1924c : fetch_word Plain.M.loaded_segments (0x192a4 : word) = Some W_1924c.
Proof. vm_refl. Qed.
Lemma D_1924c : decode_any W_1924c = Some (Jal 0 2091472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19250 : bv 32 := 0x04000737.
Lemma F_19250 : fetch_word Plain.M.loaded_segments (0x192a8 : word) = Some W_19250.
Proof. vm_refl. Qed.
Lemma D_19250 : decode_any W_19250 = Some (Lui 14 16384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19254 : bv 32 := 0x0017071b.
Lemma F_19254 : fetch_word Plain.M.loaded_segments (0x192ac : word) = Some W_19254.
Proof. vm_refl. Qed.
Lemma D_19254 : decode_any W_19254 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19258 : bv 32 := 0x02e6e663.
Lemma F_19258 : fetch_word Plain.M.loaded_segments (0x192b0 : word) = Some W_19258.
Proof. vm_refl. Qed.
Lemma D_19258 : decode_any W_19258 = Some (Branch BC_LTU 13 14 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1925c : bv 32 := 0x0001f517.
Lemma F_1925c : fetch_word Plain.M.loaded_segments (0x192b4 : word) = Some W_1925c.
Proof. vm_refl. Qed.
Lemma D_1925c : decode_any W_1925c = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19260 : bv 32 := 0x1bc53503.
Lemma F_19260 : fetch_word Plain.M.loaded_segments (0x192b8 : word) = Some W_19260.
Proof. vm_refl. Qed.
Lemma D_19260 : decode_any W_19260 = Some (Load SZ8 true 10 10 444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19264 : bv 32 := 0x00052503.
Lemma F_19264 : fetch_word Plain.M.loaded_segments (0x192bc : word) = Some W_19264.
Proof. vm_refl. Qed.
Lemma D_19264 : decode_any W_19264 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19268 : bv 32 := 0x00500593.
Lemma F_19268 : fetch_word Plain.M.loaded_segments (0x192c0 : word) = Some W_19268.
Proof. vm_refl. Qed.
Lemma D_19268 : decode_any W_19268 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1926c : bv 32 := 0x06a5cc63.
Lemma F_1926c : fetch_word Plain.M.loaded_segments (0x192c4 : word) = Some W_1926c.
Proof. vm_refl. Qed.
Lemma D_1926c : decode_any W_1926c = Some (Branch BC_LT 11 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19270 : bv 32 := 0xffff7517.
Lemma F_19270 : fetch_word Plain.M.loaded_segments (0x192c8 : word) = Some W_19270.
Proof. vm_refl. Qed.
Lemma D_19270 : decode_any W_19270 = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19274 : bv 32 := 0xffff8597.
Lemma F_19274 : fetch_word Plain.M.loaded_segments (0x192cc : word) = Some W_19274.
Proof. vm_refl. Qed.
Lemma D_19274 : decode_any W_19274 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19278 : bv 32 := 0x31b50513.
Lemma F_19278 : fetch_word Plain.M.loaded_segments (0x192d0 : word) = Some W_19278.
Proof. vm_refl. Qed.
Lemma D_19278 : decode_any W_19278 = Some (OpImm ALU_ADD 10 10 795, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1927c : bv 32 := 0xd1358593.
Lemma F_1927c : fetch_word Plain.M.loaded_segments (0x192d4 : word) = Some W_1927c.
Proof. vm_refl. Qed.
Lemma D_1927c : decode_any W_1927c = Some (OpImm ALU_ADD 11 11 3347, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19280 : bv 32 := 0x0600006f.
Lemma F_19280 : fetch_word Plain.M.loaded_segments (0x192d8 : word) = Some W_19280.
Proof. vm_refl. Qed.
Lemma D_19280 : decode_any W_19280 = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19284 : bv 32 := 0x000056b7.
Lemma F_19284 : fetch_word Plain.M.loaded_segments (0x192dc : word) = Some W_19284.
Proof. vm_refl. Qed.
Lemma D_19284 : decode_any W_19284 = Some (Lui 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19288 : bv 32 := 0xe216869b.
Lemma F_19288 : fetch_word Plain.M.loaded_segments (0x192e0 : word) = Some W_19288.
Proof. vm_refl. Qed.
Lemma D_19288 : decode_any W_19288 = Some (OpImm32 13 13 3617, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1928c : bv 32 := 0x02d56663.
Lemma F_1928c : fetch_word Plain.M.loaded_segments (0x192e4 : word) = Some W_1928c.
Proof. vm_refl. Qed.
Lemma D_1928c : decode_any W_1928c = Some (Branch BC_LTU 10 13 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19290 : bv 32 := 0x0001f517.
Lemma F_19290 : fetch_word Plain.M.loaded_segments (0x192e8 : word) = Some W_19290.
Proof. vm_refl. Qed.
Lemma D_19290 : decode_any W_19290 = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19294 : bv 32 := 0x18853503.
Lemma F_19294 : fetch_word Plain.M.loaded_segments (0x192ec : word) = Some W_19294.
Proof. vm_refl. Qed.
Lemma D_19294 : decode_any W_19294 = Some (Load SZ8 true 10 10 392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19298 : bv 32 := 0x00052503.
Lemma F_19298 : fetch_word Plain.M.loaded_segments (0x192f0 : word) = Some W_19298.
Proof. vm_refl. Qed.
Lemma D_19298 : decode_any W_19298 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1929c : bv 32 := 0x00500593.
Lemma F_1929c : fetch_word Plain.M.loaded_segments (0x192f4 : word) = Some W_1929c.
Proof. vm_refl. Qed.
Lemma D_1929c : decode_any W_1929c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192a0 : bv 32 := 0x04a5c263.
Lemma F_192a0 : fetch_word Plain.M.loaded_segments (0x192f8 : word) = Some W_192a0.
Proof. vm_refl. Qed.
Lemma D_192a0 : decode_any W_192a0 = Some (Branch BC_LT 11 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192a4 : bv 32 := 0xffff9517.
Lemma F_192a4 : fetch_word Plain.M.loaded_segments (0x192fc : word) = Some W_192a4.
Proof. vm_refl. Qed.
Lemma D_192a4 : decode_any W_192a4 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192a8 : bv 32 := 0xffff8597.
Lemma F_192a8 : fetch_word Plain.M.loaded_segments (0x19300 : word) = Some W_192a8.
Proof. vm_refl. Qed.
Lemma D_192a8 : decode_any W_192a8 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192ac : bv 32 := 0xced50513.
Lemma F_192ac : fetch_word Plain.M.loaded_segments (0x19304 : word) = Some W_192ac.
Proof. vm_refl. Qed.
Lemma D_192ac : decode_any W_192ac = Some (OpImm ALU_ADD 10 10 3309, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192b0 : bv 32 := 0xcdf58593.
Lemma F_192b0 : fetch_word Plain.M.loaded_segments (0x19308 : word) = Some W_192b0.
Proof. vm_refl. Qed.
Lemma D_192b0 : decode_any W_192b0 = Some (OpImm ALU_ADD 11 11 3295, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192b4 : bv 32 := 0x02c0006f.
Lemma F_192b4 : fetch_word Plain.M.loaded_segments (0x1930c : word) = Some W_192b4.
Proof. vm_refl. Qed.
Lemma D_192b4 : decode_any W_192b4 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192b8 : bv 32 := 0x04d5e863.
Lemma F_192b8 : fetch_word Plain.M.loaded_segments (0x19310 : word) = Some W_192b8.
Proof. vm_refl. Qed.
Lemma D_192b8 : decode_any W_192b8 = Some (Branch BC_LTU 11 13 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192bc : bv 32 := 0x0001f517.
Lemma F_192bc : fetch_word Plain.M.loaded_segments (0x19314 : word) = Some W_192bc.
Proof. vm_refl. Qed.
Lemma D_192bc : decode_any W_192bc = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192c0 : bv 32 := 0x15c53503.
Lemma F_192c0 : fetch_word Plain.M.loaded_segments (0x19318 : word) = Some W_192c0.
Proof. vm_refl. Qed.
Lemma D_192c0 : decode_any W_192c0 = Some (Load SZ8 true 10 10 348, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192c4 : bv 32 := 0x00052503.
Lemma F_192c4 : fetch_word Plain.M.loaded_segments (0x1931c : word) = Some W_192c4.
Proof. vm_refl. Qed.
Lemma D_192c4 : decode_any W_192c4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192c8 : bv 32 := 0x00500593.
Lemma F_192c8 : fetch_word Plain.M.loaded_segments (0x19320 : word) = Some W_192c8.
Proof. vm_refl. Qed.
Lemma D_192c8 : decode_any W_192c8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192cc : bv 32 := 0x00a5cc63.
Lemma F_192cc : fetch_word Plain.M.loaded_segments (0x19324 : word) = Some W_192cc.
Proof. vm_refl. Qed.
Lemma D_192cc : decode_any W_192cc = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192d0 : bv 32 := 0xffff8517.
Lemma F_192d0 : fetch_word Plain.M.loaded_segments (0x19328 : word) = Some W_192d0.
Proof. vm_refl. Qed.
Lemma D_192d0 : decode_any W_192d0 = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192d4 : bv 32 := 0xffff8597.
Lemma F_192d4 : fetch_word Plain.M.loaded_segments (0x1932c : word) = Some W_192d4.
Proof. vm_refl. Qed.
Lemma D_192d4 : decode_any W_192d4 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192d8 : bv 32 := 0x3c050513.
Lemma F_192d8 : fetch_word Plain.M.loaded_segments (0x19330 : word) = Some W_192d8.
Proof. vm_refl. Qed.
Lemma D_192d8 : decode_any W_192d8 = Some (OpImm ALU_ADD 10 10 960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192dc : bv 32 := 0xcb358593.
Lemma F_192dc : fetch_word Plain.M.loaded_segments (0x19334 : word) = Some W_192dc.
Proof. vm_refl. Qed.
Lemma D_192dc : decode_any W_192dc = Some (OpImm ALU_ADD 11 11 3251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192e0 : bv 32 := 0x8a1fe0ef.
Lemma F_192e0 : fetch_word Plain.M.loaded_segments (0x19338 : word) = Some W_192e0.
Proof. vm_refl. Qed.
Lemma D_192e0 : decode_any W_192e0 = Some (Jal 1 2091168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192e4 : bv 32 := 0x00000513.
Lemma F_192e4 : fetch_word Plain.M.loaded_segments (0x1933c : word) = Some W_192e4.
Proof. vm_refl. Qed.
Lemma D_192e4 : decode_any W_192e4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192e8 : bv 32 := 0x02813083.
Lemma F_192e8 : fetch_word Plain.M.loaded_segments (0x19340 : word) = Some W_192e8.
Proof. vm_refl. Qed.
Lemma D_192e8 : decode_any W_192e8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192ec : bv 32 := 0x02013403.
Lemma F_192ec : fetch_word Plain.M.loaded_segments (0x19344 : word) = Some W_192ec.
Proof. vm_refl. Qed.
Lemma D_192ec : decode_any W_192ec = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192f0 : bv 32 := 0x01813483.
Lemma F_192f0 : fetch_word Plain.M.loaded_segments (0x19348 : word) = Some W_192f0.
Proof. vm_refl. Qed.
Lemma D_192f0 : decode_any W_192f0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192f4 : bv 32 := 0x01013903.
Lemma F_192f4 : fetch_word Plain.M.loaded_segments (0x1934c : word) = Some W_192f4.
Proof. vm_refl. Qed.
Lemma D_192f4 : decode_any W_192f4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192f8 : bv 32 := 0x00813983.
Lemma F_192f8 : fetch_word Plain.M.loaded_segments (0x19350 : word) = Some W_192f8.
Proof. vm_refl. Qed.
Lemma D_192f8 : decode_any W_192f8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192fc : bv 32 := 0x00013a03.
Lemma F_192fc : fetch_word Plain.M.loaded_segments (0x19354 : word) = Some W_192fc.
Proof. vm_refl. Qed.
Lemma D_192fc : decode_any W_192fc = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19300 : bv 32 := 0x03010113.
Lemma F_19300 : fetch_word Plain.M.loaded_segments (0x19358 : word) = Some W_19300.
Proof. vm_refl. Qed.
Lemma D_19300 : decode_any W_19300 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19304 : bv 32 := 0x00008067.
Lemma F_19304 : fetch_word Plain.M.loaded_segments (0x1935c : word) = Some W_19304.
Proof. vm_refl. Qed.
Lemma D_19304 : decode_any W_19304 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19308 : bv 32 := 0x00050993.
Lemma F_19308 : fetch_word Plain.M.loaded_segments (0x19360 : word) = Some W_19308.
Proof. vm_refl. Qed.
Lemma D_19308 : decode_any W_19308 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1930c : bv 32 := 0x00058913.
Lemma F_1930c : fetch_word Plain.M.loaded_segments (0x19364 : word) = Some W_1930c.
Proof. vm_refl. Qed.
Lemma D_1930c : decode_any W_1930c = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19310 : bv 32 := 0x00060a13.
Lemma F_19310 : fetch_word Plain.M.loaded_segments (0x19368 : word) = Some W_19310.
Proof. vm_refl. Qed.
Lemma D_19310 : decode_any W_19310 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19314 : bv 32 := 0x00100513.
Lemma F_19314 : fetch_word Plain.M.loaded_segments (0x1936c : word) = Some W_19314.
Proof. vm_refl. Qed.
Lemma D_19314 : decode_any W_19314 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19318 : bv 32 := 0x04000593.
Lemma F_19318 : fetch_word Plain.M.loaded_segments (0x19370 : word) = Some W_19318.
Proof. vm_refl. Qed.
Lemma D_19318 : decode_any W_19318 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1931c : bv 32 := 0x00100493.
Lemma F_1931c : fetch_word Plain.M.loaded_segments (0x19374 : word) = Some W_1931c.
Proof. vm_refl. Qed.
Lemma D_1931c : decode_any W_1931c = Some (OpImm ALU_ADD 9 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19320 : bv 32 := 0x35c160ef.
Lemma F_19320 : fetch_word Plain.M.loaded_segments (0x19378 : word) = Some W_19320.
Proof. vm_refl. Qed.
Lemma D_19320 : decode_any W_19320 = Some (Jal 1 90972, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19324 : bv 32 := 0x02050463.
Lemma F_19324 : fetch_word Plain.M.loaded_segments (0x1937c : word) = Some W_19324.
Proof. vm_refl. Qed.
Lemma D_19324 : decode_any W_19324 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19328 : bv 32 := 0xfe8a059b.
Lemma F_19328 : fetch_word Plain.M.loaded_segments (0x19380 : word) = Some W_19328.
Proof. vm_refl. Qed.
Lemma D_19328 : decode_any W_19328 = Some (OpImm32 11 20 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1932c : bv 32 := 0xff75f593.
Lemma F_1932c : fetch_word Plain.M.loaded_segments (0x19384 : word) = Some W_1932c.
Proof. vm_refl. Qed.
Lemma D_1932c : decode_any W_1932c = Some (OpImm ALU_AND 11 11 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19330 : bv 32 := 0x01352023.
Lemma F_19330 : fetch_word Plain.M.loaded_segments (0x19388 : word) = Some W_19330.
Proof. vm_refl. Qed.
Lemma D_19330 : decode_any W_19330 = Some (Store SZ4 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19334 : bv 32 := 0x01252223.
Lemma F_19334 : fetch_word Plain.M.loaded_segments (0x1938c : word) = Some W_19334.
Proof. vm_refl. Qed.
Lemma D_19334 : decode_any W_19334 = Some (Store SZ4 10 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19338 : bv 32 := 0x01452423.
Lemma F_19338 : fetch_word Plain.M.loaded_segments (0x19390 : word) = Some W_19338.
Proof. vm_refl. Qed.
Lemma D_19338 : decode_any W_19338 = Some (Store SZ4 10 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1933c : bv 32 := 0x00852823.
Lemma F_1933c : fetch_word Plain.M.loaded_segments (0x19394 : word) = Some W_1933c.
Proof. vm_refl. Qed.
Lemma D_1933c : decode_any W_1933c = Some (Store SZ4 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19340 : bv 32 := 0x02058a63.
Lemma F_19340 : fetch_word Plain.M.loaded_segments (0x19398 : word) = Some W_19340.
Proof. vm_refl. Qed.
Lemma D_19340 : decode_any W_19340 = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19344 : bv 32 := 0x00100593.
Lemma F_19344 : fetch_word Plain.M.loaded_segments (0x1939c : word) = Some W_19344.
Proof. vm_refl. Qed.
Lemma D_19344 : decode_any W_19344 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19348 : bv 32 := 0x0300006f.
Lemma F_19348 : fetch_word Plain.M.loaded_segments (0x193a0 : word) = Some W_19348.
Proof. vm_refl. Qed.
Lemma D_19348 : decode_any W_19348 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1934c : bv 32 := 0x0001f517.
Lemma F_1934c : fetch_word Plain.M.loaded_segments (0x193a4 : word) = Some W_1934c.
Proof. vm_refl. Qed.
Lemma D_1934c : decode_any W_1934c = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19350 : bv 32 := 0x0cc53503.
Lemma F_19350 : fetch_word Plain.M.loaded_segments (0x193a8 : word) = Some W_19350.
Proof. vm_refl. Qed.
Lemma D_19350 : decode_any W_19350 = Some (Load SZ8 true 10 10 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19354 : bv 32 := 0x00052503.
Lemma F_19354 : fetch_word Plain.M.loaded_segments (0x193ac : word) = Some W_19354.
Proof. vm_refl. Qed.
Lemma D_19354 : decode_any W_19354 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19358 : bv 32 := 0x00500593.
Lemma F_19358 : fetch_word Plain.M.loaded_segments (0x193b0 : word) = Some W_19358.
Proof. vm_refl. Qed.
Lemma D_19358 : decode_any W_19358 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1935c : bv 32 := 0xf8a5c4e3.
Lemma F_1935c : fetch_word Plain.M.loaded_segments (0x193b4 : word) = Some W_1935c.
Proof. vm_refl. Qed.
Lemma D_1935c : decode_any W_1935c = Some (Branch BC_LT 11 10 8072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19360 : bv 32 := 0xffff7517.
Lemma F_19360 : fetch_word Plain.M.loaded_segments (0x193b8 : word) = Some W_19360.
Proof. vm_refl. Qed.
Lemma D_19360 : decode_any W_19360 = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19364 : bv 32 := 0xffff8597.
Lemma F_19364 : fetch_word Plain.M.loaded_segments (0x193bc : word) = Some W_19364.
Proof. vm_refl. Qed.
Lemma D_19364 : decode_any W_19364 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19368 : bv 32 := 0x3a050513.
Lemma F_19368 : fetch_word Plain.M.loaded_segments (0x193c0 : word) = Some W_19368.
Proof. vm_refl. Qed.
Lemma D_19368 : decode_any W_19368 = Some (OpImm ALU_ADD 10 10 928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1936c : bv 32 := 0xc2358593.
Lemma F_1936c : fetch_word Plain.M.loaded_segments (0x193c4 : word) = Some W_1936c.
Proof. vm_refl. Qed.
Lemma D_1936c : decode_any W_1936c = Some (OpImm ALU_ADD 11 11 3107, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19370 : bv 32 := 0xebdff06f.
Lemma F_19370 : fetch_word Plain.M.loaded_segments (0x193c8 : word) = Some W_19370.
Proof. vm_refl. Qed.
Lemma D_19370 : decode_any W_19370 = Some (Jal 0 2096828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19374 : bv 32 := 0x00300593.
Lemma F_19374 : fetch_word Plain.M.loaded_segments (0x193cc : word) = Some W_19374.
Proof. vm_refl. Qed.
Lemma D_19374 : decode_any W_19374 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19378 : bv 32 := 0x00b52623.
Lemma F_19378 : fetch_word Plain.M.loaded_segments (0x193d0 : word) = Some W_19378.
Proof. vm_refl. Qed.
Lemma D_19378 : decode_any W_19378 = Some (Store SZ4 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1937c : bv 32 := 0x0310000f.
Lemma F_1937c : fetch_word Plain.M.loaded_segments (0x193d4 : word) = Some W_1937c.
Proof. vm_refl. Qed.
Lemma D_1937c : decode_any W_1937c = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19380 : bv 32 := 0x00952a23.
Lemma F_19380 : fetch_word Plain.M.loaded_segments (0x193d8 : word) = Some W_19380.
Proof. vm_refl. Qed.
Lemma D_19380 : decode_any W_19380 = Some (Store SZ4 10 9 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19384 : bv 32 := 0x0330000f.
Lemma F_19384 : fetch_word Plain.M.loaded_segments (0x193dc : word) = Some W_19384.
Proof. vm_refl. Qed.
Lemma D_19384 : decode_any W_19384 = Some (Fence 0 3 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19388 : bv 32 := 0x02052023.
Lemma F_19388 : fetch_word Plain.M.loaded_segments (0x193e0 : word) = Some W_19388.
Proof. vm_refl. Qed.
Lemma D_19388 : decode_any W_19388 = Some (Store SZ4 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1938c : bv 32 := 0xf5dff06f.
Lemma F_1938c : fetch_word Plain.M.loaded_segments (0x193e4 : word) = Some W_1938c.
Proof. vm_refl. Qed.
Lemma D_1938c : decode_any W_1938c = Some (Jal 0 2096988, 4%Z).
Proof. vm_refl. Qed.
