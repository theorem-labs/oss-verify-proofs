(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_83958 : bv 32 := 0x000e9517.
Lemma F_83958 : fetch_word AsanUbsan.M.loaded_segments (0x839a0 : word) = Some W_83958.
Proof. vm_refl. Qed.
Lemma D_83958 : decode_any W_83958 = Some (Auipc 10 233, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8395c : bv 32 := 0x67c50503.
Lemma F_8395c : fetch_word AsanUbsan.M.loaded_segments (0x839a4 : word) = Some W_8395c.
Proof. vm_refl. Qed.
Lemma D_8395c : decode_any W_8395c = Some (Load SZ1 true 10 10 1660, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83960 : bv 32 := 0x0230000f.
Lemma F_83960 : fetch_word AsanUbsan.M.loaded_segments (0x839a8 : word) = Some W_83960.
Proof. vm_refl. Qed.
Lemma D_83960 : decode_any W_83960 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83964 : bv 32 := 0x00a03533.
Lemma F_83964 : fetch_word AsanUbsan.M.loaded_segments (0x839ac : word) = Some W_83964.
Proof. vm_refl. Qed.
Lemma D_83964 : decode_any W_83964 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83968 : bv 32 := 0x00008067.
Lemma F_83968 : fetch_word AsanUbsan.M.loaded_segments (0x839b0 : word) = Some W_83968.
Proof. vm_refl. Qed.
Lemma D_83968 : decode_any W_83968 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8396c : bv 32 := 0xfc010113.
Lemma F_8396c : fetch_word AsanUbsan.M.loaded_segments (0x839b4 : word) = Some W_8396c.
Proof. vm_refl. Qed.
Lemma D_8396c : decode_any W_8396c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83970 : bv 32 := 0x02113c23.
Lemma F_83970 : fetch_word AsanUbsan.M.loaded_segments (0x839b8 : word) = Some W_83970.
Proof. vm_refl. Qed.
Lemma D_83970 : decode_any W_83970 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83974 : bv 32 := 0x02813823.
Lemma F_83974 : fetch_word AsanUbsan.M.loaded_segments (0x839bc : word) = Some W_83974.
Proof. vm_refl. Qed.
Lemma D_83974 : decode_any W_83974 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83978 : bv 32 := 0x02913423.
Lemma F_83978 : fetch_word AsanUbsan.M.loaded_segments (0x839c0 : word) = Some W_83978.
Proof. vm_refl. Qed.
Lemma D_83978 : decode_any W_83978 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8397c : bv 32 := 0x03213023.
Lemma F_8397c : fetch_word AsanUbsan.M.loaded_segments (0x839c4 : word) = Some W_8397c.
Proof. vm_refl. Qed.
Lemma D_8397c : decode_any W_8397c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83980 : bv 32 := 0x01313c23.
Lemma F_83980 : fetch_word AsanUbsan.M.loaded_segments (0x839c8 : word) = Some W_83980.
Proof. vm_refl. Qed.
Lemma D_83980 : decode_any W_83980 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83984 : bv 32 := 0x01413823.
Lemma F_83984 : fetch_word AsanUbsan.M.loaded_segments (0x839cc : word) = Some W_83984.
Proof. vm_refl. Qed.
Lemma D_83984 : decode_any W_83984 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83988 : bv 32 := 0x01513423.
Lemma F_83988 : fetch_word AsanUbsan.M.loaded_segments (0x839d0 : word) = Some W_83988.
Proof. vm_refl. Qed.
Lemma D_83988 : decode_any W_83988 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8398c : bv 32 := 0x00060a63.
Lemma F_8398c : fetch_word AsanUbsan.M.loaded_segments (0x839d4 : word) = Some W_8398c.
Proof. vm_refl. Qed.
Lemma D_8398c : decode_any W_8398c = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83990 : bv 32 := 0x000e9697.
Lemma F_83990 : fetch_word AsanUbsan.M.loaded_segments (0x839d8 : word) = Some W_83990.
Proof. vm_refl. Qed.
Lemma D_83990 : decode_any W_83990 = Some (Auipc 13 233, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83994 : bv 32 := 0x64468683.
Lemma F_83994 : fetch_word AsanUbsan.M.loaded_segments (0x839dc : word) = Some W_83994.
Proof. vm_refl. Qed.
Lemma D_83994 : decode_any W_83994 = Some (Load SZ1 true 13 13 1604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83998 : bv 32 := 0x0230000f.
Lemma F_83998 : fetch_word AsanUbsan.M.loaded_segments (0x839e0 : word) = Some W_83998.
Proof. vm_refl. Qed.
Lemma D_83998 : decode_any W_83998 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8399c : bv 32 := 0x0a068a63.
Lemma F_8399c : fetch_word AsanUbsan.M.loaded_segments (0x839e4 : word) = Some W_8399c.
Proof. vm_refl. Qed.
Lemma D_8399c : decode_any W_8399c = Some (Branch BC_EQ 13 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839a0 : bv 32 := 0x00757693.
Lemma F_839a0 : fetch_word AsanUbsan.M.loaded_segments (0x839e8 : word) = Some W_839a0.
Proof. vm_refl. Qed.
Lemma D_839a0 : decode_any W_839a0 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839a4 : bv 32 := 0x42069863.
Lemma F_839a4 : fetch_word AsanUbsan.M.loaded_segments (0x839ec : word) = Some W_839a4.
Proof. vm_refl. Qed.
Lemma D_839a4 : decode_any W_839a4 = Some (Branch BC_NE 13 0 1072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839a8 : bv 32 := 0x000e1697.
Lemma F_839a8 : fetch_word AsanUbsan.M.loaded_segments (0x839f0 : word) = Some W_839a8.
Proof. vm_refl. Qed.
Lemma D_839a8 : decode_any W_839a8 = Some (Auipc 13 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839ac : bv 32 := 0xb286b683.
Lemma F_839ac : fetch_word AsanUbsan.M.loaded_segments (0x839f4 : word) = Some W_839ac.
Proof. vm_refl. Qed.
Lemma D_839ac : decode_any W_839ac = Some (Load SZ8 true 13 13 2856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839b0 : bv 32 := 0x0006b483.
Lemma F_839b0 : fetch_word AsanUbsan.M.loaded_segments (0x839f8 : word) = Some W_839b0.
Proof. vm_refl. Qed.
Lemma D_839b0 : decode_any W_839b0 = Some (Load SZ8 true 9 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839b4 : bv 32 := 0xfff48693.
Lemma F_839b4 : fetch_word AsanUbsan.M.loaded_segments (0x839fc : word) = Some W_839b4.
Proof. vm_refl. Qed.
Lemma D_839b4 : decode_any W_839b4 = Some (OpImm ALU_ADD 13 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839b8 : bv 32 := 0x00d4b733.
Lemma F_839b8 : fetch_word AsanUbsan.M.loaded_segments (0x83a00 : word) = Some W_839b8.
Proof. vm_refl. Qed.
Lemma D_839b8 : decode_any W_839b8 = Some (Op ALU_SLTU 14 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839bc : bv 32 := 0xfff70713.
Lemma F_839bc : fetch_word AsanUbsan.M.loaded_segments (0x83a04 : word) = Some W_839bc.
Proof. vm_refl. Qed.
Lemma D_839bc : decode_any W_839bc = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839c0 : bv 32 := 0x00d77733.
Lemma F_839c0 : fetch_word AsanUbsan.M.loaded_segments (0x83a08 : word) = Some W_839c0.
Proof. vm_refl. Qed.
Lemma D_839c0 : decode_any W_839c0 = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839c4 : bv 32 := 0x1ca77c63.
Lemma F_839c4 : fetch_word AsanUbsan.M.loaded_segments (0x83a0c : word) = Some W_839c4.
Proof. vm_refl. Qed.
Lemma D_839c4 : decode_any W_839c4 = Some (Branch BC_GEU 14 10 472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839c8 : bv 32 := 0x000e1797.
Lemma F_839c8 : fetch_word AsanUbsan.M.loaded_segments (0x83a10 : word) = Some W_839c8.
Proof. vm_refl. Qed.
Lemma D_839c8 : decode_any W_839c8 = Some (Auipc 15 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839cc : bv 32 := 0xb107b783.
Lemma F_839cc : fetch_word AsanUbsan.M.loaded_segments (0x83a14 : word) = Some W_839cc.
Proof. vm_refl. Qed.
Lemma D_839cc : decode_any W_839cc = Some (Load SZ8 true 15 15 2832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839d0 : bv 32 := 0x000e1817.
Lemma F_839d0 : fetch_word AsanUbsan.M.loaded_segments (0x83a18 : word) = Some W_839d0.
Proof. vm_refl. Qed.
Lemma D_839d0 : decode_any W_839d0 = Some (Auipc 16 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839d4 : bv 32 := 0xb1083803.
Lemma F_839d4 : fetch_word AsanUbsan.M.loaded_segments (0x83a1c : word) = Some W_839d4.
Proof. vm_refl. Qed.
Lemma D_839d4 : decode_any W_839d4 = Some (Load SZ8 true 16 16 2832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839d8 : bv 32 := 0x0007b883.
Lemma F_839d8 : fetch_word AsanUbsan.M.loaded_segments (0x83a20 : word) = Some W_839d8.
Proof. vm_refl. Qed.
Lemma D_839d8 : decode_any W_839d8 = Some (Load SZ8 true 17 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839dc : bv 32 := 0x00083783.
Lemma F_839dc : fetch_word AsanUbsan.M.loaded_segments (0x83a24 : word) = Some W_839dc.
Proof. vm_refl. Qed.
Lemma D_839dc : decode_any W_839dc = Some (Load SZ8 true 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839e0 : bv 32 := 0xfff88813.
Lemma F_839e0 : fetch_word AsanUbsan.M.loaded_segments (0x83a28 : word) = Some W_839e0.
Proof. vm_refl. Qed.
Lemma D_839e0 : decode_any W_839e0 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839e4 : bv 32 := 0x00a87463.
Lemma F_839e4 : fetch_word AsanUbsan.M.loaded_segments (0x83a2c : word) = Some W_839e4.
Proof. vm_refl. Qed.
Lemma D_839e4 : decode_any W_839e4 = Some (Branch BC_GEU 16 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839ec : bv 32 := 0x000e1297.
Lemma F_839ec : fetch_word AsanUbsan.M.loaded_segments (0x83a34 : word) = Some W_839ec.
Proof. vm_refl. Qed.
Lemma D_839ec : decode_any W_839ec = Some (Auipc 5 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839f0 : bv 32 := 0xafc2b283.
Lemma F_839f0 : fetch_word AsanUbsan.M.loaded_segments (0x83a38 : word) = Some W_839f0.
Proof. vm_refl. Qed.
Lemma D_839f0 : decode_any W_839f0 = Some (Load SZ8 true 5 5 2812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839f4 : bv 32 := 0x0002be03.
Lemma F_839f4 : fetch_word AsanUbsan.M.loaded_segments (0x83a3c : word) = Some W_839f4.
Proof. vm_refl. Qed.
Lemma D_839f4 : decode_any W_839f4 = Some (Load SZ8 true 28 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839f8 : bv 32 := 0x003e5313.
Lemma F_839f8 : fetch_word AsanUbsan.M.loaded_segments (0x83a40 : word) = Some W_839f8.
Proof. vm_refl. Qed.
Lemma D_839f8 : decode_any W_839f8 = Some (ShiftImm ALU_SRL 6 28 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_839fc : bv 32 := 0x009303b3.
Lemma F_839fc : fetch_word AsanUbsan.M.loaded_segments (0x83a44 : word) = Some W_839fc.
Proof. vm_refl. Qed.
Lemma D_839fc : decode_any W_839fc = Some (Op ALU_ADD 7 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a00 : bv 32 := 0x00ae6463.
Lemma F_83a00 : fetch_word AsanUbsan.M.loaded_segments (0x83a48 : word) = Some W_83a00.
Proof. vm_refl. Qed.
Lemma D_83a00 : decode_any W_83a00 = Some (Branch BC_LTU 28 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a04 : bv 32 := 0x0ca3e463.
Lemma F_83a04 : fetch_word AsanUbsan.M.loaded_segments (0x83a4c : word) = Some W_83a04.
Proof. vm_refl. Qed.
Lemma D_83a04 : decode_any W_83a04 = Some (Branch BC_LTU 7 10 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83acc : bv 32 := 0x0002b383.
Lemma F_83acc : fetch_word AsanUbsan.M.loaded_segments (0x83b14 : word) = Some W_83acc.
Proof. vm_refl. Qed.
Lemma D_83acc : decode_any W_83acc = Some (Load SZ8 true 7 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ad0 : bv 32 := 0x0033d293.
Lemma F_83ad0 : fetch_word AsanUbsan.M.loaded_segments (0x83b18 : word) = Some W_83ad0.
Proof. vm_refl. Qed.
Lemma D_83ad0 : decode_any W_83ad0 = Some (ShiftImm ALU_SRL 5 7 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ad4 : bv 32 := 0x00928333.
Lemma F_83ad4 : fetch_word AsanUbsan.M.loaded_segments (0x83b1c : word) = Some W_83ad4.
Proof. vm_refl. Qed.
Lemma D_83ad4 : decode_any W_83ad4 = Some (Op ALU_ADD 6 5 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ad8 : bv 32 := 0x00a3e463.
Lemma F_83ad8 : fetch_word AsanUbsan.M.loaded_segments (0x83b20 : word) = Some W_83ad8.
Proof. vm_refl. Qed.
Lemma D_83ad8 : decode_any W_83ad8 = Some (Branch BC_LTU 7 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83adc : bv 32 := 0x0ca36063.
Lemma F_83adc : fetch_word AsanUbsan.M.loaded_segments (0x83b24 : word) = Some W_83adc.
Proof. vm_refl. Qed.
Lemma D_83adc : decode_any W_83adc = Some (Branch BC_LTU 6 10 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b9c : bv 32 := 0x0075f793.
Lemma F_83b9c : fetch_word AsanUbsan.M.loaded_segments (0x83be4 : word) = Some W_83b9c.
Proof. vm_refl. Qed.
Lemma D_83b9c : decode_any W_83b9c = Some (OpImm ALU_AND 15 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ba0 : bv 32 := 0x26079a63.
Lemma F_83ba0 : fetch_word AsanUbsan.M.loaded_segments (0x83be8 : word) = Some W_83ba0.
Proof. vm_refl. Qed.
Lemma D_83ba0 : decode_any W_83ba0 = Some (Branch BC_NE 15 0 628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ba4 : bv 32 := 0x00b505b3.
Lemma F_83ba4 : fetch_word AsanUbsan.M.loaded_segments (0x83bec : word) = Some W_83ba4.
Proof. vm_refl. Qed.
Lemma D_83ba4 : decode_any W_83ba4 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ba8 : bv 32 := 0xff858593.
Lemma F_83ba8 : fetch_word AsanUbsan.M.loaded_segments (0x83bf0 : word) = Some W_83ba8.
Proof. vm_refl. Qed.
Lemma D_83ba8 : decode_any W_83ba8 = Some (OpImm ALU_ADD 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bac : bv 32 := 0x04b77263.
Lemma F_83bac : fetch_word AsanUbsan.M.loaded_segments (0x83bf4 : word) = Some W_83bac.
Proof. vm_refl. Qed.
Lemma D_83bac : decode_any W_83bac = Some (Branch BC_GEU 14 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bb0 : bv 32 := 0x000e1717.
Lemma F_83bb0 : fetch_word AsanUbsan.M.loaded_segments (0x83bf8 : word) = Some W_83bb0.
Proof. vm_refl. Qed.
Lemma D_83bb0 : decode_any W_83bb0 = Some (Auipc 14 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bb4 : bv 32 := 0x92873703.
Lemma F_83bb4 : fetch_word AsanUbsan.M.loaded_segments (0x83bfc : word) = Some W_83bb4.
Proof. vm_refl. Qed.
Lemma D_83bb4 : decode_any W_83bb4 = Some (Load SZ8 true 14 14 2344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bb8 : bv 32 := 0x000e1797.
Lemma F_83bb8 : fetch_word AsanUbsan.M.loaded_segments (0x83c00 : word) = Some W_83bb8.
Proof. vm_refl. Qed.
Lemma D_83bb8 : decode_any W_83bb8 = Some (Auipc 15 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bbc : bv 32 := 0x9287b783.
Lemma F_83bbc : fetch_word AsanUbsan.M.loaded_segments (0x83c04 : word) = Some W_83bbc.
Proof. vm_refl. Qed.
Lemma D_83bbc : decode_any W_83bbc = Some (Load SZ8 true 15 15 2344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bc0 : bv 32 := 0x00073883.
Lemma F_83bc0 : fetch_word AsanUbsan.M.loaded_segments (0x83c08 : word) = Some W_83bc0.
Proof. vm_refl. Qed.
Lemma D_83bc0 : decode_any W_83bc0 = Some (Load SZ8 true 17 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bc4 : bv 32 := 0x0007b703.
Lemma F_83bc4 : fetch_word AsanUbsan.M.loaded_segments (0x83c0c : word) = Some W_83bc4.
Proof. vm_refl. Qed.
Lemma D_83bc4 : decode_any W_83bc4 = Some (Load SZ8 true 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bc8 : bv 32 := 0xfff88813.
Lemma F_83bc8 : fetch_word AsanUbsan.M.loaded_segments (0x83c10 : word) = Some W_83bc8.
Proof. vm_refl. Qed.
Lemma D_83bc8 : decode_any W_83bc8 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bcc : bv 32 := 0x00b87463.
Lemma F_83bcc : fetch_word AsanUbsan.M.loaded_segments (0x83c14 : word) = Some W_83bcc.
Proof. vm_refl. Qed.
Lemma D_83bcc : decode_any W_83bcc = Some (Branch BC_GEU 16 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bd4 : bv 32 := 0x000e1797.
Lemma F_83bd4 : fetch_word AsanUbsan.M.loaded_segments (0x83c1c : word) = Some W_83bd4.
Proof. vm_refl. Qed.
Lemma D_83bd4 : decode_any W_83bd4 = Some (Auipc 15 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bd8 : bv 32 := 0x9147b783.
Lemma F_83bd8 : fetch_word AsanUbsan.M.loaded_segments (0x83c20 : word) = Some W_83bd8.
Proof. vm_refl. Qed.
Lemma D_83bd8 : decode_any W_83bd8 = Some (Load SZ8 true 15 15 2324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bdc : bv 32 := 0x0007b303.
Lemma F_83bdc : fetch_word AsanUbsan.M.loaded_segments (0x83c24 : word) = Some W_83bdc.
Proof. vm_refl. Qed.
Lemma D_83bdc : decode_any W_83bdc = Some (Load SZ8 true 6 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83be0 : bv 32 := 0x00335793.
Lemma F_83be0 : fetch_word AsanUbsan.M.loaded_segments (0x83c28 : word) = Some W_83be0.
Proof. vm_refl. Qed.
Lemma D_83be0 : decode_any W_83be0 = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83be4 : bv 32 := 0x009782b3.
Lemma F_83be4 : fetch_word AsanUbsan.M.loaded_segments (0x83c2c : word) = Some W_83be4.
Proof. vm_refl. Qed.
Lemma D_83be4 : decode_any W_83be4 = Some (Op ALU_ADD 5 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83be8 : bv 32 := 0x12b36263.
Lemma F_83be8 : fetch_word AsanUbsan.M.loaded_segments (0x83c30 : word) = Some W_83be8.
Proof. vm_refl. Qed.
Lemma D_83be8 : decode_any W_83be8 = Some (Branch BC_LTU 6 11 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bec : bv 32 := 0x12b2f063.
Lemma F_83bec : fetch_word AsanUbsan.M.loaded_segments (0x83c34 : word) = Some W_83bec.
Proof. vm_refl. Qed.
Lemma D_83bec : decode_any W_83bec = Some (Branch BC_GEU 5 11 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bf0 : bv 32 := 0x000e1697.
Lemma F_83bf0 : fetch_word AsanUbsan.M.loaded_segments (0x83c38 : word) = Some W_83bf0.
Proof. vm_refl. Qed.
Lemma D_83bf0 : decode_any W_83bf0 = Some (Auipc 13 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bf4 : bv 32 := 0x9006b983.
Lemma F_83bf4 : fetch_word AsanUbsan.M.loaded_segments (0x83c3c : word) = Some W_83bf4.
Proof. vm_refl. Qed.
Lemma D_83bf4 : decode_any W_83bf4 = Some (Load SZ8 true 19 13 2304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bf8 : bv 32 := 0x0009b303.
Lemma F_83bf8 : fetch_word AsanUbsan.M.loaded_segments (0x83c40 : word) = Some W_83bf8.
Proof. vm_refl. Qed.
Lemma D_83bf8 : decode_any W_83bf8 = Some (Load SZ8 true 6 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bfc : bv 32 := 0x22030c63.
Lemma F_83bfc : fetch_word AsanUbsan.M.loaded_segments (0x83c44 : word) = Some W_83bfc.
Proof. vm_refl. Qed.
Lemma D_83bfc : decode_any W_83bfc = Some (Branch BC_EQ 6 0 568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83c00 : bv 32 := 0x00355693.
Lemma F_83c00 : fetch_word AsanUbsan.M.loaded_segments (0x83c48 : word) = Some W_83c00.
Proof. vm_refl. Qed.
Lemma D_83c00 : decode_any W_83c00 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83c04 : bv 32 := 0x0035d593.
Lemma F_83c04 : fetch_word AsanUbsan.M.loaded_segments (0x83c4c : word) = Some W_83c04.
Proof. vm_refl. Qed.
Lemma D_83c04 : decode_any W_83c04 = Some (ShiftImm ALU_SRL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83c08 : bv 32 := 0x00d48533.
Lemma F_83c08 : fetch_word AsanUbsan.M.loaded_segments (0x83c50 : word) = Some W_83c08.
Proof. vm_refl. Qed.
Lemma D_83c08 : decode_any W_83c08 = Some (Op ALU_ADD 10 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83c0c : bv 32 := 0x00158913.
Lemma F_83c0c : fetch_word AsanUbsan.M.loaded_segments (0x83c54 : word) = Some W_83c0c.
Proof. vm_refl. Qed.
Lemma D_83c0c : decode_any W_83c0c = Some (OpImm ALU_ADD 18 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83c10 : bv 32 := 0x40d90433.
Lemma F_83c10 : fetch_word AsanUbsan.M.loaded_segments (0x83c58 : word) = Some W_83c10.
Proof. vm_refl. Qed.
Lemma D_83c10 : decode_any W_83c10 = Some (Op ALU_SUB 8 18 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83c14 : bv 32 := 0x0c061063.
Lemma F_83c14 : fetch_word AsanUbsan.M.loaded_segments (0x83c5c : word) = Some W_83c14.
Proof. vm_refl. Qed.
Lemma D_83c14 : decode_any W_83c14 = Some (Branch BC_NE 12 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83c18 : bv 32 := 0x000e1597.
Lemma F_83c18 : fetch_word AsanUbsan.M.loaded_segments (0x83c60 : word) = Some W_83c18.
Proof. vm_refl. Qed.
Lemma D_83c18 : decode_any W_83c18 = Some (Auipc 11 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83c1c : bv 32 := 0x8a85b583.
Lemma F_83c1c : fetch_word AsanUbsan.M.loaded_segments (0x83c64 : word) = Some W_83c1c.
Proof. vm_refl. Qed.
Lemma D_83c1c : decode_any W_83c1c = Some (Load SZ8 true 11 11 2216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83c20 : bv 32 := 0x0785b583.
Lemma F_83c20 : fetch_word AsanUbsan.M.loaded_segments (0x83c68 : word) = Some W_83c20.
Proof. vm_refl. Qed.
Lemma D_83c20 : decode_any W_83c20 = Some (Load SZ8 true 11 11 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83c24 : bv 32 := 0x0ab46863.
Lemma F_83c24 : fetch_word AsanUbsan.M.loaded_segments (0x83c6c : word) = Some W_83c24.
Proof. vm_refl. Qed.
Lemma D_83c24 : decode_any W_83c24 = Some (Branch BC_LTU 8 11 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83cd4 : bv 32 := 0x00060593.
Lemma F_83cd4 : fetch_word AsanUbsan.M.loaded_segments (0x83d1c : word) = Some W_83cd4.
Proof. vm_refl. Qed.
Lemma D_83cd4 : decode_any W_83cd4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83cd8 : bv 32 := 0x00c0006f.
Lemma F_83cd8 : fetch_word AsanUbsan.M.loaded_segments (0x83d20 : word) = Some W_83cd8.
Proof. vm_refl. Qed.
Lemma D_83cd8 : decode_any W_83cd8 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ce4 : bv 32 := 0x00040613.
Lemma F_83ce4 : fetch_word AsanUbsan.M.loaded_segments (0x83d2c : word) = Some W_83ce4.
Proof. vm_refl. Qed.
Lemma D_83ce4 : decode_any W_83ce4 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ce8 : bv 32 := 0x03813083.
Lemma F_83ce8 : fetch_word AsanUbsan.M.loaded_segments (0x83d30 : word) = Some W_83ce8.
Proof. vm_refl. Qed.
Lemma D_83ce8 : decode_any W_83ce8 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83cec : bv 32 := 0x03013403.
Lemma F_83cec : fetch_word AsanUbsan.M.loaded_segments (0x83d34 : word) = Some W_83cec.
Proof. vm_refl. Qed.
Lemma D_83cec : decode_any W_83cec = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83cf0 : bv 32 := 0x02813483.
Lemma F_83cf0 : fetch_word AsanUbsan.M.loaded_segments (0x83d38 : word) = Some W_83cf0.
Proof. vm_refl. Qed.
Lemma D_83cf0 : decode_any W_83cf0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83cf4 : bv 32 := 0x02013903.
Lemma F_83cf4 : fetch_word AsanUbsan.M.loaded_segments (0x83d3c : word) = Some W_83cf4.
Proof. vm_refl. Qed.
Lemma D_83cf4 : decode_any W_83cf4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83cf8 : bv 32 := 0x01813983.
Lemma F_83cf8 : fetch_word AsanUbsan.M.loaded_segments (0x83d40 : word) = Some W_83cf8.
Proof. vm_refl. Qed.
Lemma D_83cf8 : decode_any W_83cf8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83cfc : bv 32 := 0x01013a03.
Lemma F_83cfc : fetch_word AsanUbsan.M.loaded_segments (0x83d44 : word) = Some W_83cfc.
Proof. vm_refl. Qed.
Lemma D_83cfc : decode_any W_83cfc = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83d00 : bv 32 := 0x00813a83.
Lemma F_83d00 : fetch_word AsanUbsan.M.loaded_segments (0x83d48 : word) = Some W_83d00.
Proof. vm_refl. Qed.
Lemma D_83d00 : decode_any W_83d00 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83d04 : bv 32 := 0x04010113.
Lemma F_83d04 : fetch_word AsanUbsan.M.loaded_segments (0x83d4c : word) = Some W_83d04.
Proof. vm_refl. Qed.
Lemma D_83d04 : decode_any W_83d04 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83d08 : bv 32 := 0x00030067.
Lemma F_83d08 : fetch_word AsanUbsan.M.loaded_segments (0x83d50 : word) = Some W_83d08.
Proof. vm_refl. Qed.
Lemma D_83d08 : decode_any W_83d08 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83e68 : bv 32 := 0x000e0597.
Lemma F_83e68 : fetch_word AsanUbsan.M.loaded_segments (0x83eb0 : word) = Some W_83e68.
Proof. vm_refl. Qed.
Lemma D_83e68 : decode_any W_83e68 = Some (Auipc 11 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83e6c : bv 32 := 0x6685b583.
Lemma F_83e6c : fetch_word AsanUbsan.M.loaded_segments (0x83eb4 : word) = Some W_83e6c.
Proof. vm_refl. Qed.
Lemma D_83e6c : decode_any W_83e6c = Some (Load SZ8 true 11 11 1640, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83e70 : bv 32 := 0x0005b583.
Lemma F_83e70 : fetch_word AsanUbsan.M.loaded_segments (0x83eb8 : word) = Some W_83e70.
Proof. vm_refl. Qed.
Lemma D_83e70 : decode_any W_83e70 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83e74 : bv 32 := 0xfff58613.
Lemma F_83e74 : fetch_word AsanUbsan.M.loaded_segments (0x83ebc : word) = Some W_83e74.
Proof. vm_refl. Qed.
Lemma D_83e74 : decode_any W_83e74 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83e78 : bv 32 := 0x00c5b6b3.
Lemma F_83e78 : fetch_word AsanUbsan.M.loaded_segments (0x83ec0 : word) = Some W_83e78.
Proof. vm_refl. Qed.
Lemma D_83e78 : decode_any W_83e78 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83e7c : bv 32 := 0xfff68693.
Lemma F_83e7c : fetch_word AsanUbsan.M.loaded_segments (0x83ec4 : word) = Some W_83e7c.
Proof. vm_refl. Qed.
Lemma D_83e7c : decode_any W_83e7c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83e80 : bv 32 := 0x00c6f6b3.
Lemma F_83e80 : fetch_word AsanUbsan.M.loaded_segments (0x83ec8 : word) = Some W_83e80.
Proof. vm_refl. Qed.
Lemma D_83e80 : decode_any W_83e80 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83e84 : bv 32 := 0x04a6f263.
Lemma F_83e84 : fetch_word AsanUbsan.M.loaded_segments (0x83ecc : word) = Some W_83e84.
Proof. vm_refl. Qed.
Lemma D_83e84 : decode_any W_83e84 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83e88 : bv 32 := 0x000e0697.
Lemma F_83e88 : fetch_word AsanUbsan.M.loaded_segments (0x83ed0 : word) = Some W_83e88.
Proof. vm_refl. Qed.
Lemma D_83e88 : decode_any W_83e88 = Some (Auipc 13 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83e8c : bv 32 := 0x6506b683.
Lemma F_83e8c : fetch_word AsanUbsan.M.loaded_segments (0x83ed4 : word) = Some W_83e8c.
Proof. vm_refl. Qed.
Lemma D_83e8c : decode_any W_83e8c = Some (Load SZ8 true 13 13 1616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83e90 : bv 32 := 0x000e0717.
Lemma F_83e90 : fetch_word AsanUbsan.M.loaded_segments (0x83ed8 : word) = Some W_83e90.
Proof. vm_refl. Qed.
Lemma D_83e90 : decode_any W_83e90 = Some (Auipc 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83e94 : bv 32 := 0x65073703.
Lemma F_83e94 : fetch_word AsanUbsan.M.loaded_segments (0x83edc : word) = Some W_83e94.
Proof. vm_refl. Qed.
Lemma D_83e94 : decode_any W_83e94 = Some (Load SZ8 true 14 14 1616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83e98 : bv 32 := 0x0006b803.
Lemma F_83e98 : fetch_word AsanUbsan.M.loaded_segments (0x83ee0 : word) = Some W_83e98.
Proof. vm_refl. Qed.
Lemma D_83e98 : decode_any W_83e98 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83e9c : bv 32 := 0x00073683.
Lemma F_83e9c : fetch_word AsanUbsan.M.loaded_segments (0x83ee4 : word) = Some W_83e9c.
Proof. vm_refl. Qed.
Lemma D_83e9c : decode_any W_83e9c = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ea0 : bv 32 := 0xfff80793.
Lemma F_83ea0 : fetch_word AsanUbsan.M.loaded_segments (0x83ee8 : word) = Some W_83ea0.
Proof. vm_refl. Qed.
Lemma D_83ea0 : decode_any W_83ea0 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ea4 : bv 32 := 0x00a7f463.
Lemma F_83ea4 : fetch_word AsanUbsan.M.loaded_segments (0x83eec : word) = Some W_83ea4.
Proof. vm_refl. Qed.
Lemma D_83ea4 : decode_any W_83ea4 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83eac : bv 32 := 0x000e0717.
Lemma F_83eac : fetch_word AsanUbsan.M.loaded_segments (0x83ef4 : word) = Some W_83eac.
Proof. vm_refl. Qed.
Lemma D_83eac : decode_any W_83eac = Some (Auipc 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83eb0 : bv 32 := 0x63c73703.
Lemma F_83eb0 : fetch_word AsanUbsan.M.loaded_segments (0x83ef8 : word) = Some W_83eb0.
Proof. vm_refl. Qed.
Lemma D_83eb0 : decode_any W_83eb0 = Some (Load SZ8 true 14 14 1596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83eb4 : bv 32 := 0x00073283.
Lemma F_83eb4 : fetch_word AsanUbsan.M.loaded_segments (0x83efc : word) = Some W_83eb4.
Proof. vm_refl. Qed.
Lemma D_83eb4 : decode_any W_83eb4 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83eb8 : bv 32 := 0x0032d713.
Lemma F_83eb8 : fetch_word AsanUbsan.M.loaded_segments (0x83f00 : word) = Some W_83eb8.
Proof. vm_refl. Qed.
Lemma D_83eb8 : decode_any W_83eb8 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ebc : bv 32 := 0x00b708b3.
Lemma F_83ebc : fetch_word AsanUbsan.M.loaded_segments (0x83f04 : word) = Some W_83ebc.
Proof. vm_refl. Qed.
Lemma D_83ebc : decode_any W_83ebc = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ec0 : bv 32 := 0x00a2ea63.
Lemma F_83ec0 : fetch_word AsanUbsan.M.loaded_segments (0x83f08 : word) = Some W_83ec0.
Proof. vm_refl. Qed.
Lemma D_83ec0 : decode_any W_83ec0 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ec4 : bv 32 := 0x00a8f863.
Lemma F_83ec4 : fetch_word AsanUbsan.M.loaded_segments (0x83f0c : word) = Some W_83ec4.
Proof. vm_refl. Qed.
Lemma D_83ec4 : decode_any W_83ec4 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ec8 : bv 32 := 0x00355513.
Lemma F_83ec8 : fetch_word AsanUbsan.M.loaded_segments (0x83f10 : word) = Some W_83ec8.
Proof. vm_refl. Qed.
Lemma D_83ec8 : decode_any W_83ec8 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ecc : bv 32 := 0x00a58533.
Lemma F_83ecc : fetch_word AsanUbsan.M.loaded_segments (0x83f14 : word) = Some W_83ecc.
Proof. vm_refl. Qed.
Lemma D_83ecc : decode_any W_83ecc = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ed0 : bv 32 := 0x00008067.
Lemma F_83ed0 : fetch_word AsanUbsan.M.loaded_segments (0x83f18 : word) = Some W_83ed0.
Proof. vm_refl. Qed.
Lemma D_83ed0 : decode_any W_83ed0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

