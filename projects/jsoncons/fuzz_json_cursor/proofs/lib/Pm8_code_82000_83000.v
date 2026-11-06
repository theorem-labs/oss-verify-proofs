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

Definition W_82030 : bv 32 := 0x00060593.
Lemma F_82030 : fetch_word Asan.M.loaded_segments (0x82080 : word) = Some W_82030.
Proof. vm_refl. Qed.
Lemma D_82030 : decode_any W_82030 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82034 : bv 32 := 0x00c0006f.
Lemma F_82034 : fetch_word Asan.M.loaded_segments (0x82084 : word) = Some W_82034.
Proof. vm_refl. Qed.
Lemma D_82034 : decode_any W_82034 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82040 : bv 32 := 0x00040613.
Lemma F_82040 : fetch_word Asan.M.loaded_segments (0x82090 : word) = Some W_82040.
Proof. vm_refl. Qed.
Lemma D_82040 : decode_any W_82040 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82044 : bv 32 := 0x03813083.
Lemma F_82044 : fetch_word Asan.M.loaded_segments (0x82094 : word) = Some W_82044.
Proof. vm_refl. Qed.
Lemma D_82044 : decode_any W_82044 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_82048 : bv 32 := 0x03013403.
Lemma F_82048 : fetch_word Asan.M.loaded_segments (0x82098 : word) = Some W_82048.
Proof. vm_refl. Qed.
Lemma D_82048 : decode_any W_82048 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8204c : bv 32 := 0x02813483.
Lemma F_8204c : fetch_word Asan.M.loaded_segments (0x8209c : word) = Some W_8204c.
Proof. vm_refl. Qed.
Lemma D_8204c : decode_any W_8204c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_82050 : bv 32 := 0x02013903.
Lemma F_82050 : fetch_word Asan.M.loaded_segments (0x820a0 : word) = Some W_82050.
Proof. vm_refl. Qed.
Lemma D_82050 : decode_any W_82050 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_82054 : bv 32 := 0x01813983.
Lemma F_82054 : fetch_word Asan.M.loaded_segments (0x820a4 : word) = Some W_82054.
Proof. vm_refl. Qed.
Lemma D_82054 : decode_any W_82054 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_82058 : bv 32 := 0x01013a03.
Lemma F_82058 : fetch_word Asan.M.loaded_segments (0x820a8 : word) = Some W_82058.
Proof. vm_refl. Qed.
Lemma D_82058 : decode_any W_82058 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8205c : bv 32 := 0x00813a83.
Lemma F_8205c : fetch_word Asan.M.loaded_segments (0x820ac : word) = Some W_8205c.
Proof. vm_refl. Qed.
Lemma D_8205c : decode_any W_8205c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82060 : bv 32 := 0x04010113.
Lemma F_82060 : fetch_word Asan.M.loaded_segments (0x820b0 : word) = Some W_82060.
Proof. vm_refl. Qed.
Lemma D_82060 : decode_any W_82060 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_82064 : bv 32 := 0x00030067.
Lemma F_82064 : fetch_word Asan.M.loaded_segments (0x820b4 : word) = Some W_82064.
Proof. vm_refl. Qed.
Lemma D_82064 : decode_any W_82064 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_821c4 : bv 32 := 0x000d1597.
Lemma F_821c4 : fetch_word Asan.M.loaded_segments (0x82214 : word) = Some W_821c4.
Proof. vm_refl. Qed.
Lemma D_821c4 : decode_any W_821c4 = Some (Auipc 11 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_821c8 : bv 32 := 0xf245b583.
Lemma F_821c8 : fetch_word Asan.M.loaded_segments (0x82218 : word) = Some W_821c8.
Proof. vm_refl. Qed.
Lemma D_821c8 : decode_any W_821c8 = Some (Load SZ8 true 11 11 3876, 4%Z).
Proof. vm_refl. Qed.

Definition W_821cc : bv 32 := 0x0005b583.
Lemma F_821cc : fetch_word Asan.M.loaded_segments (0x8221c : word) = Some W_821cc.
Proof. vm_refl. Qed.
Lemma D_821cc : decode_any W_821cc = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_821d0 : bv 32 := 0xfff58613.
Lemma F_821d0 : fetch_word Asan.M.loaded_segments (0x82220 : word) = Some W_821d0.
Proof. vm_refl. Qed.
Lemma D_821d0 : decode_any W_821d0 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_821d4 : bv 32 := 0x00c5b6b3.
Lemma F_821d4 : fetch_word Asan.M.loaded_segments (0x82224 : word) = Some W_821d4.
Proof. vm_refl. Qed.
Lemma D_821d4 : decode_any W_821d4 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_821d8 : bv 32 := 0xfff68693.
Lemma F_821d8 : fetch_word Asan.M.loaded_segments (0x82228 : word) = Some W_821d8.
Proof. vm_refl. Qed.
Lemma D_821d8 : decode_any W_821d8 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_821dc : bv 32 := 0x00c6f6b3.
Lemma F_821dc : fetch_word Asan.M.loaded_segments (0x8222c : word) = Some W_821dc.
Proof. vm_refl. Qed.
Lemma D_821dc : decode_any W_821dc = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_821e0 : bv 32 := 0x04a6f263.
Lemma F_821e0 : fetch_word Asan.M.loaded_segments (0x82230 : word) = Some W_821e0.
Proof. vm_refl. Qed.
Lemma D_821e0 : decode_any W_821e0 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_821e4 : bv 32 := 0x000d1697.
Lemma F_821e4 : fetch_word Asan.M.loaded_segments (0x82234 : word) = Some W_821e4.
Proof. vm_refl. Qed.
Lemma D_821e4 : decode_any W_821e4 = Some (Auipc 13 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_821e8 : bv 32 := 0xf0c6b683.
Lemma F_821e8 : fetch_word Asan.M.loaded_segments (0x82238 : word) = Some W_821e8.
Proof. vm_refl. Qed.
Lemma D_821e8 : decode_any W_821e8 = Some (Load SZ8 true 13 13 3852, 4%Z).
Proof. vm_refl. Qed.

Definition W_821ec : bv 32 := 0x000d1717.
Lemma F_821ec : fetch_word Asan.M.loaded_segments (0x8223c : word) = Some W_821ec.
Proof. vm_refl. Qed.
Lemma D_821ec : decode_any W_821ec = Some (Auipc 14 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_821f0 : bv 32 := 0xf0c73703.
Lemma F_821f0 : fetch_word Asan.M.loaded_segments (0x82240 : word) = Some W_821f0.
Proof. vm_refl. Qed.
Lemma D_821f0 : decode_any W_821f0 = Some (Load SZ8 true 14 14 3852, 4%Z).
Proof. vm_refl. Qed.

Definition W_821f4 : bv 32 := 0x0006b803.
Lemma F_821f4 : fetch_word Asan.M.loaded_segments (0x82244 : word) = Some W_821f4.
Proof. vm_refl. Qed.
Lemma D_821f4 : decode_any W_821f4 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_821f8 : bv 32 := 0x00073683.
Lemma F_821f8 : fetch_word Asan.M.loaded_segments (0x82248 : word) = Some W_821f8.
Proof. vm_refl. Qed.
Lemma D_821f8 : decode_any W_821f8 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_821fc : bv 32 := 0xfff80793.
Lemma F_821fc : fetch_word Asan.M.loaded_segments (0x8224c : word) = Some W_821fc.
Proof. vm_refl. Qed.
Lemma D_821fc : decode_any W_821fc = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82200 : bv 32 := 0x00a7f463.
Lemma F_82200 : fetch_word Asan.M.loaded_segments (0x82250 : word) = Some W_82200.
Proof. vm_refl. Qed.
Lemma D_82200 : decode_any W_82200 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82208 : bv 32 := 0x000d1717.
Lemma F_82208 : fetch_word Asan.M.loaded_segments (0x82258 : word) = Some W_82208.
Proof. vm_refl. Qed.
Lemma D_82208 : decode_any W_82208 = Some (Auipc 14 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_8220c : bv 32 := 0xef873703.
Lemma F_8220c : fetch_word Asan.M.loaded_segments (0x8225c : word) = Some W_8220c.
Proof. vm_refl. Qed.
Lemma D_8220c : decode_any W_8220c = Some (Load SZ8 true 14 14 3832, 4%Z).
Proof. vm_refl. Qed.

Definition W_82210 : bv 32 := 0x00073283.
Lemma F_82210 : fetch_word Asan.M.loaded_segments (0x82260 : word) = Some W_82210.
Proof. vm_refl. Qed.
Lemma D_82210 : decode_any W_82210 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82214 : bv 32 := 0x0032d713.
Lemma F_82214 : fetch_word Asan.M.loaded_segments (0x82264 : word) = Some W_82214.
Proof. vm_refl. Qed.
Lemma D_82214 : decode_any W_82214 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82218 : bv 32 := 0x00b708b3.
Lemma F_82218 : fetch_word Asan.M.loaded_segments (0x82268 : word) = Some W_82218.
Proof. vm_refl. Qed.
Lemma D_82218 : decode_any W_82218 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8221c : bv 32 := 0x00a2ea63.
Lemma F_8221c : fetch_word Asan.M.loaded_segments (0x8226c : word) = Some W_8221c.
Proof. vm_refl. Qed.
Lemma D_8221c : decode_any W_8221c = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_82220 : bv 32 := 0x00a8f863.
Lemma F_82220 : fetch_word Asan.M.loaded_segments (0x82270 : word) = Some W_82220.
Proof. vm_refl. Qed.
Lemma D_82220 : decode_any W_82220 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_82224 : bv 32 := 0x00355513.
Lemma F_82224 : fetch_word Asan.M.loaded_segments (0x82274 : word) = Some W_82224.
Proof. vm_refl. Qed.
Lemma D_82224 : decode_any W_82224 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82228 : bv 32 := 0x00a58533.
Lemma F_82228 : fetch_word Asan.M.loaded_segments (0x82278 : word) = Some W_82228.
Proof. vm_refl. Qed.
Lemma D_82228 : decode_any W_82228 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8222c : bv 32 := 0x00008067.
Lemma F_8222c : fetch_word Asan.M.loaded_segments (0x8227c : word) = Some W_8222c.
Proof. vm_refl. Qed.
Lemma D_8222c : decode_any W_8222c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82650 : bv 32 := 0xfc010113.
Lemma F_82650 : fetch_word Asan.M.loaded_segments (0x826a0 : word) = Some W_82650.
Proof. vm_refl. Qed.
Lemma D_82650 : decode_any W_82650 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_82654 : bv 32 := 0x02113c23.
Lemma F_82654 : fetch_word Asan.M.loaded_segments (0x826a4 : word) = Some W_82654.
Proof. vm_refl. Qed.
Lemma D_82654 : decode_any W_82654 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_82658 : bv 32 := 0x02813823.
Lemma F_82658 : fetch_word Asan.M.loaded_segments (0x826a8 : word) = Some W_82658.
Proof. vm_refl. Qed.
Lemma D_82658 : decode_any W_82658 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8265c : bv 32 := 0x02913423.
Lemma F_8265c : fetch_word Asan.M.loaded_segments (0x826ac : word) = Some W_8265c.
Proof. vm_refl. Qed.
Lemma D_8265c : decode_any W_8265c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_82660 : bv 32 := 0x03213023.
Lemma F_82660 : fetch_word Asan.M.loaded_segments (0x826b0 : word) = Some W_82660.
Proof. vm_refl. Qed.
Lemma D_82660 : decode_any W_82660 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_82664 : bv 32 := 0x01313c23.
Lemma F_82664 : fetch_word Asan.M.loaded_segments (0x826b4 : word) = Some W_82664.
Proof. vm_refl. Qed.
Lemma D_82664 : decode_any W_82664 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_82668 : bv 32 := 0x01413823.
Lemma F_82668 : fetch_word Asan.M.loaded_segments (0x826b8 : word) = Some W_82668.
Proof. vm_refl. Qed.
Lemma D_82668 : decode_any W_82668 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8266c : bv 32 := 0x01513423.
Lemma F_8266c : fetch_word Asan.M.loaded_segments (0x826bc : word) = Some W_8266c.
Proof. vm_refl. Qed.
Lemma D_8266c : decode_any W_8266c = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82670 : bv 32 := 0x14058c63.
Lemma F_82670 : fetch_word Asan.M.loaded_segments (0x826c0 : word) = Some W_82670.
Proof. vm_refl. Qed.
Lemma D_82670 : decode_any W_82670 = Some (Branch BC_EQ 11 0 344, 4%Z).
Proof. vm_refl. Qed.

Definition W_82674 : bv 32 := 0x00058493.
Lemma F_82674 : fetch_word Asan.M.loaded_segments (0x826c4 : word) = Some W_82674.
Proof. vm_refl. Qed.
Lemma D_82674 : decode_any W_82674 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82678 : bv 32 := 0x00050413.
Lemma F_82678 : fetch_word Asan.M.loaded_segments (0x826c8 : word) = Some W_82678.
Proof. vm_refl. Qed.
Lemma D_82678 : decode_any W_82678 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8267c : bv 32 := 0x000d1517.
Lemma F_8267c : fetch_word Asan.M.loaded_segments (0x826cc : word) = Some W_8267c.
Proof. vm_refl. Qed.
Lemma D_8267c : decode_any W_8267c = Some (Auipc 10 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_82680 : bv 32 := 0xa6c53a83.
Lemma F_82680 : fetch_word Asan.M.loaded_segments (0x826d0 : word) = Some W_82680.
Proof. vm_refl. Qed.
Lemma D_82680 : decode_any W_82680 = Some (Load SZ8 true 21 10 2668, 4%Z).
Proof. vm_refl. Qed.

Definition W_82684 : bv 32 := 0x000ab583.
Lemma F_82684 : fetch_word Asan.M.loaded_segments (0x826d4 : word) = Some W_82684.
Proof. vm_refl. Qed.
Lemma D_82684 : decode_any W_82684 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82688 : bv 32 := 0xfff58513.
Lemma F_82688 : fetch_word Asan.M.loaded_segments (0x826d8 : word) = Some W_82688.
Proof. vm_refl. Qed.
Lemma D_82688 : decode_any W_82688 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8268c : bv 32 := 0x00a5b633.
Lemma F_8268c : fetch_word Asan.M.loaded_segments (0x826dc : word) = Some W_8268c.
Proof. vm_refl. Qed.
Lemma D_8268c : decode_any W_8268c = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_82690 : bv 32 := 0xfff60613.
Lemma F_82690 : fetch_word Asan.M.loaded_segments (0x826e0 : word) = Some W_82690.
Proof. vm_refl. Qed.
Lemma D_82690 : decode_any W_82690 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82694 : bv 32 := 0x00a67633.
Lemma F_82694 : fetch_word Asan.M.loaded_segments (0x826e4 : word) = Some W_82694.
Proof. vm_refl. Qed.
Lemma D_82694 : decode_any W_82694 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_82698 : bv 32 := 0x04867263.
Lemma F_82698 : fetch_word Asan.M.loaded_segments (0x826e8 : word) = Some W_82698.
Proof. vm_refl. Qed.
Lemma D_82698 : decode_any W_82698 = Some (Branch BC_GEU 12 8 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_8269c : bv 32 := 0x000d1697.
Lemma F_8269c : fetch_word Asan.M.loaded_segments (0x826ec : word) = Some W_8269c.
Proof. vm_refl. Qed.
Lemma D_8269c : decode_any W_8269c = Some (Auipc 13 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_826a0 : bv 32 := 0xa546b683.
Lemma F_826a0 : fetch_word Asan.M.loaded_segments (0x826f0 : word) = Some W_826a0.
Proof. vm_refl. Qed.
Lemma D_826a0 : decode_any W_826a0 = Some (Load SZ8 true 13 13 2644, 4%Z).
Proof. vm_refl. Qed.

Definition W_826a4 : bv 32 := 0x000d1717.
Lemma F_826a4 : fetch_word Asan.M.loaded_segments (0x826f4 : word) = Some W_826a4.
Proof. vm_refl. Qed.
Lemma D_826a4 : decode_any W_826a4 = Some (Auipc 14 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_826a8 : bv 32 := 0xa5473703.
Lemma F_826a8 : fetch_word Asan.M.loaded_segments (0x826f8 : word) = Some W_826a8.
Proof. vm_refl. Qed.
Lemma D_826a8 : decode_any W_826a8 = Some (Load SZ8 true 14 14 2644, 4%Z).
Proof. vm_refl. Qed.

Definition W_826ac : bv 32 := 0x0006b803.
Lemma F_826ac : fetch_word Asan.M.loaded_segments (0x826fc : word) = Some W_826ac.
Proof. vm_refl. Qed.
Lemma D_826ac : decode_any W_826ac = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_826b0 : bv 32 := 0x00073683.
Lemma F_826b0 : fetch_word Asan.M.loaded_segments (0x82700 : word) = Some W_826b0.
Proof. vm_refl. Qed.
Lemma D_826b0 : decode_any W_826b0 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_826b4 : bv 32 := 0xfff80793.
Lemma F_826b4 : fetch_word Asan.M.loaded_segments (0x82704 : word) = Some W_826b4.
Proof. vm_refl. Qed.
Lemma D_826b4 : decode_any W_826b4 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_826b8 : bv 32 := 0x0087f463.
Lemma F_826b8 : fetch_word Asan.M.loaded_segments (0x82708 : word) = Some W_826b8.
Proof. vm_refl. Qed.
Lemma D_826b8 : decode_any W_826b8 = Some (Branch BC_GEU 15 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_826c0 : bv 32 := 0x000d1717.
Lemma F_826c0 : fetch_word Asan.M.loaded_segments (0x82710 : word) = Some W_826c0.
Proof. vm_refl. Qed.
Lemma D_826c0 : decode_any W_826c0 = Some (Auipc 14 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_826c4 : bv 32 := 0xa4073703.
Lemma F_826c4 : fetch_word Asan.M.loaded_segments (0x82714 : word) = Some W_826c4.
Proof. vm_refl. Qed.
Lemma D_826c4 : decode_any W_826c4 = Some (Load SZ8 true 14 14 2624, 4%Z).
Proof. vm_refl. Qed.

Definition W_826c8 : bv 32 := 0x00073283.
Lemma F_826c8 : fetch_word Asan.M.loaded_segments (0x82718 : word) = Some W_826c8.
Proof. vm_refl. Qed.
Lemma D_826c8 : decode_any W_826c8 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_826cc : bv 32 := 0x0032d713.
Lemma F_826cc : fetch_word Asan.M.loaded_segments (0x8271c : word) = Some W_826cc.
Proof. vm_refl. Qed.
Lemma D_826cc : decode_any W_826cc = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_826d0 : bv 32 := 0x00b708b3.
Lemma F_826d0 : fetch_word Asan.M.loaded_segments (0x82720 : word) = Some W_826d0.
Proof. vm_refl. Qed.
Lemma D_826d0 : decode_any W_826d0 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_826d4 : bv 32 := 0x1282e063.
Lemma F_826d4 : fetch_word Asan.M.loaded_segments (0x82724 : word) = Some W_826d4.
Proof. vm_refl. Qed.
Lemma D_826d4 : decode_any W_826d4 = Some (Branch BC_LTU 5 8 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_826d8 : bv 32 := 0x1088fe63.
Lemma F_826d8 : fetch_word Asan.M.loaded_segments (0x82728 : word) = Some W_826d8.
Proof. vm_refl. Qed.
Lemma D_826d8 : decode_any W_826d8 = Some (Branch BC_GEU 17 8 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_826dc : bv 32 := 0x00848933.
Lemma F_826dc : fetch_word Asan.M.loaded_segments (0x8272c : word) = Some W_826dc.
Proof. vm_refl. Qed.
Lemma D_826dc : decode_any W_826dc = Some (Op ALU_ADD 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_826e0 : bv 32 := 0x05267263.
Lemma F_826e0 : fetch_word Asan.M.loaded_segments (0x82730 : word) = Some W_826e0.
Proof. vm_refl. Qed.
Lemma D_826e0 : decode_any W_826e0 = Some (Branch BC_GEU 12 18 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_826e4 : bv 32 := 0x000d1617.
Lemma F_826e4 : fetch_word Asan.M.loaded_segments (0x82734 : word) = Some W_826e4.
Proof. vm_refl. Qed.
Lemma D_826e4 : decode_any W_826e4 = Some (Auipc 12 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_826e8 : bv 32 := 0xa0c63603.
Lemma F_826e8 : fetch_word Asan.M.loaded_segments (0x82738 : word) = Some W_826e8.
Proof. vm_refl. Qed.
Lemma D_826e8 : decode_any W_826e8 = Some (Load SZ8 true 12 12 2572, 4%Z).
Proof. vm_refl. Qed.

Definition W_826ec : bv 32 := 0x000d1697.
Lemma F_826ec : fetch_word Asan.M.loaded_segments (0x8273c : word) = Some W_826ec.
Proof. vm_refl. Qed.
Lemma D_826ec : decode_any W_826ec = Some (Auipc 13 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_826f0 : bv 32 := 0xa0c6b683.
Lemma F_826f0 : fetch_word Asan.M.loaded_segments (0x82740 : word) = Some W_826f0.
Proof. vm_refl. Qed.
Lemma D_826f0 : decode_any W_826f0 = Some (Load SZ8 true 13 13 2572, 4%Z).
Proof. vm_refl. Qed.

Definition W_826f4 : bv 32 := 0x00063783.
Lemma F_826f4 : fetch_word Asan.M.loaded_segments (0x82744 : word) = Some W_826f4.
Proof. vm_refl. Qed.
Lemma D_826f4 : decode_any W_826f4 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_826f8 : bv 32 := 0x0006b603.
Lemma F_826f8 : fetch_word Asan.M.loaded_segments (0x82748 : word) = Some W_826f8.
Proof. vm_refl. Qed.
Lemma D_826f8 : decode_any W_826f8 = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_826fc : bv 32 := 0xfff78713.
Lemma F_826fc : fetch_word Asan.M.loaded_segments (0x8274c : word) = Some W_826fc.
Proof. vm_refl. Qed.
Lemma D_826fc : decode_any W_826fc = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82700 : bv 32 := 0x01277463.
Lemma F_82700 : fetch_word Asan.M.loaded_segments (0x82750 : word) = Some W_82700.
Proof. vm_refl. Qed.
Lemma D_82700 : decode_any W_82700 = Some (Branch BC_GEU 14 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82708 : bv 32 := 0x000d1697.
Lemma F_82708 : fetch_word Asan.M.loaded_segments (0x82758 : word) = Some W_82708.
Proof. vm_refl. Qed.
Lemma D_82708 : decode_any W_82708 = Some (Auipc 13 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_8270c : bv 32 := 0x9f86b683.
Lemma F_8270c : fetch_word Asan.M.loaded_segments (0x8275c : word) = Some W_8270c.
Proof. vm_refl. Qed.
Lemma D_8270c : decode_any W_8270c = Some (Load SZ8 true 13 13 2552, 4%Z).
Proof. vm_refl. Qed.

Definition W_82710 : bv 32 := 0x0006b883.
Lemma F_82710 : fetch_word Asan.M.loaded_segments (0x82760 : word) = Some W_82710.
Proof. vm_refl. Qed.
Lemma D_82710 : decode_any W_82710 = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82714 : bv 32 := 0x0038d693.
Lemma F_82714 : fetch_word Asan.M.loaded_segments (0x82764 : word) = Some W_82714.
Proof. vm_refl. Qed.
Lemma D_82714 : decode_any W_82714 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82718 : bv 32 := 0x00b68833.
Lemma F_82718 : fetch_word Asan.M.loaded_segments (0x82768 : word) = Some W_82718.
Proof. vm_refl. Qed.
Lemma D_82718 : decode_any W_82718 = Some (Op ALU_ADD 16 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8271c : bv 32 := 0x1328e463.
Lemma F_8271c : fetch_word Asan.M.loaded_segments (0x8276c : word) = Some W_8271c.
Proof. vm_refl. Qed.
Lemma D_8271c : decode_any W_8271c = Some (Branch BC_LTU 17 18 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_82720 : bv 32 := 0x13287263.
Lemma F_82720 : fetch_word Asan.M.loaded_segments (0x82770 : word) = Some W_82720.
Proof. vm_refl. Qed.
Lemma D_82720 : decode_any W_82720 = Some (Branch BC_GEU 16 18 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_82724 : bv 32 := 0x23247863.
Lemma F_82724 : fetch_word Asan.M.loaded_segments (0x82774 : word) = Some W_82724.
Proof. vm_refl. Qed.
Lemma D_82724 : decode_any W_82724 = Some (Branch BC_GEU 8 18 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_82728 : bv 32 := 0x00740513.
Lemma F_82728 : fetch_word Asan.M.loaded_segments (0x82778 : word) = Some W_82728.
Proof. vm_refl. Qed.
Lemma D_82728 : decode_any W_82728 = Some (OpImm ALU_ADD 10 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8272c : bv 32 := 0xff857513.
Lemma F_8272c : fetch_word Asan.M.loaded_segments (0x8277c : word) = Some W_8272c.
Proof. vm_refl. Qed.
Lemma D_8272c : decode_any W_8272c = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_82730 : bv 32 := 0xff897a13.
Lemma F_82730 : fetch_word Asan.M.loaded_segments (0x82780 : word) = Some W_82730.
Proof. vm_refl. Qed.
Lemma D_82730 : decode_any W_82730 = Some (OpImm ALU_AND 20 18 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_82734 : bv 32 := 0xa91ff0ef.
Lemma F_82734 : fetch_word Asan.M.loaded_segments (0x82784 : word) = Some W_82734.
Proof. vm_refl. Qed.
Lemma D_82734 : decode_any W_82734 = Some (Jal 1 2095760, 4%Z).
Proof. vm_refl. Qed.

Definition W_82738 : bv 32 := 0x00050993.
Lemma F_82738 : fetch_word Asan.M.loaded_segments (0x82788 : word) = Some W_82738.
Proof. vm_refl. Qed.
Lemma D_82738 : decode_any W_82738 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8273c : bv 32 := 0x000a0513.
Lemma F_8273c : fetch_word Asan.M.loaded_segments (0x8278c : word) = Some W_8273c.
Proof. vm_refl. Qed.
Lemma D_8273c : decode_any W_8273c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82740 : bv 32 := 0xa85ff0ef.
Lemma F_82740 : fetch_word Asan.M.loaded_segments (0x82790 : word) = Some W_82740.
Proof. vm_refl. Qed.
Lemma D_82740 : decode_any W_82740 = Some (Jal 1 2095748, 4%Z).
Proof. vm_refl. Qed.

Definition W_82744 : bv 32 := 0x000ab583.
Lemma F_82744 : fetch_word Asan.M.loaded_segments (0x82794 : word) = Some W_82744.
Proof. vm_refl. Qed.
Lemma D_82744 : decode_any W_82744 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82748 : bv 32 := 0x00345613.
Lemma F_82748 : fetch_word Asan.M.loaded_segments (0x82798 : word) = Some W_82748.
Proof. vm_refl. Qed.
Lemma D_82748 : decode_any W_82748 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8274c : bv 32 := 0x00c58633.
Lemma F_8274c : fetch_word Asan.M.loaded_segments (0x8279c : word) = Some W_8274c.
Proof. vm_refl. Qed.
Lemma D_8274c : decode_any W_8274c = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82750 : bv 32 := 0x00060603.
Lemma F_82750 : fetch_word Asan.M.loaded_segments (0x827a0 : word) = Some W_82750.
Proof. vm_refl. Qed.
Lemma D_82750 : decode_any W_82750 = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82754 : bv 32 := 0x00060663.
Lemma F_82754 : fetch_word Asan.M.loaded_segments (0x827a4 : word) = Some W_82754.
Proof. vm_refl. Qed.
Lemma D_82754 : decode_any W_82754 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82758 : bv 32 := 0x00747693.
Lemma F_82758 : fetch_word Asan.M.loaded_segments (0x827a8 : word) = Some W_82758.
Proof. vm_refl. Qed.
Lemma D_82758 : decode_any W_82758 = Some (OpImm ALU_AND 13 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8275c : bv 32 := 0x02c6d063.
Lemma F_8275c : fetch_word Asan.M.loaded_segments (0x827ac : word) = Some W_8275c.
Proof. vm_refl. Qed.
Lemma D_8275c : decode_any W_8275c = Some (Branch BC_GE 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_82760 : bv 32 := 0xfff90913.
Lemma F_82760 : fetch_word Asan.M.loaded_segments (0x827b0 : word) = Some W_82760.
Proof. vm_refl. Qed.
Lemma D_82760 : decode_any W_82760 = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82764 : bv 32 := 0x00395613.
Lemma F_82764 : fetch_word Asan.M.loaded_segments (0x827b4 : word) = Some W_82764.
Proof. vm_refl. Qed.
Lemma D_82764 : decode_any W_82764 = Some (ShiftImm ALU_SRL 12 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82768 : bv 32 := 0x00c585b3.
Lemma F_82768 : fetch_word Asan.M.loaded_segments (0x827b8 : word) = Some W_82768.
Proof. vm_refl. Qed.
Lemma D_82768 : decode_any W_82768 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8276c : bv 32 := 0x00058583.
Lemma F_8276c : fetch_word Asan.M.loaded_segments (0x827bc : word) = Some W_8276c.
Proof. vm_refl. Qed.
Lemma D_8276c : decode_any W_8276c = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82770 : bv 32 := 0x04058263.
Lemma F_82770 : fetch_word Asan.M.loaded_segments (0x827c0 : word) = Some W_82770.
Proof. vm_refl. Qed.
Lemma D_82770 : decode_any W_82770 = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_82774 : bv 32 := 0x00797613.
Lemma F_82774 : fetch_word Asan.M.loaded_segments (0x827c4 : word) = Some W_82774.
Proof. vm_refl. Qed.
Lemma D_82774 : decode_any W_82774 = Some (OpImm ALU_AND 12 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82778 : bv 32 := 0x02b64e63.
Lemma F_82778 : fetch_word Asan.M.loaded_segments (0x827c8 : word) = Some W_82778.
Proof. vm_refl. Qed.
Lemma D_82778 : decode_any W_82778 = Some (Branch BC_LT 12 11 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_827b4 : bv 32 := 0x00a9fa63.
Lemma F_827b4 : fetch_word Asan.M.loaded_segments (0x82804 : word) = Some W_827b4.
Proof. vm_refl. Qed.
Lemma D_827b4 : decode_any W_827b4 = Some (Branch BC_GEU 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_827b8 : bv 32 := 0x413505b3.
Lemma F_827b8 : fetch_word Asan.M.loaded_segments (0x82808 : word) = Some W_827b8.
Proof. vm_refl. Qed.
Lemma D_827b8 : decode_any W_827b8 = Some (Op ALU_SUB 11 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_827bc : bv 32 := 0x00098513.
Lemma F_827bc : fetch_word Asan.M.loaded_segments (0x8280c : word) = Some W_827bc.
Proof. vm_refl. Qed.
Lemma D_827bc : decode_any W_827bc = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_827c0 : bv 32 := 0x37c100ef.
Lemma F_827c0 : fetch_word Asan.M.loaded_segments (0x82810 : word) = Some W_827c0.
Proof. vm_refl. Qed.
Lemma D_827c0 : decode_any W_827c0 = Some (Jal 1 66428, 4%Z).
Proof. vm_refl. Qed.

Definition W_827c4 : bv 32 := 0xfa050ce3.
Lemma F_827c4 : fetch_word Asan.M.loaded_segments (0x82814 : word) = Some W_827c4.
Proof. vm_refl. Qed.
Lemma D_827c4 : decode_any W_827c4 = Some (Branch BC_EQ 10 0 8120, 4%Z).
Proof. vm_refl. Qed.

Definition W_827c8 : bv 32 := 0x00000413.
Lemma F_827c8 : fetch_word Asan.M.loaded_segments (0x82818 : word) = Some W_827c8.
Proof. vm_refl. Qed.
Lemma D_827c8 : decode_any W_827c8 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_827cc : bv 32 := 0x00040513.
Lemma F_827cc : fetch_word Asan.M.loaded_segments (0x8281c : word) = Some W_827cc.
Proof. vm_refl. Qed.
Lemma D_827cc : decode_any W_827cc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_827d0 : bv 32 := 0x03813083.
Lemma F_827d0 : fetch_word Asan.M.loaded_segments (0x82820 : word) = Some W_827d0.
Proof. vm_refl. Qed.
Lemma D_827d0 : decode_any W_827d0 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_827d4 : bv 32 := 0x03013403.
Lemma F_827d4 : fetch_word Asan.M.loaded_segments (0x82824 : word) = Some W_827d4.
Proof. vm_refl. Qed.
Lemma D_827d4 : decode_any W_827d4 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_827d8 : bv 32 := 0x02813483.
Lemma F_827d8 : fetch_word Asan.M.loaded_segments (0x82828 : word) = Some W_827d8.
Proof. vm_refl. Qed.
Lemma D_827d8 : decode_any W_827d8 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_827dc : bv 32 := 0x02013903.
Lemma F_827dc : fetch_word Asan.M.loaded_segments (0x8282c : word) = Some W_827dc.
Proof. vm_refl. Qed.
Lemma D_827dc : decode_any W_827dc = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_827e0 : bv 32 := 0x01813983.
Lemma F_827e0 : fetch_word Asan.M.loaded_segments (0x82830 : word) = Some W_827e0.
Proof. vm_refl. Qed.
Lemma D_827e0 : decode_any W_827e0 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_827e4 : bv 32 := 0x01013a03.
Lemma F_827e4 : fetch_word Asan.M.loaded_segments (0x82834 : word) = Some W_827e4.
Proof. vm_refl. Qed.
Lemma D_827e4 : decode_any W_827e4 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_827e8 : bv 32 := 0x00813a83.
Lemma F_827e8 : fetch_word Asan.M.loaded_segments (0x82838 : word) = Some W_827e8.
Proof. vm_refl. Qed.
Lemma D_827e8 : decode_any W_827e8 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_827ec : bv 32 := 0x04010113.
Lemma F_827ec : fetch_word Asan.M.loaded_segments (0x8283c : word) = Some W_827ec.
Proof. vm_refl. Qed.
Lemma D_827ec : decode_any W_827ec = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_827f0 : bv 32 := 0x00008067.
Lemma F_827f0 : fetch_word Asan.M.loaded_segments (0x82840 : word) = Some W_827f0.
Proof. vm_refl. Qed.
Lemma D_827f0 : decode_any W_827f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f88 : bv 32 := 0xfb010113.
Lemma F_82f88 : fetch_word Asan.M.loaded_segments (0x82fd8 : word) = Some W_82f88.
Proof. vm_refl. Qed.
Lemma D_82f88 : decode_any W_82f88 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f8c : bv 32 := 0x04113423.
Lemma F_82f8c : fetch_word Asan.M.loaded_segments (0x82fdc : word) = Some W_82f8c.
Proof. vm_refl. Qed.
Lemma D_82f8c : decode_any W_82f8c = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f90 : bv 32 := 0x04813023.
Lemma F_82f90 : fetch_word Asan.M.loaded_segments (0x82fe0 : word) = Some W_82f90.
Proof. vm_refl. Qed.
Lemma D_82f90 : decode_any W_82f90 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f94 : bv 32 := 0x000d0517.
Lemma F_82f94 : fetch_word Asan.M.loaded_segments (0x82fe4 : word) = Some W_82f94.
Proof. vm_refl. Qed.
Lemma D_82f94 : decode_any W_82f94 = Some (Auipc 10 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f98 : bv 32 := 0x19453503.
Lemma F_82f98 : fetch_word Asan.M.loaded_segments (0x82fe8 : word) = Some W_82f98.
Proof. vm_refl. Qed.
Lemma D_82f98 : decode_any W_82f98 = Some (Load SZ8 true 10 10 404, 4%Z).
Proof. vm_refl. Qed.

Definition W_82f9c : bv 32 := 0x0a051463.
Lemma F_82f9c : fetch_word Asan.M.loaded_segments (0x82fec : word) = Some W_82f9c.
Proof. vm_refl. Qed.
Lemma D_82f9c : decode_any W_82f9c = Some (Branch BC_NE 10 0 168, 4%Z).
Proof. vm_refl. Qed.

