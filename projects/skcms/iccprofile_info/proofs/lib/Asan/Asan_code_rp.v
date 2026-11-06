(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_53724 : bv 32 := 0x0004b597.
Lemma F_53724 : fetch_word Asan.M.loaded_segments (0x53724 : word) = Some W_53724.
Proof. vm_refl. Qed.
Lemma D_53724 : decode_any W_53724 = Some (Auipc 11 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53728 : bv 32 := 0x3cc5b583.
Lemma F_53728 : fetch_word Asan.M.loaded_segments (0x53728 : word) = Some W_53728.
Proof. vm_refl. Qed.
Lemma D_53728 : decode_any W_53728 = Some (Load SZ8 true 11 11 972, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5372c : bv 32 := 0x0005b583.
Lemma F_5372c : fetch_word Asan.M.loaded_segments (0x5372c : word) = Some W_5372c.
Proof. vm_refl. Qed.
Lemma D_5372c : decode_any W_5372c = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53730 : bv 32 := 0xfff58613.
Lemma F_53730 : fetch_word Asan.M.loaded_segments (0x53730 : word) = Some W_53730.
Proof. vm_refl. Qed.
Lemma D_53730 : decode_any W_53730 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53734 : bv 32 := 0x00c5b6b3.
Lemma F_53734 : fetch_word Asan.M.loaded_segments (0x53734 : word) = Some W_53734.
Proof. vm_refl. Qed.
Lemma D_53734 : decode_any W_53734 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53738 : bv 32 := 0xfff68693.
Lemma F_53738 : fetch_word Asan.M.loaded_segments (0x53738 : word) = Some W_53738.
Proof. vm_refl. Qed.
Lemma D_53738 : decode_any W_53738 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5373c : bv 32 := 0x00c6f6b3.
Lemma F_5373c : fetch_word Asan.M.loaded_segments (0x5373c : word) = Some W_5373c.
Proof. vm_refl. Qed.
Lemma D_5373c : decode_any W_5373c = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53740 : bv 32 := 0x04a6f263.
Lemma F_53740 : fetch_word Asan.M.loaded_segments (0x53740 : word) = Some W_53740.
Proof. vm_refl. Qed.
Lemma D_53740 : decode_any W_53740 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53744 : bv 32 := 0x0004b697.
Lemma F_53744 : fetch_word Asan.M.loaded_segments (0x53744 : word) = Some W_53744.
Proof. vm_refl. Qed.
Lemma D_53744 : decode_any W_53744 = Some (Auipc 13 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53748 : bv 32 := 0x3b46b683.
Lemma F_53748 : fetch_word Asan.M.loaded_segments (0x53748 : word) = Some W_53748.
Proof. vm_refl. Qed.
Lemma D_53748 : decode_any W_53748 = Some (Load SZ8 true 13 13 948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5374c : bv 32 := 0x0004b717.
Lemma F_5374c : fetch_word Asan.M.loaded_segments (0x5374c : word) = Some W_5374c.
Proof. vm_refl. Qed.
Lemma D_5374c : decode_any W_5374c = Some (Auipc 14 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53750 : bv 32 := 0x3b473703.
Lemma F_53750 : fetch_word Asan.M.loaded_segments (0x53750 : word) = Some W_53750.
Proof. vm_refl. Qed.
Lemma D_53750 : decode_any W_53750 = Some (Load SZ8 true 14 14 948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53754 : bv 32 := 0x0006b803.
Lemma F_53754 : fetch_word Asan.M.loaded_segments (0x53754 : word) = Some W_53754.
Proof. vm_refl. Qed.
Lemma D_53754 : decode_any W_53754 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53758 : bv 32 := 0x00073683.
Lemma F_53758 : fetch_word Asan.M.loaded_segments (0x53758 : word) = Some W_53758.
Proof. vm_refl. Qed.
Lemma D_53758 : decode_any W_53758 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5375c : bv 32 := 0xfff80793.
Lemma F_5375c : fetch_word Asan.M.loaded_segments (0x5375c : word) = Some W_5375c.
Proof. vm_refl. Qed.
Lemma D_5375c : decode_any W_5375c = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53760 : bv 32 := 0x00a7f463.
Lemma F_53760 : fetch_word Asan.M.loaded_segments (0x53760 : word) = Some W_53760.
Proof. vm_refl. Qed.
Lemma D_53760 : decode_any W_53760 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53764 : bv 32 := 0x02a6f063.
Lemma F_53764 : fetch_word Asan.M.loaded_segments (0x53764 : word) = Some W_53764.
Proof. vm_refl. Qed.
Lemma D_53764 : decode_any W_53764 = Some (Branch BC_GEU 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53768 : bv 32 := 0x0004b717.
Lemma F_53768 : fetch_word Asan.M.loaded_segments (0x53768 : word) = Some W_53768.
Proof. vm_refl. Qed.
Lemma D_53768 : decode_any W_53768 = Some (Auipc 14 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5376c : bv 32 := 0x3a073703.
Lemma F_5376c : fetch_word Asan.M.loaded_segments (0x5376c : word) = Some W_5376c.
Proof. vm_refl. Qed.
Lemma D_5376c : decode_any W_5376c = Some (Load SZ8 true 14 14 928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53770 : bv 32 := 0x00073283.
Lemma F_53770 : fetch_word Asan.M.loaded_segments (0x53770 : word) = Some W_53770.
Proof. vm_refl. Qed.
Lemma D_53770 : decode_any W_53770 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53774 : bv 32 := 0x0032d713.
Lemma F_53774 : fetch_word Asan.M.loaded_segments (0x53774 : word) = Some W_53774.
Proof. vm_refl. Qed.
Lemma D_53774 : decode_any W_53774 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53778 : bv 32 := 0x00b708b3.
Lemma F_53778 : fetch_word Asan.M.loaded_segments (0x53778 : word) = Some W_53778.
Proof. vm_refl. Qed.
Lemma D_53778 : decode_any W_53778 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5377c : bv 32 := 0x00a2ea63.
Lemma F_5377c : fetch_word Asan.M.loaded_segments (0x5377c : word) = Some W_5377c.
Proof. vm_refl. Qed.
Lemma D_5377c : decode_any W_5377c = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53780 : bv 32 := 0x00a8f863.
Lemma F_53780 : fetch_word Asan.M.loaded_segments (0x53780 : word) = Some W_53780.
Proof. vm_refl. Qed.
Lemma D_53780 : decode_any W_53780 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53784 : bv 32 := 0x00355513.
Lemma F_53784 : fetch_word Asan.M.loaded_segments (0x53784 : word) = Some W_53784.
Proof. vm_refl. Qed.
Lemma D_53784 : decode_any W_53784 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53788 : bv 32 := 0x00a58533.
Lemma F_53788 : fetch_word Asan.M.loaded_segments (0x53788 : word) = Some W_53788.
Proof. vm_refl. Qed.
Lemma D_53788 : decode_any W_53788 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5378c : bv 32 := 0x00008067.
Lemma F_5378c : fetch_word Asan.M.loaded_segments (0x5378c : word) = Some W_5378c.
Proof. vm_refl. Qed.
Lemma D_5378c : decode_any W_5378c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53bb0 : bv 32 := 0xfc010113.
Lemma F_53bb0 : fetch_word Asan.M.loaded_segments (0x53bb0 : word) = Some W_53bb0.
Proof. vm_refl. Qed.
Lemma D_53bb0 : decode_any W_53bb0 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53bb4 : bv 32 := 0x02113c23.
Lemma F_53bb4 : fetch_word Asan.M.loaded_segments (0x53bb4 : word) = Some W_53bb4.
Proof. vm_refl. Qed.
Lemma D_53bb4 : decode_any W_53bb4 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53bb8 : bv 32 := 0x02813823.
Lemma F_53bb8 : fetch_word Asan.M.loaded_segments (0x53bb8 : word) = Some W_53bb8.
Proof. vm_refl. Qed.
Lemma D_53bb8 : decode_any W_53bb8 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53bbc : bv 32 := 0x02913423.
Lemma F_53bbc : fetch_word Asan.M.loaded_segments (0x53bbc : word) = Some W_53bbc.
Proof. vm_refl. Qed.
Lemma D_53bbc : decode_any W_53bbc = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53bc0 : bv 32 := 0x03213023.
Lemma F_53bc0 : fetch_word Asan.M.loaded_segments (0x53bc0 : word) = Some W_53bc0.
Proof. vm_refl. Qed.
Lemma D_53bc0 : decode_any W_53bc0 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53bc4 : bv 32 := 0x01313c23.
Lemma F_53bc4 : fetch_word Asan.M.loaded_segments (0x53bc4 : word) = Some W_53bc4.
Proof. vm_refl. Qed.
Lemma D_53bc4 : decode_any W_53bc4 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53bc8 : bv 32 := 0x01413823.
Lemma F_53bc8 : fetch_word Asan.M.loaded_segments (0x53bc8 : word) = Some W_53bc8.
Proof. vm_refl. Qed.
Lemma D_53bc8 : decode_any W_53bc8 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53bcc : bv 32 := 0x01513423.
Lemma F_53bcc : fetch_word Asan.M.loaded_segments (0x53bcc : word) = Some W_53bcc.
Proof. vm_refl. Qed.
Lemma D_53bcc : decode_any W_53bcc = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53bd0 : bv 32 := 0x14058c63.
Lemma F_53bd0 : fetch_word Asan.M.loaded_segments (0x53bd0 : word) = Some W_53bd0.
Proof. vm_refl. Qed.
Lemma D_53bd0 : decode_any W_53bd0 = Some (Branch BC_EQ 11 0 344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53bd4 : bv 32 := 0x00058493.
Lemma F_53bd4 : fetch_word Asan.M.loaded_segments (0x53bd4 : word) = Some W_53bd4.
Proof. vm_refl. Qed.
Lemma D_53bd4 : decode_any W_53bd4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53bd8 : bv 32 := 0x00050413.
Lemma F_53bd8 : fetch_word Asan.M.loaded_segments (0x53bd8 : word) = Some W_53bd8.
Proof. vm_refl. Qed.
Lemma D_53bd8 : decode_any W_53bd8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53bdc : bv 32 := 0x0004b517.
Lemma F_53bdc : fetch_word Asan.M.loaded_segments (0x53bdc : word) = Some W_53bdc.
Proof. vm_refl. Qed.
Lemma D_53bdc : decode_any W_53bdc = Some (Auipc 10 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53be0 : bv 32 := 0xf1453a83.
Lemma F_53be0 : fetch_word Asan.M.loaded_segments (0x53be0 : word) = Some W_53be0.
Proof. vm_refl. Qed.
Lemma D_53be0 : decode_any W_53be0 = Some (Load SZ8 true 21 10 3860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53be4 : bv 32 := 0x000ab583.
Lemma F_53be4 : fetch_word Asan.M.loaded_segments (0x53be4 : word) = Some W_53be4.
Proof. vm_refl. Qed.
Lemma D_53be4 : decode_any W_53be4 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53be8 : bv 32 := 0xfff58513.
Lemma F_53be8 : fetch_word Asan.M.loaded_segments (0x53be8 : word) = Some W_53be8.
Proof. vm_refl. Qed.
Lemma D_53be8 : decode_any W_53be8 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53bec : bv 32 := 0x00a5b633.
Lemma F_53bec : fetch_word Asan.M.loaded_segments (0x53bec : word) = Some W_53bec.
Proof. vm_refl. Qed.
Lemma D_53bec : decode_any W_53bec = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53bf0 : bv 32 := 0xfff60613.
Lemma F_53bf0 : fetch_word Asan.M.loaded_segments (0x53bf0 : word) = Some W_53bf0.
Proof. vm_refl. Qed.
Lemma D_53bf0 : decode_any W_53bf0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53bf4 : bv 32 := 0x00a67633.
Lemma F_53bf4 : fetch_word Asan.M.loaded_segments (0x53bf4 : word) = Some W_53bf4.
Proof. vm_refl. Qed.
Lemma D_53bf4 : decode_any W_53bf4 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53bf8 : bv 32 := 0x04867263.
Lemma F_53bf8 : fetch_word Asan.M.loaded_segments (0x53bf8 : word) = Some W_53bf8.
Proof. vm_refl. Qed.
Lemma D_53bf8 : decode_any W_53bf8 = Some (Branch BC_GEU 12 8 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53bfc : bv 32 := 0x0004b697.
Lemma F_53bfc : fetch_word Asan.M.loaded_segments (0x53bfc : word) = Some W_53bfc.
Proof. vm_refl. Qed.
Lemma D_53bfc : decode_any W_53bfc = Some (Auipc 13 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c00 : bv 32 := 0xefc6b683.
Lemma F_53c00 : fetch_word Asan.M.loaded_segments (0x53c00 : word) = Some W_53c00.
Proof. vm_refl. Qed.
Lemma D_53c00 : decode_any W_53c00 = Some (Load SZ8 true 13 13 3836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c04 : bv 32 := 0x0004b717.
Lemma F_53c04 : fetch_word Asan.M.loaded_segments (0x53c04 : word) = Some W_53c04.
Proof. vm_refl. Qed.
Lemma D_53c04 : decode_any W_53c04 = Some (Auipc 14 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c08 : bv 32 := 0xefc73703.
Lemma F_53c08 : fetch_word Asan.M.loaded_segments (0x53c08 : word) = Some W_53c08.
Proof. vm_refl. Qed.
Lemma D_53c08 : decode_any W_53c08 = Some (Load SZ8 true 14 14 3836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c0c : bv 32 := 0x0006b803.
Lemma F_53c0c : fetch_word Asan.M.loaded_segments (0x53c0c : word) = Some W_53c0c.
Proof. vm_refl. Qed.
Lemma D_53c0c : decode_any W_53c0c = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c10 : bv 32 := 0x00073683.
Lemma F_53c10 : fetch_word Asan.M.loaded_segments (0x53c10 : word) = Some W_53c10.
Proof. vm_refl. Qed.
Lemma D_53c10 : decode_any W_53c10 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c14 : bv 32 := 0xfff80793.
Lemma F_53c14 : fetch_word Asan.M.loaded_segments (0x53c14 : word) = Some W_53c14.
Proof. vm_refl. Qed.
Lemma D_53c14 : decode_any W_53c14 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c18 : bv 32 := 0x0087f463.
Lemma F_53c18 : fetch_word Asan.M.loaded_segments (0x53c18 : word) = Some W_53c18.
Proof. vm_refl. Qed.
Lemma D_53c18 : decode_any W_53c18 = Some (Branch BC_GEU 15 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c1c : bv 32 := 0x0286f063.
Lemma F_53c1c : fetch_word Asan.M.loaded_segments (0x53c1c : word) = Some W_53c1c.
Proof. vm_refl. Qed.
Lemma D_53c1c : decode_any W_53c1c = Some (Branch BC_GEU 13 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c20 : bv 32 := 0x0004b717.
Lemma F_53c20 : fetch_word Asan.M.loaded_segments (0x53c20 : word) = Some W_53c20.
Proof. vm_refl. Qed.
Lemma D_53c20 : decode_any W_53c20 = Some (Auipc 14 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c24 : bv 32 := 0xee873703.
Lemma F_53c24 : fetch_word Asan.M.loaded_segments (0x53c24 : word) = Some W_53c24.
Proof. vm_refl. Qed.
Lemma D_53c24 : decode_any W_53c24 = Some (Load SZ8 true 14 14 3816, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c28 : bv 32 := 0x00073283.
Lemma F_53c28 : fetch_word Asan.M.loaded_segments (0x53c28 : word) = Some W_53c28.
Proof. vm_refl. Qed.
Lemma D_53c28 : decode_any W_53c28 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c2c : bv 32 := 0x0032d713.
Lemma F_53c2c : fetch_word Asan.M.loaded_segments (0x53c2c : word) = Some W_53c2c.
Proof. vm_refl. Qed.
Lemma D_53c2c : decode_any W_53c2c = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c30 : bv 32 := 0x00b708b3.
Lemma F_53c30 : fetch_word Asan.M.loaded_segments (0x53c30 : word) = Some W_53c30.
Proof. vm_refl. Qed.
Lemma D_53c30 : decode_any W_53c30 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c34 : bv 32 := 0x1282e063.
Lemma F_53c34 : fetch_word Asan.M.loaded_segments (0x53c34 : word) = Some W_53c34.
Proof. vm_refl. Qed.
Lemma D_53c34 : decode_any W_53c34 = Some (Branch BC_LTU 5 8 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c38 : bv 32 := 0x1088fe63.
Lemma F_53c38 : fetch_word Asan.M.loaded_segments (0x53c38 : word) = Some W_53c38.
Proof. vm_refl. Qed.
Lemma D_53c38 : decode_any W_53c38 = Some (Branch BC_GEU 17 8 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c3c : bv 32 := 0x00848933.
Lemma F_53c3c : fetch_word Asan.M.loaded_segments (0x53c3c : word) = Some W_53c3c.
Proof. vm_refl. Qed.
Lemma D_53c3c : decode_any W_53c3c = Some (Op ALU_ADD 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c40 : bv 32 := 0x05267263.
Lemma F_53c40 : fetch_word Asan.M.loaded_segments (0x53c40 : word) = Some W_53c40.
Proof. vm_refl. Qed.
Lemma D_53c40 : decode_any W_53c40 = Some (Branch BC_GEU 12 18 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c44 : bv 32 := 0x0004b617.
Lemma F_53c44 : fetch_word Asan.M.loaded_segments (0x53c44 : word) = Some W_53c44.
Proof. vm_refl. Qed.
Lemma D_53c44 : decode_any W_53c44 = Some (Auipc 12 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c48 : bv 32 := 0xeb463603.
Lemma F_53c48 : fetch_word Asan.M.loaded_segments (0x53c48 : word) = Some W_53c48.
Proof. vm_refl. Qed.
Lemma D_53c48 : decode_any W_53c48 = Some (Load SZ8 true 12 12 3764, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c4c : bv 32 := 0x0004b697.
Lemma F_53c4c : fetch_word Asan.M.loaded_segments (0x53c4c : word) = Some W_53c4c.
Proof. vm_refl. Qed.
Lemma D_53c4c : decode_any W_53c4c = Some (Auipc 13 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c50 : bv 32 := 0xeb46b683.
Lemma F_53c50 : fetch_word Asan.M.loaded_segments (0x53c50 : word) = Some W_53c50.
Proof. vm_refl. Qed.
Lemma D_53c50 : decode_any W_53c50 = Some (Load SZ8 true 13 13 3764, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c54 : bv 32 := 0x00063783.
Lemma F_53c54 : fetch_word Asan.M.loaded_segments (0x53c54 : word) = Some W_53c54.
Proof. vm_refl. Qed.
Lemma D_53c54 : decode_any W_53c54 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c58 : bv 32 := 0x0006b603.
Lemma F_53c58 : fetch_word Asan.M.loaded_segments (0x53c58 : word) = Some W_53c58.
Proof. vm_refl. Qed.
Lemma D_53c58 : decode_any W_53c58 = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c5c : bv 32 := 0xfff78713.
Lemma F_53c5c : fetch_word Asan.M.loaded_segments (0x53c5c : word) = Some W_53c5c.
Proof. vm_refl. Qed.
Lemma D_53c5c : decode_any W_53c5c = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c60 : bv 32 := 0x01277463.
Lemma F_53c60 : fetch_word Asan.M.loaded_segments (0x53c60 : word) = Some W_53c60.
Proof. vm_refl. Qed.
Lemma D_53c60 : decode_any W_53c60 = Some (Branch BC_GEU 14 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c64 : bv 32 := 0x03267063.
Lemma F_53c64 : fetch_word Asan.M.loaded_segments (0x53c64 : word) = Some W_53c64.
Proof. vm_refl. Qed.
Lemma D_53c64 : decode_any W_53c64 = Some (Branch BC_GEU 12 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c68 : bv 32 := 0x0004b697.
Lemma F_53c68 : fetch_word Asan.M.loaded_segments (0x53c68 : word) = Some W_53c68.
Proof. vm_refl. Qed.
Lemma D_53c68 : decode_any W_53c68 = Some (Auipc 13 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c6c : bv 32 := 0xea06b683.
Lemma F_53c6c : fetch_word Asan.M.loaded_segments (0x53c6c : word) = Some W_53c6c.
Proof. vm_refl. Qed.
Lemma D_53c6c : decode_any W_53c6c = Some (Load SZ8 true 13 13 3744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c70 : bv 32 := 0x0006b883.
Lemma F_53c70 : fetch_word Asan.M.loaded_segments (0x53c70 : word) = Some W_53c70.
Proof. vm_refl. Qed.
Lemma D_53c70 : decode_any W_53c70 = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c74 : bv 32 := 0x0038d693.
Lemma F_53c74 : fetch_word Asan.M.loaded_segments (0x53c74 : word) = Some W_53c74.
Proof. vm_refl. Qed.
Lemma D_53c74 : decode_any W_53c74 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c78 : bv 32 := 0x00b68833.
Lemma F_53c78 : fetch_word Asan.M.loaded_segments (0x53c78 : word) = Some W_53c78.
Proof. vm_refl. Qed.
Lemma D_53c78 : decode_any W_53c78 = Some (Op ALU_ADD 16 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c7c : bv 32 := 0x1328e463.
Lemma F_53c7c : fetch_word Asan.M.loaded_segments (0x53c7c : word) = Some W_53c7c.
Proof. vm_refl. Qed.
Lemma D_53c7c : decode_any W_53c7c = Some (Branch BC_LTU 17 18 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c80 : bv 32 := 0x13287263.
Lemma F_53c80 : fetch_word Asan.M.loaded_segments (0x53c80 : word) = Some W_53c80.
Proof. vm_refl. Qed.
Lemma D_53c80 : decode_any W_53c80 = Some (Branch BC_GEU 16 18 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c84 : bv 32 := 0x23247863.
Lemma F_53c84 : fetch_word Asan.M.loaded_segments (0x53c84 : word) = Some W_53c84.
Proof. vm_refl. Qed.
Lemma D_53c84 : decode_any W_53c84 = Some (Branch BC_GEU 8 18 560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c88 : bv 32 := 0x00740513.
Lemma F_53c88 : fetch_word Asan.M.loaded_segments (0x53c88 : word) = Some W_53c88.
Proof. vm_refl. Qed.
Lemma D_53c88 : decode_any W_53c88 = Some (OpImm ALU_ADD 10 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c8c : bv 32 := 0xff857513.
Lemma F_53c8c : fetch_word Asan.M.loaded_segments (0x53c8c : word) = Some W_53c8c.
Proof. vm_refl. Qed.
Lemma D_53c8c : decode_any W_53c8c = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c90 : bv 32 := 0xff897a13.
Lemma F_53c90 : fetch_word Asan.M.loaded_segments (0x53c90 : word) = Some W_53c90.
Proof. vm_refl. Qed.
Lemma D_53c90 : decode_any W_53c90 = Some (OpImm ALU_AND 20 18 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c94 : bv 32 := 0xa91ff0ef.
Lemma F_53c94 : fetch_word Asan.M.loaded_segments (0x53c94 : word) = Some W_53c94.
Proof. vm_refl. Qed.
Lemma D_53c94 : decode_any W_53c94 = Some (Jal 1 2095760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c98 : bv 32 := 0x00050993.
Lemma F_53c98 : fetch_word Asan.M.loaded_segments (0x53c98 : word) = Some W_53c98.
Proof. vm_refl. Qed.
Lemma D_53c98 : decode_any W_53c98 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53c9c : bv 32 := 0x000a0513.
Lemma F_53c9c : fetch_word Asan.M.loaded_segments (0x53c9c : word) = Some W_53c9c.
Proof. vm_refl. Qed.
Lemma D_53c9c : decode_any W_53c9c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ca0 : bv 32 := 0xa85ff0ef.
Lemma F_53ca0 : fetch_word Asan.M.loaded_segments (0x53ca0 : word) = Some W_53ca0.
Proof. vm_refl. Qed.
Lemma D_53ca0 : decode_any W_53ca0 = Some (Jal 1 2095748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ca4 : bv 32 := 0x000ab583.
Lemma F_53ca4 : fetch_word Asan.M.loaded_segments (0x53ca4 : word) = Some W_53ca4.
Proof. vm_refl. Qed.
Lemma D_53ca4 : decode_any W_53ca4 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ca8 : bv 32 := 0x00345613.
Lemma F_53ca8 : fetch_word Asan.M.loaded_segments (0x53ca8 : word) = Some W_53ca8.
Proof. vm_refl. Qed.
Lemma D_53ca8 : decode_any W_53ca8 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cac : bv 32 := 0x00c58633.
Lemma F_53cac : fetch_word Asan.M.loaded_segments (0x53cac : word) = Some W_53cac.
Proof. vm_refl. Qed.
Lemma D_53cac : decode_any W_53cac = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cb0 : bv 32 := 0x00060603.
Lemma F_53cb0 : fetch_word Asan.M.loaded_segments (0x53cb0 : word) = Some W_53cb0.
Proof. vm_refl. Qed.
Lemma D_53cb0 : decode_any W_53cb0 = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cb4 : bv 32 := 0x00060663.
Lemma F_53cb4 : fetch_word Asan.M.loaded_segments (0x53cb4 : word) = Some W_53cb4.
Proof. vm_refl. Qed.
Lemma D_53cb4 : decode_any W_53cb4 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cb8 : bv 32 := 0x00747693.
Lemma F_53cb8 : fetch_word Asan.M.loaded_segments (0x53cb8 : word) = Some W_53cb8.
Proof. vm_refl. Qed.
Lemma D_53cb8 : decode_any W_53cb8 = Some (OpImm ALU_AND 13 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cbc : bv 32 := 0x02c6d063.
Lemma F_53cbc : fetch_word Asan.M.loaded_segments (0x53cbc : word) = Some W_53cbc.
Proof. vm_refl. Qed.
Lemma D_53cbc : decode_any W_53cbc = Some (Branch BC_GE 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cc0 : bv 32 := 0xfff90913.
Lemma F_53cc0 : fetch_word Asan.M.loaded_segments (0x53cc0 : word) = Some W_53cc0.
Proof. vm_refl. Qed.
Lemma D_53cc0 : decode_any W_53cc0 = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cc4 : bv 32 := 0x00395613.
Lemma F_53cc4 : fetch_word Asan.M.loaded_segments (0x53cc4 : word) = Some W_53cc4.
Proof. vm_refl. Qed.
Lemma D_53cc4 : decode_any W_53cc4 = Some (ShiftImm ALU_SRL 12 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cc8 : bv 32 := 0x00c585b3.
Lemma F_53cc8 : fetch_word Asan.M.loaded_segments (0x53cc8 : word) = Some W_53cc8.
Proof. vm_refl. Qed.
Lemma D_53cc8 : decode_any W_53cc8 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ccc : bv 32 := 0x00058583.
Lemma F_53ccc : fetch_word Asan.M.loaded_segments (0x53ccc : word) = Some W_53ccc.
Proof. vm_refl. Qed.
Lemma D_53ccc : decode_any W_53ccc = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cd0 : bv 32 := 0x04058263.
Lemma F_53cd0 : fetch_word Asan.M.loaded_segments (0x53cd0 : word) = Some W_53cd0.
Proof. vm_refl. Qed.
Lemma D_53cd0 : decode_any W_53cd0 = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cd4 : bv 32 := 0x00797613.
Lemma F_53cd4 : fetch_word Asan.M.loaded_segments (0x53cd4 : word) = Some W_53cd4.
Proof. vm_refl. Qed.
Lemma D_53cd4 : decode_any W_53cd4 = Some (OpImm ALU_AND 12 18 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cd8 : bv 32 := 0x02b64e63.
Lemma F_53cd8 : fetch_word Asan.M.loaded_segments (0x53cd8 : word) = Some W_53cd8.
Proof. vm_refl. Qed.
Lemma D_53cd8 : decode_any W_53cd8 = Some (Branch BC_LT 12 11 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cdc : bv 32 := 0x000ab503.
Lemma F_53cdc : fetch_word Asan.M.loaded_segments (0x53cdc : word) = Some W_53cdc.
Proof. vm_refl. Qed.
Lemma D_53cdc : decode_any W_53cdc = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ce0 : bv 32 := 0x00040593.
Lemma F_53ce0 : fetch_word Asan.M.loaded_segments (0x53ce0 : word) = Some W_53ce0.
Proof. vm_refl. Qed.
Lemma D_53ce0 : decode_any W_53ce0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ce4 : bv 32 := 0x0140006f.
Lemma F_53ce4 : fetch_word Asan.M.loaded_segments (0x53ce4 : word) = Some W_53ce4.
Proof. vm_refl. Qed.
Lemma D_53ce4 : decode_any W_53ce4 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ce8 : bv 32 := 0x00140413.
Lemma F_53ce8 : fetch_word Asan.M.loaded_segments (0x53ce8 : word) = Some W_53ce8.
Proof. vm_refl. Qed.
Lemma D_53ce8 : decode_any W_53ce8 = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cec : bv 32 := 0xfff48493.
Lemma F_53cec : fetch_word Asan.M.loaded_segments (0x53cec : word) = Some W_53cec.
Proof. vm_refl. Qed.
Lemma D_53cec : decode_any W_53cec = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cf0 : bv 32 := 0x00158593.
Lemma F_53cf0 : fetch_word Asan.M.loaded_segments (0x53cf0 : word) = Some W_53cf0.
Proof. vm_refl. Qed.
Lemma D_53cf0 : decode_any W_53cf0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cf4 : bv 32 := 0x1e048063.
Lemma F_53cf4 : fetch_word Asan.M.loaded_segments (0x53cf4 : word) = Some W_53cf4.
Proof. vm_refl. Qed.
Lemma D_53cf4 : decode_any W_53cf4 = Some (Branch BC_EQ 9 0 480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cf8 : bv 32 := 0x00345613.
Lemma F_53cf8 : fetch_word Asan.M.loaded_segments (0x53cf8 : word) = Some W_53cf8.
Proof. vm_refl. Qed.
Lemma D_53cf8 : decode_any W_53cf8 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cfc : bv 32 := 0x00c50633.
Lemma F_53cfc : fetch_word Asan.M.loaded_segments (0x53cfc : word) = Some W_53cfc.
Proof. vm_refl. Qed.
Lemma D_53cfc : decode_any W_53cfc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d00 : bv 32 := 0x00060603.
Lemma F_53d00 : fetch_word Asan.M.loaded_segments (0x53d00 : word) = Some W_53d00.
Proof. vm_refl. Qed.
Lemma D_53d00 : decode_any W_53d00 = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d04 : bv 32 := 0xfe0602e3.
Lemma F_53d04 : fetch_word Asan.M.loaded_segments (0x53d04 : word) = Some W_53d04.
Proof. vm_refl. Qed.
Lemma D_53d04 : decode_any W_53d04 = Some (Branch BC_EQ 12 0 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d08 : bv 32 := 0x0075f693.
Lemma F_53d08 : fetch_word Asan.M.loaded_segments (0x53d08 : word) = Some W_53d08.
Proof. vm_refl. Qed.
Lemma D_53d08 : decode_any W_53d08 = Some (OpImm ALU_AND 13 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d0c : bv 32 := 0xfcc6cee3.
Lemma F_53d0c : fetch_word Asan.M.loaded_segments (0x53d0c : word) = Some W_53d0c.
Proof. vm_refl. Qed.
Lemma D_53d0c : decode_any W_53d0c = Some (Branch BC_LT 13 12 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d10 : bv 32 := 0x01c0006f.
Lemma F_53d10 : fetch_word Asan.M.loaded_segments (0x53d10 : word) = Some W_53d10.
Proof. vm_refl. Qed.
Lemma D_53d10 : decode_any W_53d10 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d14 : bv 32 := 0x00a9fa63.
Lemma F_53d14 : fetch_word Asan.M.loaded_segments (0x53d14 : word) = Some W_53d14.
Proof. vm_refl. Qed.
Lemma D_53d14 : decode_any W_53d14 = Some (Branch BC_GEU 19 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d18 : bv 32 := 0x413505b3.
Lemma F_53d18 : fetch_word Asan.M.loaded_segments (0x53d18 : word) = Some W_53d18.
Proof. vm_refl. Qed.
Lemma D_53d18 : decode_any W_53d18 = Some (Op ALU_SUB 11 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d1c : bv 32 := 0x00098513.
Lemma F_53d1c : fetch_word Asan.M.loaded_segments (0x53d1c : word) = Some W_53d1c.
Proof. vm_refl. Qed.
Lemma D_53d1c : decode_any W_53d1c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d20 : bv 32 := 0x3d10f0ef.
Lemma F_53d20 : fetch_word Asan.M.loaded_segments (0x53d20 : word) = Some W_53d20.
Proof. vm_refl. Qed.
Lemma D_53d20 : decode_any W_53d20 = Some (Jal 1 64464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d24 : bv 32 := 0xfa050ce3.
Lemma F_53d24 : fetch_word Asan.M.loaded_segments (0x53d24 : word) = Some W_53d24.
Proof. vm_refl. Qed.
Lemma D_53d24 : decode_any W_53d24 = Some (Branch BC_EQ 10 0 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d28 : bv 32 := 0x00000413.
Lemma F_53d28 : fetch_word Asan.M.loaded_segments (0x53d28 : word) = Some W_53d28.
Proof. vm_refl. Qed.
Lemma D_53d28 : decode_any W_53d28 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d2c : bv 32 := 0x00040513.
Lemma F_53d2c : fetch_word Asan.M.loaded_segments (0x53d2c : word) = Some W_53d2c.
Proof. vm_refl. Qed.
Lemma D_53d2c : decode_any W_53d2c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d30 : bv 32 := 0x03813083.
Lemma F_53d30 : fetch_word Asan.M.loaded_segments (0x53d30 : word) = Some W_53d30.
Proof. vm_refl. Qed.
Lemma D_53d30 : decode_any W_53d30 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d34 : bv 32 := 0x03013403.
Lemma F_53d34 : fetch_word Asan.M.loaded_segments (0x53d34 : word) = Some W_53d34.
Proof. vm_refl. Qed.
Lemma D_53d34 : decode_any W_53d34 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d38 : bv 32 := 0x02813483.
Lemma F_53d38 : fetch_word Asan.M.loaded_segments (0x53d38 : word) = Some W_53d38.
Proof. vm_refl. Qed.
Lemma D_53d38 : decode_any W_53d38 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d3c : bv 32 := 0x02013903.
Lemma F_53d3c : fetch_word Asan.M.loaded_segments (0x53d3c : word) = Some W_53d3c.
Proof. vm_refl. Qed.
Lemma D_53d3c : decode_any W_53d3c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d40 : bv 32 := 0x01813983.
Lemma F_53d40 : fetch_word Asan.M.loaded_segments (0x53d40 : word) = Some W_53d40.
Proof. vm_refl. Qed.
Lemma D_53d40 : decode_any W_53d40 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d44 : bv 32 := 0x01013a03.
Lemma F_53d44 : fetch_word Asan.M.loaded_segments (0x53d44 : word) = Some W_53d44.
Proof. vm_refl. Qed.
Lemma D_53d44 : decode_any W_53d44 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d48 : bv 32 := 0x00813a83.
Lemma F_53d48 : fetch_word Asan.M.loaded_segments (0x53d48 : word) = Some W_53d48.
Proof. vm_refl. Qed.
Lemma D_53d48 : decode_any W_53d48 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d4c : bv 32 := 0x04010113.
Lemma F_53d4c : fetch_word Asan.M.loaded_segments (0x53d4c : word) = Some W_53d4c.
Proof. vm_refl. Qed.
Lemma D_53d4c : decode_any W_53d4c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d50 : bv 32 := 0x00008067.
Lemma F_53d50 : fetch_word Asan.M.loaded_segments (0x53d50 : word) = Some W_53d50.
Proof. vm_refl. Qed.
Lemma D_53d50 : decode_any W_53d50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d54 : bv 32 := 0x0004b297.
Lemma F_53d54 : fetch_word Asan.M.loaded_segments (0x53d54 : word) = Some W_53d54.
Proof. vm_refl. Qed.
Lemma D_53d54 : decode_any W_53d54 = Some (Auipc 5 75, 4%Z).
Proof. vm_refl. Qed.
