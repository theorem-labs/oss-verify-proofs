(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_66140 : bv 32 := 0x02060063.
Lemma F_66140 : fetch_word Asan.M.loaded_segments (0x66140 : word) = Some W_66140.
Proof. vm_refl. Qed.
Lemma D_66140 : decode_any W_66140 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66144 : bv 32 := 0x00c50633.
Lemma F_66144 : fetch_word Asan.M.loaded_segments (0x66144 : word) = Some W_66144.
Proof. vm_refl. Qed.
Lemma D_66144 : decode_any W_66144 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66148 : bv 32 := 0x00050693.
Lemma F_66148 : fetch_word Asan.M.loaded_segments (0x66148 : word) = Some W_66148.
Proof. vm_refl. Qed.
Lemma D_66148 : decode_any W_66148 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6614c : bv 32 := 0x0005c703.
Lemma F_6614c : fetch_word Asan.M.loaded_segments (0x6614c : word) = Some W_6614c.
Proof. vm_refl. Qed.
Lemma D_6614c : decode_any W_6614c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66150 : bv 32 := 0x00e68023.
Lemma F_66150 : fetch_word Asan.M.loaded_segments (0x66150 : word) = Some W_66150.
Proof. vm_refl. Qed.
Lemma D_66150 : decode_any W_66150 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66154 : bv 32 := 0x00168693.
Lemma F_66154 : fetch_word Asan.M.loaded_segments (0x66154 : word) = Some W_66154.
Proof. vm_refl. Qed.
Lemma D_66154 : decode_any W_66154 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66158 : bv 32 := 0x00158593.
Lemma F_66158 : fetch_word Asan.M.loaded_segments (0x66158 : word) = Some W_66158.
Proof. vm_refl. Qed.
Lemma D_66158 : decode_any W_66158 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6615c : bv 32 := 0xfec698e3.
Lemma F_6615c : fetch_word Asan.M.loaded_segments (0x6615c : word) = Some W_6615c.
Proof. vm_refl. Qed.
Lemma D_6615c : decode_any W_6615c = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66160 : bv 32 := 0x00008067.
Lemma F_66160 : fetch_word Asan.M.loaded_segments (0x66160 : word) = Some W_66160.
Proof. vm_refl. Qed.
Lemma D_66160 : decode_any W_66160 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661bc : bv 32 := 0x00a666b3.
Lemma F_661bc : fetch_word Asan.M.loaded_segments (0x661bc : word) = Some W_661bc.
Proof. vm_refl. Qed.
Lemma D_661bc : decode_any W_661bc = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661c0 : bv 32 := 0x00f6f693.
Lemma F_661c0 : fetch_word Asan.M.loaded_segments (0x661c0 : word) = Some W_661c0.
Proof. vm_refl. Qed.
Lemma D_661c0 : decode_any W_661c0 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661c4 : bv 32 := 0x02068063.
Lemma F_661c4 : fetch_word Asan.M.loaded_segments (0x661c4 : word) = Some W_661c4.
Proof. vm_refl. Qed.
Lemma D_661c4 : decode_any W_661c4 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661c8 : bv 32 := 0x04060863.
Lemma F_661c8 : fetch_word Asan.M.loaded_segments (0x661c8 : word) = Some W_661c8.
Proof. vm_refl. Qed.
Lemma D_661c8 : decode_any W_661c8 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661cc : bv 32 := 0x00c50633.
Lemma F_661cc : fetch_word Asan.M.loaded_segments (0x661cc : word) = Some W_661cc.
Proof. vm_refl. Qed.
Lemma D_661cc : decode_any W_661cc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661d0 : bv 32 := 0x00050693.
Lemma F_661d0 : fetch_word Asan.M.loaded_segments (0x661d0 : word) = Some W_661d0.
Proof. vm_refl. Qed.
Lemma D_661d0 : decode_any W_661d0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661d4 : bv 32 := 0x00b68023.
Lemma F_661d4 : fetch_word Asan.M.loaded_segments (0x661d4 : word) = Some W_661d4.
Proof. vm_refl. Qed.
Lemma D_661d4 : decode_any W_661d4 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661d8 : bv 32 := 0x00168693.
Lemma F_661d8 : fetch_word Asan.M.loaded_segments (0x661d8 : word) = Some W_661d8.
Proof. vm_refl. Qed.
Lemma D_661d8 : decode_any W_661d8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661dc : bv 32 := 0xfec69ce3.
Lemma F_661dc : fetch_word Asan.M.loaded_segments (0x661dc : word) = Some W_661dc.
Proof. vm_refl. Qed.
Lemma D_661dc : decode_any W_661dc = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661e0 : bv 32 := 0x0380006f.
Lemma F_661e0 : fetch_word Asan.M.loaded_segments (0x661e0 : word) = Some W_661e0.
Proof. vm_refl. Qed.
Lemma D_661e0 : decode_any W_661e0 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661e4 : bv 32 := 0x02060a63.
Lemma F_661e4 : fetch_word Asan.M.loaded_segments (0x661e4 : word) = Some W_661e4.
Proof. vm_refl. Qed.
Lemma D_661e4 : decode_any W_661e4 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661e8 : bv 32 := 0x00c50633.
Lemma F_661e8 : fetch_word Asan.M.loaded_segments (0x661e8 : word) = Some W_661e8.
Proof. vm_refl. Qed.
Lemma D_661e8 : decode_any W_661e8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661ec : bv 32 := 0x00859693.
Lemma F_661ec : fetch_word Asan.M.loaded_segments (0x661ec : word) = Some W_661ec.
Proof. vm_refl. Qed.
Lemma D_661ec : decode_any W_661ec = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661f0 : bv 32 := 0x00b6e5b3.
Lemma F_661f0 : fetch_word Asan.M.loaded_segments (0x661f0 : word) = Some W_661f0.
Proof. vm_refl. Qed.
Lemma D_661f0 : decode_any W_661f0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661f4 : bv 32 := 0x01059693.
Lemma F_661f4 : fetch_word Asan.M.loaded_segments (0x661f4 : word) = Some W_661f4.
Proof. vm_refl. Qed.
Lemma D_661f4 : decode_any W_661f4 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661f8 : bv 32 := 0x00b6e5b3.
Lemma F_661f8 : fetch_word Asan.M.loaded_segments (0x661f8 : word) = Some W_661f8.
Proof. vm_refl. Qed.
Lemma D_661f8 : decode_any W_661f8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661fc : bv 32 := 0x02059693.
Lemma F_661fc : fetch_word Asan.M.loaded_segments (0x661fc : word) = Some W_661fc.
Proof. vm_refl. Qed.
Lemma D_661fc : decode_any W_661fc = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66200 : bv 32 := 0x00b6e5b3.
Lemma F_66200 : fetch_word Asan.M.loaded_segments (0x66200 : word) = Some W_66200.
Proof. vm_refl. Qed.
Lemma D_66200 : decode_any W_66200 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66204 : bv 32 := 0x00050693.
Lemma F_66204 : fetch_word Asan.M.loaded_segments (0x66204 : word) = Some W_66204.
Proof. vm_refl. Qed.
Lemma D_66204 : decode_any W_66204 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66208 : bv 32 := 0x00b6b023.
Lemma F_66208 : fetch_word Asan.M.loaded_segments (0x66208 : word) = Some W_66208.
Proof. vm_refl. Qed.
Lemma D_66208 : decode_any W_66208 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6620c : bv 32 := 0x00b6b423.
Lemma F_6620c : fetch_word Asan.M.loaded_segments (0x6620c : word) = Some W_6620c.
Proof. vm_refl. Qed.
Lemma D_6620c : decode_any W_6620c = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66210 : bv 32 := 0x01068693.
Lemma F_66210 : fetch_word Asan.M.loaded_segments (0x66210 : word) = Some W_66210.
Proof. vm_refl. Qed.
Lemma D_66210 : decode_any W_66210 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66214 : bv 32 := 0xfec6eae3.
Lemma F_66214 : fetch_word Asan.M.loaded_segments (0x66214 : word) = Some W_66214.
Proof. vm_refl. Qed.
Lemma D_66214 : decode_any W_66214 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66218 : bv 32 := 0x00008067.
Lemma F_66218 : fetch_word Asan.M.loaded_segments (0x66218 : word) = Some W_66218.
Proof. vm_refl. Qed.
Lemma D_66218 : decode_any W_66218 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666ec : bv 32 := 0xff010113.
Lemma F_666ec : fetch_word Asan.M.loaded_segments (0x666ec : word) = Some W_666ec.
Proof. vm_refl. Qed.
Lemma D_666ec : decode_any W_666ec = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666f0 : bv 32 := 0x00113423.
Lemma F_666f0 : fetch_word Asan.M.loaded_segments (0x666f0 : word) = Some W_666f0.
Proof. vm_refl. Qed.
Lemma D_666f0 : decode_any W_666f0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666f4 : bv 32 := 0x00058693.
Lemma F_666f4 : fetch_word Asan.M.loaded_segments (0x666f4 : word) = Some W_666f4.
Proof. vm_refl. Qed.
Lemma D_666f4 : decode_any W_666f4 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666f8 : bv 32 := 0x00100713.
Lemma F_666f8 : fetch_word Asan.M.loaded_segments (0x666f8 : word) = Some W_666f8.
Proof. vm_refl. Qed.
Lemma D_666f8 : decode_any W_666f8 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666fc : bv 32 := 0x02871713.
Lemma F_666fc : fetch_word Asan.M.loaded_segments (0x666fc : word) = Some W_666fc.
Proof. vm_refl. Qed.
Lemma D_666fc : decode_any W_666fc = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66700 : bv 32 := 0x00170593.
Lemma F_66700 : fetch_word Asan.M.loaded_segments (0x66700 : word) = Some W_66700.
Proof. vm_refl. Qed.
Lemma D_66700 : decode_any W_66700 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66704 : bv 32 := 0x08b6f263.
Lemma F_66704 : fetch_word Asan.M.loaded_segments (0x66704 : word) = Some W_66704.
Proof. vm_refl. Qed.
Lemma D_66704 : decode_any W_66704 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66708 : bv 32 := 0x00000593.
Lemma F_66708 : fetch_word Asan.M.loaded_segments (0x66708 : word) = Some W_66708.
Proof. vm_refl. Qed.
Lemma D_66708 : decode_any W_66708 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6670c : bv 32 := 0x00d50733.
Lemma F_6670c : fetch_word Asan.M.loaded_segments (0x6670c : word) = Some W_6670c.
Proof. vm_refl. Qed.
Lemma D_6670c : decode_any W_6670c = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66710 : bv 32 := 0x00750793.
Lemma F_66710 : fetch_word Asan.M.loaded_segments (0x66710 : word) = Some W_66710.
Proof. vm_refl. Qed.
Lemma D_66710 : decode_any W_66710 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66714 : bv 32 := 0xff87f793.
Lemma F_66714 : fetch_word Asan.M.loaded_segments (0x66714 : word) = Some W_66714.
Proof. vm_refl. Qed.
Lemma D_66714 : decode_any W_66714 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66718 : bv 32 := 0xff877613.
Lemma F_66718 : fetch_word Asan.M.loaded_segments (0x66718 : word) = Some W_66718.
Proof. vm_refl. Qed.
Lemma D_66718 : decode_any W_66718 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6671c : bv 32 := 0x02f57463.
Lemma F_6671c : fetch_word Asan.M.loaded_segments (0x6671c : word) = Some W_6671c.
Proof. vm_refl. Qed.
Lemma D_6671c : decode_any W_6671c = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66720 : bv 32 := 0x02068263.
Lemma F_66720 : fetch_word Asan.M.loaded_segments (0x66720 : word) = Some W_66720.
Proof. vm_refl. Qed.
Lemma D_66720 : decode_any W_66720 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66724 : bv 32 := 0x00000593.
Lemma F_66724 : fetch_word Asan.M.loaded_segments (0x66724 : word) = Some W_66724.
Proof. vm_refl. Qed.
Lemma D_66724 : decode_any W_66724 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66728 : bv 32 := 0x00150693.
Lemma F_66728 : fetch_word Asan.M.loaded_segments (0x66728 : word) = Some W_66728.
Proof. vm_refl. Qed.
Lemma D_66728 : decode_any W_66728 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6672c : bv 32 := 0x00068813.
Lemma F_6672c : fetch_word Asan.M.loaded_segments (0x6672c : word) = Some W_6672c.
Proof. vm_refl. Qed.
Lemma D_6672c : decode_any W_6672c = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66730 : bv 32 := 0xfff6c683.
Lemma F_66730 : fetch_word Asan.M.loaded_segments (0x66730 : word) = Some W_66730.
Proof. vm_refl. Qed.
Lemma D_66730 : decode_any W_66730 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66734 : bv 32 := 0x00d5e5b3.
Lemma F_66734 : fetch_word Asan.M.loaded_segments (0x66734 : word) = Some W_66734.
Proof. vm_refl. Qed.
Lemma D_66734 : decode_any W_66734 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66738 : bv 32 := 0x00f87663.
Lemma F_66738 : fetch_word Asan.M.loaded_segments (0x66738 : word) = Some W_66738.
Proof. vm_refl. Qed.
Lemma D_66738 : decode_any W_66738 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6673c : bv 32 := 0x00180693.
Lemma F_6673c : fetch_word Asan.M.loaded_segments (0x6673c : word) = Some W_6673c.
Proof. vm_refl. Qed.
Lemma D_6673c : decode_any W_6673c = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66740 : bv 32 := 0xfee866e3.
Lemma F_66740 : fetch_word Asan.M.loaded_segments (0x66740 : word) = Some W_66740.
Proof. vm_refl. Qed.
Lemma D_66740 : decode_any W_66740 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66744 : bv 32 := 0x00c7fa63.
Lemma F_66744 : fetch_word Asan.M.loaded_segments (0x66744 : word) = Some W_66744.
Proof. vm_refl. Qed.
Lemma D_66744 : decode_any W_66744 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66748 : bv 32 := 0x0007b683.
Lemma F_66748 : fetch_word Asan.M.loaded_segments (0x66748 : word) = Some W_66748.
Proof. vm_refl. Qed.
Lemma D_66748 : decode_any W_66748 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6674c : bv 32 := 0x00878793.
Lemma F_6674c : fetch_word Asan.M.loaded_segments (0x6674c : word) = Some W_6674c.
Proof. vm_refl. Qed.
Lemma D_6674c : decode_any W_6674c = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66750 : bv 32 := 0x00b6e5b3.
Lemma F_66750 : fetch_word Asan.M.loaded_segments (0x66750 : word) = Some W_66750.
Proof. vm_refl. Qed.
Lemma D_66750 : decode_any W_66750 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66754 : bv 32 := 0xfec7eae3.
Lemma F_66754 : fetch_word Asan.M.loaded_segments (0x66754 : word) = Some W_66754.
Proof. vm_refl. Qed.
Lemma D_66754 : decode_any W_66754 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66758 : bv 32 := 0x02a66063.
Lemma F_66758 : fetch_word Asan.M.loaded_segments (0x66758 : word) = Some W_66758.
Proof. vm_refl. Qed.
Lemma D_66758 : decode_any W_66758 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6675c : bv 32 := 0x00e67e63.
Lemma F_6675c : fetch_word Asan.M.loaded_segments (0x6675c : word) = Some W_6675c.
Proof. vm_refl. Qed.
Lemma D_6675c : decode_any W_6675c = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66760 : bv 32 := 0x40c70733.
Lemma F_66760 : fetch_word Asan.M.loaded_segments (0x66760 : word) = Some W_66760.
Proof. vm_refl. Qed.
Lemma D_66760 : decode_any W_66760 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66764 : bv 32 := 0x00064503.
Lemma F_66764 : fetch_word Asan.M.loaded_segments (0x66764 : word) = Some W_66764.
Proof. vm_refl. Qed.
Lemma D_66764 : decode_any W_66764 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66768 : bv 32 := 0xfff70713.
Lemma F_66768 : fetch_word Asan.M.loaded_segments (0x66768 : word) = Some W_66768.
Proof. vm_refl. Qed.
Lemma D_66768 : decode_any W_66768 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6676c : bv 32 := 0x00a5e5b3.
Lemma F_6676c : fetch_word Asan.M.loaded_segments (0x6676c : word) = Some W_6676c.
Proof. vm_refl. Qed.
Lemma D_6676c : decode_any W_6676c = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66770 : bv 32 := 0x00160613.
Lemma F_66770 : fetch_word Asan.M.loaded_segments (0x66770 : word) = Some W_66770.
Proof. vm_refl. Qed.
Lemma D_66770 : decode_any W_66770 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66774 : bv 32 := 0xfe0718e3.
Lemma F_66774 : fetch_word Asan.M.loaded_segments (0x66774 : word) = Some W_66774.
Proof. vm_refl. Qed.
Lemma D_66774 : decode_any W_66774 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66778 : bv 32 := 0x0015b513.
Lemma F_66778 : fetch_word Asan.M.loaded_segments (0x66778 : word) = Some W_66778.
Proof. vm_refl. Qed.
Lemma D_66778 : decode_any W_66778 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6677c : bv 32 := 0x00813083.
Lemma F_6677c : fetch_word Asan.M.loaded_segments (0x6677c : word) = Some W_6677c.
Proof. vm_refl. Qed.
Lemma D_6677c : decode_any W_6677c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66780 : bv 32 := 0x01010113.
Lemma F_66780 : fetch_word Asan.M.loaded_segments (0x66780 : word) = Some W_66780.
Proof. vm_refl. Qed.
Lemma D_66780 : decode_any W_66780 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66784 : bv 32 := 0x00008067.
Lemma F_66784 : fetch_word Asan.M.loaded_segments (0x66784 : word) = Some W_66784.
Proof. vm_refl. Qed.
Lemma D_66784 : decode_any W_66784 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
