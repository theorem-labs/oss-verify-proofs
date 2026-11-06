(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import AsanUbsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_164440 : bv 32 := 0x0e060a63.
Lemma F_164440 : fetch_word AsanUbsan.M.loaded_segments (0x164790 : word) = Some W_164440.
Proof. vm_refl. Qed.
Lemma D_164440 : decode_any W_164440 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164444 : bv 32 := 0x00b50023.
Lemma F_164444 : fetch_word AsanUbsan.M.loaded_segments (0x164794 : word) = Some W_164444.
Proof. vm_refl. Qed.
Lemma D_164444 : decode_any W_164444 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164448 : bv 32 := 0x00c506b3.
Lemma F_164448 : fetch_word AsanUbsan.M.loaded_segments (0x164798 : word) = Some W_164448.
Proof. vm_refl. Qed.
Lemma D_164448 : decode_any W_164448 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16444c : bv 32 := 0x00300713.
Lemma F_16444c : fetch_word AsanUbsan.M.loaded_segments (0x16479c : word) = Some W_16444c.
Proof. vm_refl. Qed.
Lemma D_16444c : decode_any W_16444c = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164450 : bv 32 := 0xfeb68fa3.
Lemma F_164450 : fetch_word AsanUbsan.M.loaded_segments (0x1647a0 : word) = Some W_164450.
Proof. vm_refl. Qed.
Lemma D_164450 : decode_any W_164450 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164454 : bv 32 := 0x0ee66063.
Lemma F_164454 : fetch_word AsanUbsan.M.loaded_segments (0x1647a4 : word) = Some W_164454.
Proof. vm_refl. Qed.
Lemma D_164454 : decode_any W_164454 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164458 : bv 32 := 0x00b500a3.
Lemma F_164458 : fetch_word AsanUbsan.M.loaded_segments (0x1647a8 : word) = Some W_164458.
Proof. vm_refl. Qed.
Lemma D_164458 : decode_any W_164458 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16445c : bv 32 := 0x00b50123.
Lemma F_16445c : fetch_word AsanUbsan.M.loaded_segments (0x1647ac : word) = Some W_16445c.
Proof. vm_refl. Qed.
Lemma D_16445c : decode_any W_16445c = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164460 : bv 32 := 0x00700713.
Lemma F_164460 : fetch_word AsanUbsan.M.loaded_segments (0x1647b0 : word) = Some W_164460.
Proof. vm_refl. Qed.
Lemma D_164460 : decode_any W_164460 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164464 : bv 32 := 0xfeb68ea3.
Lemma F_164464 : fetch_word AsanUbsan.M.loaded_segments (0x1647b4 : word) = Some W_164464.
Proof. vm_refl. Qed.
Lemma D_164464 : decode_any W_164464 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164468 : bv 32 := 0xfeb68f23.
Lemma F_164468 : fetch_word AsanUbsan.M.loaded_segments (0x1647b8 : word) = Some W_164468.
Proof. vm_refl. Qed.
Lemma D_164468 : decode_any W_164468 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16446c : bv 32 := 0x0ce66463.
Lemma F_16446c : fetch_word AsanUbsan.M.loaded_segments (0x1647bc : word) = Some W_16446c.
Proof. vm_refl. Qed.
Lemma D_16446c : decode_any W_16446c = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164470 : bv 32 := 0x00b501a3.
Lemma F_164470 : fetch_word AsanUbsan.M.loaded_segments (0x1647c0 : word) = Some W_164470.
Proof. vm_refl. Qed.
Lemma D_164470 : decode_any W_164470 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164474 : bv 32 := 0x00900793.
Lemma F_164474 : fetch_word AsanUbsan.M.loaded_segments (0x1647c4 : word) = Some W_164474.
Proof. vm_refl. Qed.
Lemma D_164474 : decode_any W_164474 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164478 : bv 32 := 0xfeb68e23.
Lemma F_164478 : fetch_word AsanUbsan.M.loaded_segments (0x1647c8 : word) = Some W_164478.
Proof. vm_refl. Qed.
Lemma D_164478 : decode_any W_164478 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16447c : bv 32 := 0x0af66c63.
Lemma F_16447c : fetch_word AsanUbsan.M.loaded_segments (0x1647cc : word) = Some W_16447c.
Proof. vm_refl. Qed.
Lemma D_16447c : decode_any W_16447c = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164480 : bv 32 := 0x40a006bb.
Lemma F_164480 : fetch_word AsanUbsan.M.loaded_segments (0x1647d0 : word) = Some W_164480.
Proof. vm_refl. Qed.
Lemma D_164480 : decode_any W_164480 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164484 : bv 32 := 0x03859813.
Lemma F_164484 : fetch_word AsanUbsan.M.loaded_segments (0x1647d4 : word) = Some W_164484.
Proof. vm_refl. Qed.
Lemma D_164484 : decode_any W_164484 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164488 : bv 32 := 0x101015b7.
Lemma F_164488 : fetch_word AsanUbsan.M.loaded_segments (0x1647d8 : word) = Some W_164488.
Proof. vm_refl. Qed.
Lemma D_164488 : decode_any W_164488 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16448c : bv 32 := 0x0036f693.
Lemma F_16448c : fetch_word AsanUbsan.M.loaded_segments (0x1647dc : word) = Some W_16448c.
Proof. vm_refl. Qed.
Lemma D_16448c : decode_any W_16448c = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164490 : bv 32 := 0x00459713.
Lemma F_164490 : fetch_word AsanUbsan.M.loaded_segments (0x1647e0 : word) = Some W_164490.
Proof. vm_refl. Qed.
Lemma D_164490 : decode_any W_164490 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164494 : bv 32 := 0x40d60633.
Lemma F_164494 : fetch_word AsanUbsan.M.loaded_segments (0x1647e4 : word) = Some W_164494.
Proof. vm_refl. Qed.
Lemma D_164494 : decode_any W_164494 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164498 : bv 32 := 0x00d505b3.
Lemma F_164498 : fetch_word AsanUbsan.M.loaded_segments (0x1647e8 : word) = Some W_164498.
Proof. vm_refl. Qed.
Lemma D_164498 : decode_any W_164498 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16449c : bv 32 := 0x10070693.
Lemma F_16449c : fetch_word AsanUbsan.M.loaded_segments (0x1647ec : word) = Some W_16449c.
Proof. vm_refl. Qed.
Lemma D_16449c : decode_any W_16449c = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644a0 : bv 32 := 0xffc67713.
Lemma F_1644a0 : fetch_word AsanUbsan.M.loaded_segments (0x1647f0 : word) = Some W_1644a0.
Proof. vm_refl. Qed.
Lemma D_1644a0 : decode_any W_1644a0 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644a4 : bv 32 := 0x02d83633.
Lemma F_1644a4 : fetch_word AsanUbsan.M.loaded_segments (0x1647f4 : word) = Some W_1644a4.
Proof. vm_refl. Qed.
Lemma D_1644a4 : decode_any W_1644a4 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644a8 : bv 32 := 0x00c5a023.
Lemma F_1644a8 : fetch_word AsanUbsan.M.loaded_segments (0x1647f8 : word) = Some W_1644a8.
Proof. vm_refl. Qed.
Lemma D_1644a8 : decode_any W_1644a8 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644ac : bv 32 := 0x00e586b3.
Lemma F_1644ac : fetch_word AsanUbsan.M.loaded_segments (0x1647fc : word) = Some W_1644ac.
Proof. vm_refl. Qed.
Lemma D_1644ac : decode_any W_1644ac = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644b0 : bv 32 := 0xfec6ae23.
Lemma F_1644b0 : fetch_word AsanUbsan.M.loaded_segments (0x164800 : word) = Some W_1644b0.
Proof. vm_refl. Qed.
Lemma D_1644b0 : decode_any W_1644b0 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644b4 : bv 32 := 0x08f76063.
Lemma F_1644b4 : fetch_word AsanUbsan.M.loaded_segments (0x164804 : word) = Some W_1644b4.
Proof. vm_refl. Qed.
Lemma D_1644b4 : decode_any W_1644b4 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644b8 : bv 32 := 0x00c5a223.
Lemma F_1644b8 : fetch_word AsanUbsan.M.loaded_segments (0x164808 : word) = Some W_1644b8.
Proof. vm_refl. Qed.
Lemma D_1644b8 : decode_any W_1644b8 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644bc : bv 32 := 0x00c5a423.
Lemma F_1644bc : fetch_word AsanUbsan.M.loaded_segments (0x16480c : word) = Some W_1644bc.
Proof. vm_refl. Qed.
Lemma D_1644bc : decode_any W_1644bc = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644c0 : bv 32 := 0x01900793.
Lemma F_1644c0 : fetch_word AsanUbsan.M.loaded_segments (0x164810 : word) = Some W_1644c0.
Proof. vm_refl. Qed.
Lemma D_1644c0 : decode_any W_1644c0 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644c4 : bv 32 := 0xfec6aa23.
Lemma F_1644c4 : fetch_word AsanUbsan.M.loaded_segments (0x164814 : word) = Some W_1644c4.
Proof. vm_refl. Qed.
Lemma D_1644c4 : decode_any W_1644c4 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644c8 : bv 32 := 0xfec6ac23.
Lemma F_1644c8 : fetch_word AsanUbsan.M.loaded_segments (0x164818 : word) = Some W_1644c8.
Proof. vm_refl. Qed.
Lemma D_1644c8 : decode_any W_1644c8 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644cc : bv 32 := 0x06f76463.
Lemma F_1644cc : fetch_word AsanUbsan.M.loaded_segments (0x16481c : word) = Some W_1644cc.
Proof. vm_refl. Qed.
Lemma D_1644cc : decode_any W_1644cc = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644d0 : bv 32 := 0x00c5a623.
Lemma F_1644d0 : fetch_word AsanUbsan.M.loaded_segments (0x164820 : word) = Some W_1644d0.
Proof. vm_refl. Qed.
Lemma D_1644d0 : decode_any W_1644d0 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644d4 : bv 32 := 0x00c5a823.
Lemma F_1644d4 : fetch_word AsanUbsan.M.loaded_segments (0x164824 : word) = Some W_1644d4.
Proof. vm_refl. Qed.
Lemma D_1644d4 : decode_any W_1644d4 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644d8 : bv 32 := 0x00c5aa23.
Lemma F_1644d8 : fetch_word AsanUbsan.M.loaded_segments (0x164828 : word) = Some W_1644d8.
Proof. vm_refl. Qed.
Lemma D_1644d8 : decode_any W_1644d8 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644dc : bv 32 := 0x00c5ac23.
Lemma F_1644dc : fetch_word AsanUbsan.M.loaded_segments (0x16482c : word) = Some W_1644dc.
Proof. vm_refl. Qed.
Lemma D_1644dc : decode_any W_1644dc = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644e0 : bv 32 := 0x0045f793.
Lemma F_1644e0 : fetch_word AsanUbsan.M.loaded_segments (0x164830 : word) = Some W_1644e0.
Proof. vm_refl. Qed.
Lemma D_1644e0 : decode_any W_1644e0 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644e4 : bv 32 := 0x02000813.
Lemma F_1644e4 : fetch_word AsanUbsan.M.loaded_segments (0x164834 : word) = Some W_1644e4.
Proof. vm_refl. Qed.
Lemma D_1644e4 : decode_any W_1644e4 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644e8 : bv 32 := 0x01878793.
Lemma F_1644e8 : fetch_word AsanUbsan.M.loaded_segments (0x164838 : word) = Some W_1644e8.
Proof. vm_refl. Qed.
Lemma D_1644e8 : decode_any W_1644e8 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644ec : bv 32 := 0x40f70733.
Lemma F_1644ec : fetch_word AsanUbsan.M.loaded_segments (0x16483c : word) = Some W_1644ec.
Proof. vm_refl. Qed.
Lemma D_1644ec : decode_any W_1644ec = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644f0 : bv 32 := 0xfec6a223.
Lemma F_1644f0 : fetch_word AsanUbsan.M.loaded_segments (0x164840 : word) = Some W_1644f0.
Proof. vm_refl. Qed.
Lemma D_1644f0 : decode_any W_1644f0 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644f4 : bv 32 := 0xfec6a423.
Lemma F_1644f4 : fetch_word AsanUbsan.M.loaded_segments (0x164844 : word) = Some W_1644f4.
Proof. vm_refl. Qed.
Lemma D_1644f4 : decode_any W_1644f4 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644f8 : bv 32 := 0xfec6a623.
Lemma F_1644f8 : fetch_word AsanUbsan.M.loaded_segments (0x164848 : word) = Some W_1644f8.
Proof. vm_refl. Qed.
Lemma D_1644f8 : decode_any W_1644f8 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644fc : bv 32 := 0xfec6a823.
Lemma F_1644fc : fetch_word AsanUbsan.M.loaded_segments (0x16484c : word) = Some W_1644fc.
Proof. vm_refl. Qed.
Lemma D_1644fc : decode_any W_1644fc = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164500 : bv 32 := 0x03076a63.
Lemma F_164500 : fetch_word AsanUbsan.M.loaded_segments (0x164850 : word) = Some W_164500.
Proof. vm_refl. Qed.
Lemma D_164500 : decode_any W_164500 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164504 : bv 32 := 0x02061613.
Lemma F_164504 : fetch_word AsanUbsan.M.loaded_segments (0x164854 : word) = Some W_164504.
Proof. vm_refl. Qed.
Lemma D_164504 : decode_any W_164504 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164508 : bv 32 := 0x00f585b3.
Lemma F_164508 : fetch_word AsanUbsan.M.loaded_segments (0x164858 : word) = Some W_164508.
Proof. vm_refl. Qed.
Lemma D_164508 : decode_any W_164508 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16450c : bv 32 := 0x02065693.
Lemma F_16450c : fetch_word AsanUbsan.M.loaded_segments (0x16485c : word) = Some W_16450c.
Proof. vm_refl. Qed.
Lemma D_16450c : decode_any W_16450c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164510 : bv 32 := 0x00d66633.
Lemma F_164510 : fetch_word AsanUbsan.M.loaded_segments (0x164860 : word) = Some W_164510.
Proof. vm_refl. Qed.
Lemma D_164510 : decode_any W_164510 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164514 : bv 32 := 0x01f00693.
Lemma F_164514 : fetch_word AsanUbsan.M.loaded_segments (0x164864 : word) = Some W_164514.
Proof. vm_refl. Qed.
Lemma D_164514 : decode_any W_164514 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164518 : bv 32 := 0x00c5b023.
Lemma F_164518 : fetch_word AsanUbsan.M.loaded_segments (0x164868 : word) = Some W_164518.
Proof. vm_refl. Qed.
Lemma D_164518 : decode_any W_164518 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16451c : bv 32 := 0x00c5b423.
Lemma F_16451c : fetch_word AsanUbsan.M.loaded_segments (0x16486c : word) = Some W_16451c.
Proof. vm_refl. Qed.
Lemma D_16451c : decode_any W_16451c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164520 : bv 32 := 0x00c5b823.
Lemma F_164520 : fetch_word AsanUbsan.M.loaded_segments (0x164870 : word) = Some W_164520.
Proof. vm_refl. Qed.
Lemma D_164520 : decode_any W_164520 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164524 : bv 32 := 0x00c5bc23.
Lemma F_164524 : fetch_word AsanUbsan.M.loaded_segments (0x164874 : word) = Some W_164524.
Proof. vm_refl. Qed.
Lemma D_164524 : decode_any W_164524 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164528 : bv 32 := 0xfe070713.
Lemma F_164528 : fetch_word AsanUbsan.M.loaded_segments (0x164878 : word) = Some W_164528.
Proof. vm_refl. Qed.
Lemma D_164528 : decode_any W_164528 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16452c : bv 32 := 0x02058593.
Lemma F_16452c : fetch_word AsanUbsan.M.loaded_segments (0x16487c : word) = Some W_16452c.
Proof. vm_refl. Qed.
Lemma D_16452c : decode_any W_16452c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164530 : bv 32 := 0xfee6e4e3.
Lemma F_164530 : fetch_word AsanUbsan.M.loaded_segments (0x164880 : word) = Some W_164530.
Proof. vm_refl. Qed.
Lemma D_164530 : decode_any W_164530 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164534 : bv 32 := 0x00008067.
Lemma F_164534 : fetch_word AsanUbsan.M.loaded_segments (0x164884 : word) = Some W_164534.
Proof. vm_refl. Qed.
Lemma D_164534 : decode_any W_164534 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x164790%Z.
Definition Fo_000 := F_164440.
Definition Do_000 := D_164440.
Definition Fo_004 := F_164444.
Definition Do_004 := D_164444.
Definition Fo_008 := F_164448.
Definition Do_008 := D_164448.
Definition Fo_00c := F_16444c.
Definition Do_00c := D_16444c.
Definition Fo_010 := F_164450.
Definition Do_010 := D_164450.
Definition Fo_014 := F_164454.
Definition Do_014 := D_164454.
Definition Fo_018 := F_164458.
Definition Do_018 := D_164458.
Definition Fo_01c := F_16445c.
Definition Do_01c := D_16445c.
Definition Fo_020 := F_164460.
Definition Do_020 := D_164460.
Definition Fo_024 := F_164464.
Definition Do_024 := D_164464.
Definition Fo_028 := F_164468.
Definition Do_028 := D_164468.
Definition Fo_02c := F_16446c.
Definition Do_02c := D_16446c.
Definition Fo_030 := F_164470.
Definition Do_030 := D_164470.
Definition Fo_034 := F_164474.
Definition Do_034 := D_164474.
Definition Fo_038 := F_164478.
Definition Do_038 := D_164478.
Definition Fo_03c := F_16447c.
Definition Do_03c := D_16447c.
Definition Fo_040 := F_164480.
Definition Do_040 := D_164480.
Definition Fo_044 := F_164484.
Definition Do_044 := D_164484.
Definition Fo_048 := F_164488.
Definition Do_048 := D_164488.
Definition Fo_04c := F_16448c.
Definition Do_04c := D_16448c.
Definition Fo_050 := F_164490.
Definition Do_050 := D_164490.
Definition Fo_054 := F_164494.
Definition Do_054 := D_164494.
Definition Fo_058 := F_164498.
Definition Do_058 := D_164498.
Definition Fo_05c := F_16449c.
Definition Do_05c := D_16449c.
Definition Fo_060 := F_1644a0.
Definition Do_060 := D_1644a0.
Definition Fo_064 := F_1644a4.
Definition Do_064 := D_1644a4.
Definition Fo_068 := F_1644a8.
Definition Do_068 := D_1644a8.
Definition Fo_06c := F_1644ac.
Definition Do_06c := D_1644ac.
Definition Fo_070 := F_1644b0.
Definition Do_070 := D_1644b0.
Definition Fo_074 := F_1644b4.
Definition Do_074 := D_1644b4.
Definition Fo_078 := F_1644b8.
Definition Do_078 := D_1644b8.
Definition Fo_07c := F_1644bc.
Definition Do_07c := D_1644bc.
Definition Fo_080 := F_1644c0.
Definition Do_080 := D_1644c0.
Definition Fo_084 := F_1644c4.
Definition Do_084 := D_1644c4.
Definition Fo_088 := F_1644c8.
Definition Do_088 := D_1644c8.
Definition Fo_08c := F_1644cc.
Definition Do_08c := D_1644cc.
Definition Fo_090 := F_1644d0.
Definition Do_090 := D_1644d0.
Definition Fo_094 := F_1644d4.
Definition Do_094 := D_1644d4.
Definition Fo_098 := F_1644d8.
Definition Do_098 := D_1644d8.
Definition Fo_09c := F_1644dc.
Definition Do_09c := D_1644dc.
Definition Fo_0a0 := F_1644e0.
Definition Do_0a0 := D_1644e0.
Definition Fo_0a4 := F_1644e4.
Definition Do_0a4 := D_1644e4.
Definition Fo_0a8 := F_1644e8.
Definition Do_0a8 := D_1644e8.
Definition Fo_0ac := F_1644ec.
Definition Do_0ac := D_1644ec.
Definition Fo_0b0 := F_1644f0.
Definition Do_0b0 := D_1644f0.
Definition Fo_0b4 := F_1644f4.
Definition Do_0b4 := D_1644f4.
Definition Fo_0b8 := F_1644f8.
Definition Do_0b8 := D_1644f8.
Definition Fo_0bc := F_1644fc.
Definition Do_0bc := D_1644fc.
Definition Fo_0c0 := F_164500.
Definition Do_0c0 := D_164500.
Definition Fo_0c4 := F_164504.
Definition Do_0c4 := D_164504.
Definition Fo_0c8 := F_164508.
Definition Do_0c8 := D_164508.
Definition Fo_0cc := F_16450c.
Definition Do_0cc := D_16450c.
Definition Fo_0d0 := F_164510.
Definition Do_0d0 := D_164510.
Definition Fo_0d4 := F_164514.
Definition Do_0d4 := D_164514.
Definition Fo_0d8 := F_164518.
Definition Do_0d8 := D_164518.
Definition Fo_0dc := F_16451c.
Definition Do_0dc := D_16451c.
Definition Fo_0e0 := F_164520.
Definition Do_0e0 := D_164520.
Definition Fo_0e4 := F_164524.
Definition Do_0e4 := D_164524.
Definition Fo_0e8 := F_164528.
Definition Do_0e8 := D_164528.
Definition Fo_0ec := F_16452c.
Definition Do_0ec := D_16452c.
Definition Fo_0f0 := F_164530.
Definition Do_0f0 := D_164530.
Definition Fo_0f4 := F_164534.
Definition Do_0f4 := D_164534.
