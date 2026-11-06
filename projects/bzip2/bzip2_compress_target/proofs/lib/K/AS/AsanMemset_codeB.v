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
From OSSVerify.bzip2.bzip2_compress_target.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_c643c : bv 32 := 0x0e060a63.
Lemma F_c643c : fetch_word AsanUbsan.M.loaded_segments (0xc6568 : word) = Some W_c643c.
Proof. vm_refl. Qed.
Lemma D_c643c : decode_any W_c643c = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6440 : bv 32 := 0x00b50023.
Lemma F_c6440 : fetch_word AsanUbsan.M.loaded_segments (0xc656c : word) = Some W_c6440.
Proof. vm_refl. Qed.
Lemma D_c6440 : decode_any W_c6440 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6444 : bv 32 := 0x00c506b3.
Lemma F_c6444 : fetch_word AsanUbsan.M.loaded_segments (0xc6570 : word) = Some W_c6444.
Proof. vm_refl. Qed.
Lemma D_c6444 : decode_any W_c6444 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6448 : bv 32 := 0x00300713.
Lemma F_c6448 : fetch_word AsanUbsan.M.loaded_segments (0xc6574 : word) = Some W_c6448.
Proof. vm_refl. Qed.
Lemma D_c6448 : decode_any W_c6448 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c644c : bv 32 := 0xfeb68fa3.
Lemma F_c644c : fetch_word AsanUbsan.M.loaded_segments (0xc6578 : word) = Some W_c644c.
Proof. vm_refl. Qed.
Lemma D_c644c : decode_any W_c644c = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6450 : bv 32 := 0x0ee66063.
Lemma F_c6450 : fetch_word AsanUbsan.M.loaded_segments (0xc657c : word) = Some W_c6450.
Proof. vm_refl. Qed.
Lemma D_c6450 : decode_any W_c6450 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6454 : bv 32 := 0x00b500a3.
Lemma F_c6454 : fetch_word AsanUbsan.M.loaded_segments (0xc6580 : word) = Some W_c6454.
Proof. vm_refl. Qed.
Lemma D_c6454 : decode_any W_c6454 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6458 : bv 32 := 0x00b50123.
Lemma F_c6458 : fetch_word AsanUbsan.M.loaded_segments (0xc6584 : word) = Some W_c6458.
Proof. vm_refl. Qed.
Lemma D_c6458 : decode_any W_c6458 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c645c : bv 32 := 0x00700713.
Lemma F_c645c : fetch_word AsanUbsan.M.loaded_segments (0xc6588 : word) = Some W_c645c.
Proof. vm_refl. Qed.
Lemma D_c645c : decode_any W_c645c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6460 : bv 32 := 0xfeb68ea3.
Lemma F_c6460 : fetch_word AsanUbsan.M.loaded_segments (0xc658c : word) = Some W_c6460.
Proof. vm_refl. Qed.
Lemma D_c6460 : decode_any W_c6460 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6464 : bv 32 := 0xfeb68f23.
Lemma F_c6464 : fetch_word AsanUbsan.M.loaded_segments (0xc6590 : word) = Some W_c6464.
Proof. vm_refl. Qed.
Lemma D_c6464 : decode_any W_c6464 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6468 : bv 32 := 0x0ce66463.
Lemma F_c6468 : fetch_word AsanUbsan.M.loaded_segments (0xc6594 : word) = Some W_c6468.
Proof. vm_refl. Qed.
Lemma D_c6468 : decode_any W_c6468 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c646c : bv 32 := 0x00b501a3.
Lemma F_c646c : fetch_word AsanUbsan.M.loaded_segments (0xc6598 : word) = Some W_c646c.
Proof. vm_refl. Qed.
Lemma D_c646c : decode_any W_c646c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6470 : bv 32 := 0x00900793.
Lemma F_c6470 : fetch_word AsanUbsan.M.loaded_segments (0xc659c : word) = Some W_c6470.
Proof. vm_refl. Qed.
Lemma D_c6470 : decode_any W_c6470 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6474 : bv 32 := 0xfeb68e23.
Lemma F_c6474 : fetch_word AsanUbsan.M.loaded_segments (0xc65a0 : word) = Some W_c6474.
Proof. vm_refl. Qed.
Lemma D_c6474 : decode_any W_c6474 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6478 : bv 32 := 0x0af66c63.
Lemma F_c6478 : fetch_word AsanUbsan.M.loaded_segments (0xc65a4 : word) = Some W_c6478.
Proof. vm_refl. Qed.
Lemma D_c6478 : decode_any W_c6478 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c647c : bv 32 := 0x40a006bb.
Lemma F_c647c : fetch_word AsanUbsan.M.loaded_segments (0xc65a8 : word) = Some W_c647c.
Proof. vm_refl. Qed.
Lemma D_c647c : decode_any W_c647c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6480 : bv 32 := 0x03859813.
Lemma F_c6480 : fetch_word AsanUbsan.M.loaded_segments (0xc65ac : word) = Some W_c6480.
Proof. vm_refl. Qed.
Lemma D_c6480 : decode_any W_c6480 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6484 : bv 32 := 0x101015b7.
Lemma F_c6484 : fetch_word AsanUbsan.M.loaded_segments (0xc65b0 : word) = Some W_c6484.
Proof. vm_refl. Qed.
Lemma D_c6484 : decode_any W_c6484 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6488 : bv 32 := 0x0036f693.
Lemma F_c6488 : fetch_word AsanUbsan.M.loaded_segments (0xc65b4 : word) = Some W_c6488.
Proof. vm_refl. Qed.
Lemma D_c6488 : decode_any W_c6488 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c648c : bv 32 := 0x00459713.
Lemma F_c648c : fetch_word AsanUbsan.M.loaded_segments (0xc65b8 : word) = Some W_c648c.
Proof. vm_refl. Qed.
Lemma D_c648c : decode_any W_c648c = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6490 : bv 32 := 0x40d60633.
Lemma F_c6490 : fetch_word AsanUbsan.M.loaded_segments (0xc65bc : word) = Some W_c6490.
Proof. vm_refl. Qed.
Lemma D_c6490 : decode_any W_c6490 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6494 : bv 32 := 0x00d505b3.
Lemma F_c6494 : fetch_word AsanUbsan.M.loaded_segments (0xc65c0 : word) = Some W_c6494.
Proof. vm_refl. Qed.
Lemma D_c6494 : decode_any W_c6494 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6498 : bv 32 := 0x10070693.
Lemma F_c6498 : fetch_word AsanUbsan.M.loaded_segments (0xc65c4 : word) = Some W_c6498.
Proof. vm_refl. Qed.
Lemma D_c6498 : decode_any W_c6498 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c649c : bv 32 := 0xffc67713.
Lemma F_c649c : fetch_word AsanUbsan.M.loaded_segments (0xc65c8 : word) = Some W_c649c.
Proof. vm_refl. Qed.
Lemma D_c649c : decode_any W_c649c = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64a0 : bv 32 := 0x02d83633.
Lemma F_c64a0 : fetch_word AsanUbsan.M.loaded_segments (0xc65cc : word) = Some W_c64a0.
Proof. vm_refl. Qed.
Lemma D_c64a0 : decode_any W_c64a0 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64a4 : bv 32 := 0x00c5a023.
Lemma F_c64a4 : fetch_word AsanUbsan.M.loaded_segments (0xc65d0 : word) = Some W_c64a4.
Proof. vm_refl. Qed.
Lemma D_c64a4 : decode_any W_c64a4 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64a8 : bv 32 := 0x00e586b3.
Lemma F_c64a8 : fetch_word AsanUbsan.M.loaded_segments (0xc65d4 : word) = Some W_c64a8.
Proof. vm_refl. Qed.
Lemma D_c64a8 : decode_any W_c64a8 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64ac : bv 32 := 0xfec6ae23.
Lemma F_c64ac : fetch_word AsanUbsan.M.loaded_segments (0xc65d8 : word) = Some W_c64ac.
Proof. vm_refl. Qed.
Lemma D_c64ac : decode_any W_c64ac = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64b0 : bv 32 := 0x08f76063.
Lemma F_c64b0 : fetch_word AsanUbsan.M.loaded_segments (0xc65dc : word) = Some W_c64b0.
Proof. vm_refl. Qed.
Lemma D_c64b0 : decode_any W_c64b0 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64b4 : bv 32 := 0x00c5a223.
Lemma F_c64b4 : fetch_word AsanUbsan.M.loaded_segments (0xc65e0 : word) = Some W_c64b4.
Proof. vm_refl. Qed.
Lemma D_c64b4 : decode_any W_c64b4 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64b8 : bv 32 := 0x00c5a423.
Lemma F_c64b8 : fetch_word AsanUbsan.M.loaded_segments (0xc65e4 : word) = Some W_c64b8.
Proof. vm_refl. Qed.
Lemma D_c64b8 : decode_any W_c64b8 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64bc : bv 32 := 0x01900793.
Lemma F_c64bc : fetch_word AsanUbsan.M.loaded_segments (0xc65e8 : word) = Some W_c64bc.
Proof. vm_refl. Qed.
Lemma D_c64bc : decode_any W_c64bc = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64c0 : bv 32 := 0xfec6aa23.
Lemma F_c64c0 : fetch_word AsanUbsan.M.loaded_segments (0xc65ec : word) = Some W_c64c0.
Proof. vm_refl. Qed.
Lemma D_c64c0 : decode_any W_c64c0 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64c4 : bv 32 := 0xfec6ac23.
Lemma F_c64c4 : fetch_word AsanUbsan.M.loaded_segments (0xc65f0 : word) = Some W_c64c4.
Proof. vm_refl. Qed.
Lemma D_c64c4 : decode_any W_c64c4 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64c8 : bv 32 := 0x06f76463.
Lemma F_c64c8 : fetch_word AsanUbsan.M.loaded_segments (0xc65f4 : word) = Some W_c64c8.
Proof. vm_refl. Qed.
Lemma D_c64c8 : decode_any W_c64c8 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64cc : bv 32 := 0x00c5a623.
Lemma F_c64cc : fetch_word AsanUbsan.M.loaded_segments (0xc65f8 : word) = Some W_c64cc.
Proof. vm_refl. Qed.
Lemma D_c64cc : decode_any W_c64cc = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64d0 : bv 32 := 0x00c5a823.
Lemma F_c64d0 : fetch_word AsanUbsan.M.loaded_segments (0xc65fc : word) = Some W_c64d0.
Proof. vm_refl. Qed.
Lemma D_c64d0 : decode_any W_c64d0 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64d4 : bv 32 := 0x00c5aa23.
Lemma F_c64d4 : fetch_word AsanUbsan.M.loaded_segments (0xc6600 : word) = Some W_c64d4.
Proof. vm_refl. Qed.
Lemma D_c64d4 : decode_any W_c64d4 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64d8 : bv 32 := 0x00c5ac23.
Lemma F_c64d8 : fetch_word AsanUbsan.M.loaded_segments (0xc6604 : word) = Some W_c64d8.
Proof. vm_refl. Qed.
Lemma D_c64d8 : decode_any W_c64d8 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64dc : bv 32 := 0x0045f793.
Lemma F_c64dc : fetch_word AsanUbsan.M.loaded_segments (0xc6608 : word) = Some W_c64dc.
Proof. vm_refl. Qed.
Lemma D_c64dc : decode_any W_c64dc = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64e0 : bv 32 := 0x02000813.
Lemma F_c64e0 : fetch_word AsanUbsan.M.loaded_segments (0xc660c : word) = Some W_c64e0.
Proof. vm_refl. Qed.
Lemma D_c64e0 : decode_any W_c64e0 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64e4 : bv 32 := 0x01878793.
Lemma F_c64e4 : fetch_word AsanUbsan.M.loaded_segments (0xc6610 : word) = Some W_c64e4.
Proof. vm_refl. Qed.
Lemma D_c64e4 : decode_any W_c64e4 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64e8 : bv 32 := 0x40f70733.
Lemma F_c64e8 : fetch_word AsanUbsan.M.loaded_segments (0xc6614 : word) = Some W_c64e8.
Proof. vm_refl. Qed.
Lemma D_c64e8 : decode_any W_c64e8 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64ec : bv 32 := 0xfec6a223.
Lemma F_c64ec : fetch_word AsanUbsan.M.loaded_segments (0xc6618 : word) = Some W_c64ec.
Proof. vm_refl. Qed.
Lemma D_c64ec : decode_any W_c64ec = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64f0 : bv 32 := 0xfec6a423.
Lemma F_c64f0 : fetch_word AsanUbsan.M.loaded_segments (0xc661c : word) = Some W_c64f0.
Proof. vm_refl. Qed.
Lemma D_c64f0 : decode_any W_c64f0 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64f4 : bv 32 := 0xfec6a623.
Lemma F_c64f4 : fetch_word AsanUbsan.M.loaded_segments (0xc6620 : word) = Some W_c64f4.
Proof. vm_refl. Qed.
Lemma D_c64f4 : decode_any W_c64f4 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64f8 : bv 32 := 0xfec6a823.
Lemma F_c64f8 : fetch_word AsanUbsan.M.loaded_segments (0xc6624 : word) = Some W_c64f8.
Proof. vm_refl. Qed.
Lemma D_c64f8 : decode_any W_c64f8 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c64fc : bv 32 := 0x03076a63.
Lemma F_c64fc : fetch_word AsanUbsan.M.loaded_segments (0xc6628 : word) = Some W_c64fc.
Proof. vm_refl. Qed.
Lemma D_c64fc : decode_any W_c64fc = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6500 : bv 32 := 0x02061613.
Lemma F_c6500 : fetch_word AsanUbsan.M.loaded_segments (0xc662c : word) = Some W_c6500.
Proof. vm_refl. Qed.
Lemma D_c6500 : decode_any W_c6500 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6504 : bv 32 := 0x00f585b3.
Lemma F_c6504 : fetch_word AsanUbsan.M.loaded_segments (0xc6630 : word) = Some W_c6504.
Proof. vm_refl. Qed.
Lemma D_c6504 : decode_any W_c6504 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6508 : bv 32 := 0x02065693.
Lemma F_c6508 : fetch_word AsanUbsan.M.loaded_segments (0xc6634 : word) = Some W_c6508.
Proof. vm_refl. Qed.
Lemma D_c6508 : decode_any W_c6508 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c650c : bv 32 := 0x00d66633.
Lemma F_c650c : fetch_word AsanUbsan.M.loaded_segments (0xc6638 : word) = Some W_c650c.
Proof. vm_refl. Qed.
Lemma D_c650c : decode_any W_c650c = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6510 : bv 32 := 0x01f00693.
Lemma F_c6510 : fetch_word AsanUbsan.M.loaded_segments (0xc663c : word) = Some W_c6510.
Proof. vm_refl. Qed.
Lemma D_c6510 : decode_any W_c6510 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6514 : bv 32 := 0x00c5b023.
Lemma F_c6514 : fetch_word AsanUbsan.M.loaded_segments (0xc6640 : word) = Some W_c6514.
Proof. vm_refl. Qed.
Lemma D_c6514 : decode_any W_c6514 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6518 : bv 32 := 0x00c5b423.
Lemma F_c6518 : fetch_word AsanUbsan.M.loaded_segments (0xc6644 : word) = Some W_c6518.
Proof. vm_refl. Qed.
Lemma D_c6518 : decode_any W_c6518 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c651c : bv 32 := 0x00c5b823.
Lemma F_c651c : fetch_word AsanUbsan.M.loaded_segments (0xc6648 : word) = Some W_c651c.
Proof. vm_refl. Qed.
Lemma D_c651c : decode_any W_c651c = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6520 : bv 32 := 0x00c5bc23.
Lemma F_c6520 : fetch_word AsanUbsan.M.loaded_segments (0xc664c : word) = Some W_c6520.
Proof. vm_refl. Qed.
Lemma D_c6520 : decode_any W_c6520 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6524 : bv 32 := 0xfe070713.
Lemma F_c6524 : fetch_word AsanUbsan.M.loaded_segments (0xc6650 : word) = Some W_c6524.
Proof. vm_refl. Qed.
Lemma D_c6524 : decode_any W_c6524 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6528 : bv 32 := 0x02058593.
Lemma F_c6528 : fetch_word AsanUbsan.M.loaded_segments (0xc6654 : word) = Some W_c6528.
Proof. vm_refl. Qed.
Lemma D_c6528 : decode_any W_c6528 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c652c : bv 32 := 0xfee6e4e3.
Lemma F_c652c : fetch_word AsanUbsan.M.loaded_segments (0xc6658 : word) = Some W_c652c.
Proof. vm_refl. Qed.
Lemma D_c652c : decode_any W_c652c = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c6530 : bv 32 := 0x00008067.
Lemma F_c6530 : fetch_word AsanUbsan.M.loaded_segments (0xc665c : word) = Some W_c6530.
Proof. vm_refl. Qed.
Lemma D_c6530 : decode_any W_c6530 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0xc6568%Z.
Definition Fo_000 := F_c643c.
Definition Do_000 := D_c643c.
Definition Fo_004 := F_c6440.
Definition Do_004 := D_c6440.
Definition Fo_008 := F_c6444.
Definition Do_008 := D_c6444.
Definition Fo_00c := F_c6448.
Definition Do_00c := D_c6448.
Definition Fo_010 := F_c644c.
Definition Do_010 := D_c644c.
Definition Fo_014 := F_c6450.
Definition Do_014 := D_c6450.
Definition Fo_018 := F_c6454.
Definition Do_018 := D_c6454.
Definition Fo_01c := F_c6458.
Definition Do_01c := D_c6458.
Definition Fo_020 := F_c645c.
Definition Do_020 := D_c645c.
Definition Fo_024 := F_c6460.
Definition Do_024 := D_c6460.
Definition Fo_028 := F_c6464.
Definition Do_028 := D_c6464.
Definition Fo_02c := F_c6468.
Definition Do_02c := D_c6468.
Definition Fo_030 := F_c646c.
Definition Do_030 := D_c646c.
Definition Fo_034 := F_c6470.
Definition Do_034 := D_c6470.
Definition Fo_038 := F_c6474.
Definition Do_038 := D_c6474.
Definition Fo_03c := F_c6478.
Definition Do_03c := D_c6478.
Definition Fo_040 := F_c647c.
Definition Do_040 := D_c647c.
Definition Fo_044 := F_c6480.
Definition Do_044 := D_c6480.
Definition Fo_048 := F_c6484.
Definition Do_048 := D_c6484.
Definition Fo_04c := F_c6488.
Definition Do_04c := D_c6488.
Definition Fo_050 := F_c648c.
Definition Do_050 := D_c648c.
Definition Fo_054 := F_c6490.
Definition Do_054 := D_c6490.
Definition Fo_058 := F_c6494.
Definition Do_058 := D_c6494.
Definition Fo_05c := F_c6498.
Definition Do_05c := D_c6498.
Definition Fo_060 := F_c649c.
Definition Do_060 := D_c649c.
Definition Fo_064 := F_c64a0.
Definition Do_064 := D_c64a0.
Definition Fo_068 := F_c64a4.
Definition Do_068 := D_c64a4.
Definition Fo_06c := F_c64a8.
Definition Do_06c := D_c64a8.
Definition Fo_070 := F_c64ac.
Definition Do_070 := D_c64ac.
Definition Fo_074 := F_c64b0.
Definition Do_074 := D_c64b0.
Definition Fo_078 := F_c64b4.
Definition Do_078 := D_c64b4.
Definition Fo_07c := F_c64b8.
Definition Do_07c := D_c64b8.
Definition Fo_080 := F_c64bc.
Definition Do_080 := D_c64bc.
Definition Fo_084 := F_c64c0.
Definition Do_084 := D_c64c0.
Definition Fo_088 := F_c64c4.
Definition Do_088 := D_c64c4.
Definition Fo_08c := F_c64c8.
Definition Do_08c := D_c64c8.
Definition Fo_090 := F_c64cc.
Definition Do_090 := D_c64cc.
Definition Fo_094 := F_c64d0.
Definition Do_094 := D_c64d0.
Definition Fo_098 := F_c64d4.
Definition Do_098 := D_c64d4.
Definition Fo_09c := F_c64d8.
Definition Do_09c := D_c64d8.
Definition Fo_0a0 := F_c64dc.
Definition Do_0a0 := D_c64dc.
Definition Fo_0a4 := F_c64e0.
Definition Do_0a4 := D_c64e0.
Definition Fo_0a8 := F_c64e4.
Definition Do_0a8 := D_c64e4.
Definition Fo_0ac := F_c64e8.
Definition Do_0ac := D_c64e8.
Definition Fo_0b0 := F_c64ec.
Definition Do_0b0 := D_c64ec.
Definition Fo_0b4 := F_c64f0.
Definition Do_0b4 := D_c64f0.
Definition Fo_0b8 := F_c64f4.
Definition Do_0b8 := D_c64f4.
Definition Fo_0bc := F_c64f8.
Definition Do_0bc := D_c64f8.
Definition Fo_0c0 := F_c64fc.
Definition Do_0c0 := D_c64fc.
Definition Fo_0c4 := F_c6500.
Definition Do_0c4 := D_c6500.
Definition Fo_0c8 := F_c6504.
Definition Do_0c8 := D_c6504.
Definition Fo_0cc := F_c6508.
Definition Do_0cc := D_c6508.
Definition Fo_0d0 := F_c650c.
Definition Do_0d0 := D_c650c.
Definition Fo_0d4 := F_c6510.
Definition Do_0d4 := D_c6510.
Definition Fo_0d8 := F_c6514.
Definition Do_0d8 := D_c6514.
Definition Fo_0dc := F_c6518.
Definition Do_0dc := D_c6518.
Definition Fo_0e0 := F_c651c.
Definition Do_0e0 := D_c651c.
Definition Fo_0e4 := F_c6520.
Definition Do_0e4 := D_c6520.
Definition Fo_0e8 := F_c6524.
Definition Do_0e8 := D_c6524.
Definition Fo_0ec := F_c6528.
Definition Do_0ec := D_c6528.
Definition Fo_0f0 := F_c652c.
Definition Do_0f0 := D_c652c.
Definition Fo_0f4 := F_c6530.
Definition Do_0f4 := D_c6530.
