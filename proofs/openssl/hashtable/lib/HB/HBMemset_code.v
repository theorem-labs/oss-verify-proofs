(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5286c4 : bv 32 := 0x0e060a63.
Lemma F_5286c4 : fetch_word AsanUbsan.M.loaded_segments (0x56123c : word) = Some W_5286c4.
Proof. vm_refl. Qed.
Lemma D_5286c4 : decode_any W_5286c4 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5286c8 : bv 32 := 0x00b50023.
Lemma F_5286c8 : fetch_word AsanUbsan.M.loaded_segments (0x561240 : word) = Some W_5286c8.
Proof. vm_refl. Qed.
Lemma D_5286c8 : decode_any W_5286c8 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5286cc : bv 32 := 0x00c506b3.
Lemma F_5286cc : fetch_word AsanUbsan.M.loaded_segments (0x561244 : word) = Some W_5286cc.
Proof. vm_refl. Qed.
Lemma D_5286cc : decode_any W_5286cc = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5286d0 : bv 32 := 0x00300713.
Lemma F_5286d0 : fetch_word AsanUbsan.M.loaded_segments (0x561248 : word) = Some W_5286d0.
Proof. vm_refl. Qed.
Lemma D_5286d0 : decode_any W_5286d0 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5286d4 : bv 32 := 0xfeb68fa3.
Lemma F_5286d4 : fetch_word AsanUbsan.M.loaded_segments (0x56124c : word) = Some W_5286d4.
Proof. vm_refl. Qed.
Lemma D_5286d4 : decode_any W_5286d4 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5286d8 : bv 32 := 0x0ee66063.
Lemma F_5286d8 : fetch_word AsanUbsan.M.loaded_segments (0x561250 : word) = Some W_5286d8.
Proof. vm_refl. Qed.
Lemma D_5286d8 : decode_any W_5286d8 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5286dc : bv 32 := 0x00b500a3.
Lemma F_5286dc : fetch_word AsanUbsan.M.loaded_segments (0x561254 : word) = Some W_5286dc.
Proof. vm_refl. Qed.
Lemma D_5286dc : decode_any W_5286dc = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5286e0 : bv 32 := 0x00b50123.
Lemma F_5286e0 : fetch_word AsanUbsan.M.loaded_segments (0x561258 : word) = Some W_5286e0.
Proof. vm_refl. Qed.
Lemma D_5286e0 : decode_any W_5286e0 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5286e4 : bv 32 := 0x00700713.
Lemma F_5286e4 : fetch_word AsanUbsan.M.loaded_segments (0x56125c : word) = Some W_5286e4.
Proof. vm_refl. Qed.
Lemma D_5286e4 : decode_any W_5286e4 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5286e8 : bv 32 := 0xfeb68ea3.
Lemma F_5286e8 : fetch_word AsanUbsan.M.loaded_segments (0x561260 : word) = Some W_5286e8.
Proof. vm_refl. Qed.
Lemma D_5286e8 : decode_any W_5286e8 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5286ec : bv 32 := 0xfeb68f23.
Lemma F_5286ec : fetch_word AsanUbsan.M.loaded_segments (0x561264 : word) = Some W_5286ec.
Proof. vm_refl. Qed.
Lemma D_5286ec : decode_any W_5286ec = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5286f0 : bv 32 := 0x0ce66463.
Lemma F_5286f0 : fetch_word AsanUbsan.M.loaded_segments (0x561268 : word) = Some W_5286f0.
Proof. vm_refl. Qed.
Lemma D_5286f0 : decode_any W_5286f0 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5286f4 : bv 32 := 0x00b501a3.
Lemma F_5286f4 : fetch_word AsanUbsan.M.loaded_segments (0x56126c : word) = Some W_5286f4.
Proof. vm_refl. Qed.
Lemma D_5286f4 : decode_any W_5286f4 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5286f8 : bv 32 := 0x00900793.
Lemma F_5286f8 : fetch_word AsanUbsan.M.loaded_segments (0x561270 : word) = Some W_5286f8.
Proof. vm_refl. Qed.
Lemma D_5286f8 : decode_any W_5286f8 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5286fc : bv 32 := 0xfeb68e23.
Lemma F_5286fc : fetch_word AsanUbsan.M.loaded_segments (0x561274 : word) = Some W_5286fc.
Proof. vm_refl. Qed.
Lemma D_5286fc : decode_any W_5286fc = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528700 : bv 32 := 0x0af66c63.
Lemma F_528700 : fetch_word AsanUbsan.M.loaded_segments (0x561278 : word) = Some W_528700.
Proof. vm_refl. Qed.
Lemma D_528700 : decode_any W_528700 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528704 : bv 32 := 0x40a006bb.
Lemma F_528704 : fetch_word AsanUbsan.M.loaded_segments (0x56127c : word) = Some W_528704.
Proof. vm_refl. Qed.
Lemma D_528704 : decode_any W_528704 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528708 : bv 32 := 0x03859813.
Lemma F_528708 : fetch_word AsanUbsan.M.loaded_segments (0x561280 : word) = Some W_528708.
Proof. vm_refl. Qed.
Lemma D_528708 : decode_any W_528708 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52870c : bv 32 := 0x101015b7.
Lemma F_52870c : fetch_word AsanUbsan.M.loaded_segments (0x561284 : word) = Some W_52870c.
Proof. vm_refl. Qed.
Lemma D_52870c : decode_any W_52870c = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528710 : bv 32 := 0x0036f693.
Lemma F_528710 : fetch_word AsanUbsan.M.loaded_segments (0x561288 : word) = Some W_528710.
Proof. vm_refl. Qed.
Lemma D_528710 : decode_any W_528710 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528714 : bv 32 := 0x00459713.
Lemma F_528714 : fetch_word AsanUbsan.M.loaded_segments (0x56128c : word) = Some W_528714.
Proof. vm_refl. Qed.
Lemma D_528714 : decode_any W_528714 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528718 : bv 32 := 0x40d60633.
Lemma F_528718 : fetch_word AsanUbsan.M.loaded_segments (0x561290 : word) = Some W_528718.
Proof. vm_refl. Qed.
Lemma D_528718 : decode_any W_528718 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52871c : bv 32 := 0x00d505b3.
Lemma F_52871c : fetch_word AsanUbsan.M.loaded_segments (0x561294 : word) = Some W_52871c.
Proof. vm_refl. Qed.
Lemma D_52871c : decode_any W_52871c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528720 : bv 32 := 0x10070693.
Lemma F_528720 : fetch_word AsanUbsan.M.loaded_segments (0x561298 : word) = Some W_528720.
Proof. vm_refl. Qed.
Lemma D_528720 : decode_any W_528720 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528724 : bv 32 := 0xffc67713.
Lemma F_528724 : fetch_word AsanUbsan.M.loaded_segments (0x56129c : word) = Some W_528724.
Proof. vm_refl. Qed.
Lemma D_528724 : decode_any W_528724 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528728 : bv 32 := 0x02d83633.
Lemma F_528728 : fetch_word AsanUbsan.M.loaded_segments (0x5612a0 : word) = Some W_528728.
Proof. vm_refl. Qed.
Lemma D_528728 : decode_any W_528728 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52872c : bv 32 := 0x00c5a023.
Lemma F_52872c : fetch_word AsanUbsan.M.loaded_segments (0x5612a4 : word) = Some W_52872c.
Proof. vm_refl. Qed.
Lemma D_52872c : decode_any W_52872c = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528730 : bv 32 := 0x00e586b3.
Lemma F_528730 : fetch_word AsanUbsan.M.loaded_segments (0x5612a8 : word) = Some W_528730.
Proof. vm_refl. Qed.
Lemma D_528730 : decode_any W_528730 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528734 : bv 32 := 0xfec6ae23.
Lemma F_528734 : fetch_word AsanUbsan.M.loaded_segments (0x5612ac : word) = Some W_528734.
Proof. vm_refl. Qed.
Lemma D_528734 : decode_any W_528734 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528738 : bv 32 := 0x08f76063.
Lemma F_528738 : fetch_word AsanUbsan.M.loaded_segments (0x5612b0 : word) = Some W_528738.
Proof. vm_refl. Qed.
Lemma D_528738 : decode_any W_528738 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52873c : bv 32 := 0x00c5a223.
Lemma F_52873c : fetch_word AsanUbsan.M.loaded_segments (0x5612b4 : word) = Some W_52873c.
Proof. vm_refl. Qed.
Lemma D_52873c : decode_any W_52873c = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528740 : bv 32 := 0x00c5a423.
Lemma F_528740 : fetch_word AsanUbsan.M.loaded_segments (0x5612b8 : word) = Some W_528740.
Proof. vm_refl. Qed.
Lemma D_528740 : decode_any W_528740 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528744 : bv 32 := 0x01900793.
Lemma F_528744 : fetch_word AsanUbsan.M.loaded_segments (0x5612bc : word) = Some W_528744.
Proof. vm_refl. Qed.
Lemma D_528744 : decode_any W_528744 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528748 : bv 32 := 0xfec6aa23.
Lemma F_528748 : fetch_word AsanUbsan.M.loaded_segments (0x5612c0 : word) = Some W_528748.
Proof. vm_refl. Qed.
Lemma D_528748 : decode_any W_528748 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52874c : bv 32 := 0xfec6ac23.
Lemma F_52874c : fetch_word AsanUbsan.M.loaded_segments (0x5612c4 : word) = Some W_52874c.
Proof. vm_refl. Qed.
Lemma D_52874c : decode_any W_52874c = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528750 : bv 32 := 0x06f76463.
Lemma F_528750 : fetch_word AsanUbsan.M.loaded_segments (0x5612c8 : word) = Some W_528750.
Proof. vm_refl. Qed.
Lemma D_528750 : decode_any W_528750 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528754 : bv 32 := 0x00c5a623.
Lemma F_528754 : fetch_word AsanUbsan.M.loaded_segments (0x5612cc : word) = Some W_528754.
Proof. vm_refl. Qed.
Lemma D_528754 : decode_any W_528754 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528758 : bv 32 := 0x00c5a823.
Lemma F_528758 : fetch_word AsanUbsan.M.loaded_segments (0x5612d0 : word) = Some W_528758.
Proof. vm_refl. Qed.
Lemma D_528758 : decode_any W_528758 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52875c : bv 32 := 0x00c5aa23.
Lemma F_52875c : fetch_word AsanUbsan.M.loaded_segments (0x5612d4 : word) = Some W_52875c.
Proof. vm_refl. Qed.
Lemma D_52875c : decode_any W_52875c = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528760 : bv 32 := 0x00c5ac23.
Lemma F_528760 : fetch_word AsanUbsan.M.loaded_segments (0x5612d8 : word) = Some W_528760.
Proof. vm_refl. Qed.
Lemma D_528760 : decode_any W_528760 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528764 : bv 32 := 0x0045f793.
Lemma F_528764 : fetch_word AsanUbsan.M.loaded_segments (0x5612dc : word) = Some W_528764.
Proof. vm_refl. Qed.
Lemma D_528764 : decode_any W_528764 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528768 : bv 32 := 0x02000813.
Lemma F_528768 : fetch_word AsanUbsan.M.loaded_segments (0x5612e0 : word) = Some W_528768.
Proof. vm_refl. Qed.
Lemma D_528768 : decode_any W_528768 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52876c : bv 32 := 0x01878793.
Lemma F_52876c : fetch_word AsanUbsan.M.loaded_segments (0x5612e4 : word) = Some W_52876c.
Proof. vm_refl. Qed.
Lemma D_52876c : decode_any W_52876c = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528770 : bv 32 := 0x40f70733.
Lemma F_528770 : fetch_word AsanUbsan.M.loaded_segments (0x5612e8 : word) = Some W_528770.
Proof. vm_refl. Qed.
Lemma D_528770 : decode_any W_528770 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528774 : bv 32 := 0xfec6a223.
Lemma F_528774 : fetch_word AsanUbsan.M.loaded_segments (0x5612ec : word) = Some W_528774.
Proof. vm_refl. Qed.
Lemma D_528774 : decode_any W_528774 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528778 : bv 32 := 0xfec6a423.
Lemma F_528778 : fetch_word AsanUbsan.M.loaded_segments (0x5612f0 : word) = Some W_528778.
Proof. vm_refl. Qed.
Lemma D_528778 : decode_any W_528778 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52877c : bv 32 := 0xfec6a623.
Lemma F_52877c : fetch_word AsanUbsan.M.loaded_segments (0x5612f4 : word) = Some W_52877c.
Proof. vm_refl. Qed.
Lemma D_52877c : decode_any W_52877c = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528780 : bv 32 := 0xfec6a823.
Lemma F_528780 : fetch_word AsanUbsan.M.loaded_segments (0x5612f8 : word) = Some W_528780.
Proof. vm_refl. Qed.
Lemma D_528780 : decode_any W_528780 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528784 : bv 32 := 0x03076a63.
Lemma F_528784 : fetch_word AsanUbsan.M.loaded_segments (0x5612fc : word) = Some W_528784.
Proof. vm_refl. Qed.
Lemma D_528784 : decode_any W_528784 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528788 : bv 32 := 0x02061613.
Lemma F_528788 : fetch_word AsanUbsan.M.loaded_segments (0x561300 : word) = Some W_528788.
Proof. vm_refl. Qed.
Lemma D_528788 : decode_any W_528788 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52878c : bv 32 := 0x00f585b3.
Lemma F_52878c : fetch_word AsanUbsan.M.loaded_segments (0x561304 : word) = Some W_52878c.
Proof. vm_refl. Qed.
Lemma D_52878c : decode_any W_52878c = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528790 : bv 32 := 0x02065693.
Lemma F_528790 : fetch_word AsanUbsan.M.loaded_segments (0x561308 : word) = Some W_528790.
Proof. vm_refl. Qed.
Lemma D_528790 : decode_any W_528790 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528794 : bv 32 := 0x00d66633.
Lemma F_528794 : fetch_word AsanUbsan.M.loaded_segments (0x56130c : word) = Some W_528794.
Proof. vm_refl. Qed.
Lemma D_528794 : decode_any W_528794 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_528798 : bv 32 := 0x01f00693.
Lemma F_528798 : fetch_word AsanUbsan.M.loaded_segments (0x561310 : word) = Some W_528798.
Proof. vm_refl. Qed.
Lemma D_528798 : decode_any W_528798 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52879c : bv 32 := 0x00c5b023.
Lemma F_52879c : fetch_word AsanUbsan.M.loaded_segments (0x561314 : word) = Some W_52879c.
Proof. vm_refl. Qed.
Lemma D_52879c : decode_any W_52879c = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5287a0 : bv 32 := 0x00c5b423.
Lemma F_5287a0 : fetch_word AsanUbsan.M.loaded_segments (0x561318 : word) = Some W_5287a0.
Proof. vm_refl. Qed.
Lemma D_5287a0 : decode_any W_5287a0 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5287a4 : bv 32 := 0x00c5b823.
Lemma F_5287a4 : fetch_word AsanUbsan.M.loaded_segments (0x56131c : word) = Some W_5287a4.
Proof. vm_refl. Qed.
Lemma D_5287a4 : decode_any W_5287a4 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5287a8 : bv 32 := 0x00c5bc23.
Lemma F_5287a8 : fetch_word AsanUbsan.M.loaded_segments (0x561320 : word) = Some W_5287a8.
Proof. vm_refl. Qed.
Lemma D_5287a8 : decode_any W_5287a8 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5287ac : bv 32 := 0xfe070713.
Lemma F_5287ac : fetch_word AsanUbsan.M.loaded_segments (0x561324 : word) = Some W_5287ac.
Proof. vm_refl. Qed.
Lemma D_5287ac : decode_any W_5287ac = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5287b0 : bv 32 := 0x02058593.
Lemma F_5287b0 : fetch_word AsanUbsan.M.loaded_segments (0x561328 : word) = Some W_5287b0.
Proof. vm_refl. Qed.
Lemma D_5287b0 : decode_any W_5287b0 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5287b4 : bv 32 := 0xfee6e4e3.
Lemma F_5287b4 : fetch_word AsanUbsan.M.loaded_segments (0x56132c : word) = Some W_5287b4.
Proof. vm_refl. Qed.
Lemma D_5287b4 : decode_any W_5287b4 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5287b8 : bv 32 := 0x00008067.
Lemma F_5287b8 : fetch_word AsanUbsan.M.loaded_segments (0x561330 : word) = Some W_5287b8.
Proof. vm_refl. Qed.
Lemma D_5287b8 : decode_any W_5287b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x56123c%Z.
Definition Fo_000 := F_5286c4.
Definition Do_000 := D_5286c4.
Definition Fo_004 := F_5286c8.
Definition Do_004 := D_5286c8.
Definition Fo_008 := F_5286cc.
Definition Do_008 := D_5286cc.
Definition Fo_00c := F_5286d0.
Definition Do_00c := D_5286d0.
Definition Fo_010 := F_5286d4.
Definition Do_010 := D_5286d4.
Definition Fo_014 := F_5286d8.
Definition Do_014 := D_5286d8.
Definition Fo_018 := F_5286dc.
Definition Do_018 := D_5286dc.
Definition Fo_01c := F_5286e0.
Definition Do_01c := D_5286e0.
Definition Fo_020 := F_5286e4.
Definition Do_020 := D_5286e4.
Definition Fo_024 := F_5286e8.
Definition Do_024 := D_5286e8.
Definition Fo_028 := F_5286ec.
Definition Do_028 := D_5286ec.
Definition Fo_02c := F_5286f0.
Definition Do_02c := D_5286f0.
Definition Fo_030 := F_5286f4.
Definition Do_030 := D_5286f4.
Definition Fo_034 := F_5286f8.
Definition Do_034 := D_5286f8.
Definition Fo_038 := F_5286fc.
Definition Do_038 := D_5286fc.
Definition Fo_03c := F_528700.
Definition Do_03c := D_528700.
Definition Fo_040 := F_528704.
Definition Do_040 := D_528704.
Definition Fo_044 := F_528708.
Definition Do_044 := D_528708.
Definition Fo_048 := F_52870c.
Definition Do_048 := D_52870c.
Definition Fo_04c := F_528710.
Definition Do_04c := D_528710.
Definition Fo_050 := F_528714.
Definition Do_050 := D_528714.
Definition Fo_054 := F_528718.
Definition Do_054 := D_528718.
Definition Fo_058 := F_52871c.
Definition Do_058 := D_52871c.
Definition Fo_05c := F_528720.
Definition Do_05c := D_528720.
Definition Fo_060 := F_528724.
Definition Do_060 := D_528724.
Definition Fo_064 := F_528728.
Definition Do_064 := D_528728.
Definition Fo_068 := F_52872c.
Definition Do_068 := D_52872c.
Definition Fo_06c := F_528730.
Definition Do_06c := D_528730.
Definition Fo_070 := F_528734.
Definition Do_070 := D_528734.
Definition Fo_074 := F_528738.
Definition Do_074 := D_528738.
Definition Fo_078 := F_52873c.
Definition Do_078 := D_52873c.
Definition Fo_07c := F_528740.
Definition Do_07c := D_528740.
Definition Fo_080 := F_528744.
Definition Do_080 := D_528744.
Definition Fo_084 := F_528748.
Definition Do_084 := D_528748.
Definition Fo_088 := F_52874c.
Definition Do_088 := D_52874c.
Definition Fo_08c := F_528750.
Definition Do_08c := D_528750.
Definition Fo_090 := F_528754.
Definition Do_090 := D_528754.
Definition Fo_094 := F_528758.
Definition Do_094 := D_528758.
Definition Fo_098 := F_52875c.
Definition Do_098 := D_52875c.
Definition Fo_09c := F_528760.
Definition Do_09c := D_528760.
Definition Fo_0a0 := F_528764.
Definition Do_0a0 := D_528764.
Definition Fo_0a4 := F_528768.
Definition Do_0a4 := D_528768.
Definition Fo_0a8 := F_52876c.
Definition Do_0a8 := D_52876c.
Definition Fo_0ac := F_528770.
Definition Do_0ac := D_528770.
Definition Fo_0b0 := F_528774.
Definition Do_0b0 := D_528774.
Definition Fo_0b4 := F_528778.
Definition Do_0b4 := D_528778.
Definition Fo_0b8 := F_52877c.
Definition Do_0b8 := D_52877c.
Definition Fo_0bc := F_528780.
Definition Do_0bc := D_528780.
Definition Fo_0c0 := F_528784.
Definition Do_0c0 := D_528784.
Definition Fo_0c4 := F_528788.
Definition Do_0c4 := D_528788.
Definition Fo_0c8 := F_52878c.
Definition Do_0c8 := D_52878c.
Definition Fo_0cc := F_528790.
Definition Do_0cc := D_528790.
Definition Fo_0d0 := F_528794.
Definition Do_0d0 := D_528794.
Definition Fo_0d4 := F_528798.
Definition Do_0d4 := D_528798.
Definition Fo_0d8 := F_52879c.
Definition Do_0d8 := D_52879c.
Definition Fo_0dc := F_5287a0.
Definition Do_0dc := D_5287a0.
Definition Fo_0e0 := F_5287a4.
Definition Do_0e0 := D_5287a4.
Definition Fo_0e4 := F_5287a8.
Definition Do_0e4 := D_5287a8.
Definition Fo_0e8 := F_5287ac.
Definition Do_0e8 := D_5287ac.
Definition Fo_0ec := F_5287b0.
Definition Do_0ec := D_5287b0.
Definition Fo_0f0 := F_5287b4.
Definition Do_0f0 := D_5287b4.
Definition Fo_0f4 := F_5287b8.
Definition Do_0f4 := D_5287b8.
