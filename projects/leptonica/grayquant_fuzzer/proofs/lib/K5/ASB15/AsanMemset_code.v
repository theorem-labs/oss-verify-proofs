(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl_bd :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
(* [comment removed for export] *)
Lemma cl_fetch_bd : forall segs (a : word) (w : bv 32), bool_decide (fetch_word segs a = Some w) = true -> fetch_word segs a = Some w.
Proof. intros segs a w. apply bool_decide_eq_true_1. Qed.
Lemma cl_decode_bd : forall (w : bv 32) x, bool_decide (decode_any w = Some x) = true -> decode_any w = Some x.
Proof. intros w x. apply bool_decide_eq_true_1. Qed.
Local Ltac vm_refl := first [ apply cl_fetch_bd; vm_cast_no_check (@eq_refl bool true)
                            | apply cl_decode_bd; vm_cast_no_check (@eq_refl bool true)
                            | vm_refl_bd ].

(* [comment removed for export] *)
Definition W_e1714 : bv 32 := 0x0e060a63.
Lemma F_e1714 : fetch_word AsanUbsan.M.loaded_segments (0xe211c : word) = Some W_e1714.
Proof. vm_refl. Qed.
Lemma D_e1714 : decode_any W_e1714 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1718 : bv 32 := 0x00b50023.
Lemma F_e1718 : fetch_word AsanUbsan.M.loaded_segments (0xe2120 : word) = Some W_e1718.
Proof. vm_refl. Qed.
Lemma D_e1718 : decode_any W_e1718 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e171c : bv 32 := 0x00c506b3.
Lemma F_e171c : fetch_word AsanUbsan.M.loaded_segments (0xe2124 : word) = Some W_e171c.
Proof. vm_refl. Qed.
Lemma D_e171c : decode_any W_e171c = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1720 : bv 32 := 0x00300713.
Lemma F_e1720 : fetch_word AsanUbsan.M.loaded_segments (0xe2128 : word) = Some W_e1720.
Proof. vm_refl. Qed.
Lemma D_e1720 : decode_any W_e1720 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1724 : bv 32 := 0xfeb68fa3.
Lemma F_e1724 : fetch_word AsanUbsan.M.loaded_segments (0xe212c : word) = Some W_e1724.
Proof. vm_refl. Qed.
Lemma D_e1724 : decode_any W_e1724 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1728 : bv 32 := 0x0ee66063.
Lemma F_e1728 : fetch_word AsanUbsan.M.loaded_segments (0xe2130 : word) = Some W_e1728.
Proof. vm_refl. Qed.
Lemma D_e1728 : decode_any W_e1728 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e172c : bv 32 := 0x00b500a3.
Lemma F_e172c : fetch_word AsanUbsan.M.loaded_segments (0xe2134 : word) = Some W_e172c.
Proof. vm_refl. Qed.
Lemma D_e172c : decode_any W_e172c = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1730 : bv 32 := 0x00b50123.
Lemma F_e1730 : fetch_word AsanUbsan.M.loaded_segments (0xe2138 : word) = Some W_e1730.
Proof. vm_refl. Qed.
Lemma D_e1730 : decode_any W_e1730 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1734 : bv 32 := 0x00700713.
Lemma F_e1734 : fetch_word AsanUbsan.M.loaded_segments (0xe213c : word) = Some W_e1734.
Proof. vm_refl. Qed.
Lemma D_e1734 : decode_any W_e1734 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1738 : bv 32 := 0xfeb68ea3.
Lemma F_e1738 : fetch_word AsanUbsan.M.loaded_segments (0xe2140 : word) = Some W_e1738.
Proof. vm_refl. Qed.
Lemma D_e1738 : decode_any W_e1738 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e173c : bv 32 := 0xfeb68f23.
Lemma F_e173c : fetch_word AsanUbsan.M.loaded_segments (0xe2144 : word) = Some W_e173c.
Proof. vm_refl. Qed.
Lemma D_e173c : decode_any W_e173c = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1740 : bv 32 := 0x0ce66463.
Lemma F_e1740 : fetch_word AsanUbsan.M.loaded_segments (0xe2148 : word) = Some W_e1740.
Proof. vm_refl. Qed.
Lemma D_e1740 : decode_any W_e1740 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1744 : bv 32 := 0x00b501a3.
Lemma F_e1744 : fetch_word AsanUbsan.M.loaded_segments (0xe214c : word) = Some W_e1744.
Proof. vm_refl. Qed.
Lemma D_e1744 : decode_any W_e1744 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1748 : bv 32 := 0x00900793.
Lemma F_e1748 : fetch_word AsanUbsan.M.loaded_segments (0xe2150 : word) = Some W_e1748.
Proof. vm_refl. Qed.
Lemma D_e1748 : decode_any W_e1748 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e174c : bv 32 := 0xfeb68e23.
Lemma F_e174c : fetch_word AsanUbsan.M.loaded_segments (0xe2154 : word) = Some W_e174c.
Proof. vm_refl. Qed.
Lemma D_e174c : decode_any W_e174c = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1750 : bv 32 := 0x0af66c63.
Lemma F_e1750 : fetch_word AsanUbsan.M.loaded_segments (0xe2158 : word) = Some W_e1750.
Proof. vm_refl. Qed.
Lemma D_e1750 : decode_any W_e1750 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1754 : bv 32 := 0x40a006bb.
Lemma F_e1754 : fetch_word AsanUbsan.M.loaded_segments (0xe215c : word) = Some W_e1754.
Proof. vm_refl. Qed.
Lemma D_e1754 : decode_any W_e1754 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1758 : bv 32 := 0x03859813.
Lemma F_e1758 : fetch_word AsanUbsan.M.loaded_segments (0xe2160 : word) = Some W_e1758.
Proof. vm_refl. Qed.
Lemma D_e1758 : decode_any W_e1758 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e175c : bv 32 := 0x101015b7.
Lemma F_e175c : fetch_word AsanUbsan.M.loaded_segments (0xe2164 : word) = Some W_e175c.
Proof. vm_refl. Qed.
Lemma D_e175c : decode_any W_e175c = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1760 : bv 32 := 0x0036f693.
Lemma F_e1760 : fetch_word AsanUbsan.M.loaded_segments (0xe2168 : word) = Some W_e1760.
Proof. vm_refl. Qed.
Lemma D_e1760 : decode_any W_e1760 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1764 : bv 32 := 0x00459713.
Lemma F_e1764 : fetch_word AsanUbsan.M.loaded_segments (0xe216c : word) = Some W_e1764.
Proof. vm_refl. Qed.
Lemma D_e1764 : decode_any W_e1764 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1768 : bv 32 := 0x40d60633.
Lemma F_e1768 : fetch_word AsanUbsan.M.loaded_segments (0xe2170 : word) = Some W_e1768.
Proof. vm_refl. Qed.
Lemma D_e1768 : decode_any W_e1768 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e176c : bv 32 := 0x00d505b3.
Lemma F_e176c : fetch_word AsanUbsan.M.loaded_segments (0xe2174 : word) = Some W_e176c.
Proof. vm_refl. Qed.
Lemma D_e176c : decode_any W_e176c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1770 : bv 32 := 0x10070693.
Lemma F_e1770 : fetch_word AsanUbsan.M.loaded_segments (0xe2178 : word) = Some W_e1770.
Proof. vm_refl. Qed.
Lemma D_e1770 : decode_any W_e1770 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1774 : bv 32 := 0xffc67713.
Lemma F_e1774 : fetch_word AsanUbsan.M.loaded_segments (0xe217c : word) = Some W_e1774.
Proof. vm_refl. Qed.
Lemma D_e1774 : decode_any W_e1774 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1778 : bv 32 := 0x02d83633.
Lemma F_e1778 : fetch_word AsanUbsan.M.loaded_segments (0xe2180 : word) = Some W_e1778.
Proof. vm_refl. Qed.
Lemma D_e1778 : decode_any W_e1778 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e177c : bv 32 := 0x00c5a023.
Lemma F_e177c : fetch_word AsanUbsan.M.loaded_segments (0xe2184 : word) = Some W_e177c.
Proof. vm_refl. Qed.
Lemma D_e177c : decode_any W_e177c = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1780 : bv 32 := 0x00e586b3.
Lemma F_e1780 : fetch_word AsanUbsan.M.loaded_segments (0xe2188 : word) = Some W_e1780.
Proof. vm_refl. Qed.
Lemma D_e1780 : decode_any W_e1780 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1784 : bv 32 := 0xfec6ae23.
Lemma F_e1784 : fetch_word AsanUbsan.M.loaded_segments (0xe218c : word) = Some W_e1784.
Proof. vm_refl. Qed.
Lemma D_e1784 : decode_any W_e1784 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1788 : bv 32 := 0x08f76063.
Lemma F_e1788 : fetch_word AsanUbsan.M.loaded_segments (0xe2190 : word) = Some W_e1788.
Proof. vm_refl. Qed.
Lemma D_e1788 : decode_any W_e1788 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e178c : bv 32 := 0x00c5a223.
Lemma F_e178c : fetch_word AsanUbsan.M.loaded_segments (0xe2194 : word) = Some W_e178c.
Proof. vm_refl. Qed.
Lemma D_e178c : decode_any W_e178c = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1790 : bv 32 := 0x00c5a423.
Lemma F_e1790 : fetch_word AsanUbsan.M.loaded_segments (0xe2198 : word) = Some W_e1790.
Proof. vm_refl. Qed.
Lemma D_e1790 : decode_any W_e1790 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1794 : bv 32 := 0x01900793.
Lemma F_e1794 : fetch_word AsanUbsan.M.loaded_segments (0xe219c : word) = Some W_e1794.
Proof. vm_refl. Qed.
Lemma D_e1794 : decode_any W_e1794 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1798 : bv 32 := 0xfec6aa23.
Lemma F_e1798 : fetch_word AsanUbsan.M.loaded_segments (0xe21a0 : word) = Some W_e1798.
Proof. vm_refl. Qed.
Lemma D_e1798 : decode_any W_e1798 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e179c : bv 32 := 0xfec6ac23.
Lemma F_e179c : fetch_word AsanUbsan.M.loaded_segments (0xe21a4 : word) = Some W_e179c.
Proof. vm_refl. Qed.
Lemma D_e179c : decode_any W_e179c = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17a0 : bv 32 := 0x06f76463.
Lemma F_e17a0 : fetch_word AsanUbsan.M.loaded_segments (0xe21a8 : word) = Some W_e17a0.
Proof. vm_refl. Qed.
Lemma D_e17a0 : decode_any W_e17a0 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17a4 : bv 32 := 0x00c5a623.
Lemma F_e17a4 : fetch_word AsanUbsan.M.loaded_segments (0xe21ac : word) = Some W_e17a4.
Proof. vm_refl. Qed.
Lemma D_e17a4 : decode_any W_e17a4 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17a8 : bv 32 := 0x00c5a823.
Lemma F_e17a8 : fetch_word AsanUbsan.M.loaded_segments (0xe21b0 : word) = Some W_e17a8.
Proof. vm_refl. Qed.
Lemma D_e17a8 : decode_any W_e17a8 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17ac : bv 32 := 0x00c5aa23.
Lemma F_e17ac : fetch_word AsanUbsan.M.loaded_segments (0xe21b4 : word) = Some W_e17ac.
Proof. vm_refl. Qed.
Lemma D_e17ac : decode_any W_e17ac = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17b0 : bv 32 := 0x00c5ac23.
Lemma F_e17b0 : fetch_word AsanUbsan.M.loaded_segments (0xe21b8 : word) = Some W_e17b0.
Proof. vm_refl. Qed.
Lemma D_e17b0 : decode_any W_e17b0 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17b4 : bv 32 := 0x0045f793.
Lemma F_e17b4 : fetch_word AsanUbsan.M.loaded_segments (0xe21bc : word) = Some W_e17b4.
Proof. vm_refl. Qed.
Lemma D_e17b4 : decode_any W_e17b4 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17b8 : bv 32 := 0x02000813.
Lemma F_e17b8 : fetch_word AsanUbsan.M.loaded_segments (0xe21c0 : word) = Some W_e17b8.
Proof. vm_refl. Qed.
Lemma D_e17b8 : decode_any W_e17b8 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17bc : bv 32 := 0x01878793.
Lemma F_e17bc : fetch_word AsanUbsan.M.loaded_segments (0xe21c4 : word) = Some W_e17bc.
Proof. vm_refl. Qed.
Lemma D_e17bc : decode_any W_e17bc = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17c0 : bv 32 := 0x40f70733.
Lemma F_e17c0 : fetch_word AsanUbsan.M.loaded_segments (0xe21c8 : word) = Some W_e17c0.
Proof. vm_refl. Qed.
Lemma D_e17c0 : decode_any W_e17c0 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17c4 : bv 32 := 0xfec6a223.
Lemma F_e17c4 : fetch_word AsanUbsan.M.loaded_segments (0xe21cc : word) = Some W_e17c4.
Proof. vm_refl. Qed.
Lemma D_e17c4 : decode_any W_e17c4 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17c8 : bv 32 := 0xfec6a423.
Lemma F_e17c8 : fetch_word AsanUbsan.M.loaded_segments (0xe21d0 : word) = Some W_e17c8.
Proof. vm_refl. Qed.
Lemma D_e17c8 : decode_any W_e17c8 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17cc : bv 32 := 0xfec6a623.
Lemma F_e17cc : fetch_word AsanUbsan.M.loaded_segments (0xe21d4 : word) = Some W_e17cc.
Proof. vm_refl. Qed.
Lemma D_e17cc : decode_any W_e17cc = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17d0 : bv 32 := 0xfec6a823.
Lemma F_e17d0 : fetch_word AsanUbsan.M.loaded_segments (0xe21d8 : word) = Some W_e17d0.
Proof. vm_refl. Qed.
Lemma D_e17d0 : decode_any W_e17d0 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17d4 : bv 32 := 0x03076a63.
Lemma F_e17d4 : fetch_word AsanUbsan.M.loaded_segments (0xe21dc : word) = Some W_e17d4.
Proof. vm_refl. Qed.
Lemma D_e17d4 : decode_any W_e17d4 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17d8 : bv 32 := 0x02061613.
Lemma F_e17d8 : fetch_word AsanUbsan.M.loaded_segments (0xe21e0 : word) = Some W_e17d8.
Proof. vm_refl. Qed.
Lemma D_e17d8 : decode_any W_e17d8 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17dc : bv 32 := 0x00f585b3.
Lemma F_e17dc : fetch_word AsanUbsan.M.loaded_segments (0xe21e4 : word) = Some W_e17dc.
Proof. vm_refl. Qed.
Lemma D_e17dc : decode_any W_e17dc = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17e0 : bv 32 := 0x02065693.
Lemma F_e17e0 : fetch_word AsanUbsan.M.loaded_segments (0xe21e8 : word) = Some W_e17e0.
Proof. vm_refl. Qed.
Lemma D_e17e0 : decode_any W_e17e0 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17e4 : bv 32 := 0x00d66633.
Lemma F_e17e4 : fetch_word AsanUbsan.M.loaded_segments (0xe21ec : word) = Some W_e17e4.
Proof. vm_refl. Qed.
Lemma D_e17e4 : decode_any W_e17e4 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17e8 : bv 32 := 0x01f00693.
Lemma F_e17e8 : fetch_word AsanUbsan.M.loaded_segments (0xe21f0 : word) = Some W_e17e8.
Proof. vm_refl. Qed.
Lemma D_e17e8 : decode_any W_e17e8 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17ec : bv 32 := 0x00c5b023.
Lemma F_e17ec : fetch_word AsanUbsan.M.loaded_segments (0xe21f4 : word) = Some W_e17ec.
Proof. vm_refl. Qed.
Lemma D_e17ec : decode_any W_e17ec = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17f0 : bv 32 := 0x00c5b423.
Lemma F_e17f0 : fetch_word AsanUbsan.M.loaded_segments (0xe21f8 : word) = Some W_e17f0.
Proof. vm_refl. Qed.
Lemma D_e17f0 : decode_any W_e17f0 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17f4 : bv 32 := 0x00c5b823.
Lemma F_e17f4 : fetch_word AsanUbsan.M.loaded_segments (0xe21fc : word) = Some W_e17f4.
Proof. vm_refl. Qed.
Lemma D_e17f4 : decode_any W_e17f4 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17f8 : bv 32 := 0x00c5bc23.
Lemma F_e17f8 : fetch_word AsanUbsan.M.loaded_segments (0xe2200 : word) = Some W_e17f8.
Proof. vm_refl. Qed.
Lemma D_e17f8 : decode_any W_e17f8 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e17fc : bv 32 := 0xfe070713.
Lemma F_e17fc : fetch_word AsanUbsan.M.loaded_segments (0xe2204 : word) = Some W_e17fc.
Proof. vm_refl. Qed.
Lemma D_e17fc : decode_any W_e17fc = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1800 : bv 32 := 0x02058593.
Lemma F_e1800 : fetch_word AsanUbsan.M.loaded_segments (0xe2208 : word) = Some W_e1800.
Proof. vm_refl. Qed.
Lemma D_e1800 : decode_any W_e1800 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1804 : bv 32 := 0xfee6e4e3.
Lemma F_e1804 : fetch_word AsanUbsan.M.loaded_segments (0xe220c : word) = Some W_e1804.
Proof. vm_refl. Qed.
Lemma D_e1804 : decode_any W_e1804 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1808 : bv 32 := 0x00008067.
Lemma F_e1808 : fetch_word AsanUbsan.M.loaded_segments (0xe2210 : word) = Some W_e1808.
Proof. vm_refl. Qed.
Lemma D_e1808 : decode_any W_e1808 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0xe211c%Z.
Definition Fo_000 := F_e1714.
Definition Do_000 := D_e1714.
Definition Fo_004 := F_e1718.
Definition Do_004 := D_e1718.
Definition Fo_008 := F_e171c.
Definition Do_008 := D_e171c.
Definition Fo_00c := F_e1720.
Definition Do_00c := D_e1720.
Definition Fo_010 := F_e1724.
Definition Do_010 := D_e1724.
Definition Fo_014 := F_e1728.
Definition Do_014 := D_e1728.
Definition Fo_018 := F_e172c.
Definition Do_018 := D_e172c.
Definition Fo_01c := F_e1730.
Definition Do_01c := D_e1730.
Definition Fo_020 := F_e1734.
Definition Do_020 := D_e1734.
Definition Fo_024 := F_e1738.
Definition Do_024 := D_e1738.
Definition Fo_028 := F_e173c.
Definition Do_028 := D_e173c.
Definition Fo_02c := F_e1740.
Definition Do_02c := D_e1740.
Definition Fo_030 := F_e1744.
Definition Do_030 := D_e1744.
Definition Fo_034 := F_e1748.
Definition Do_034 := D_e1748.
Definition Fo_038 := F_e174c.
Definition Do_038 := D_e174c.
Definition Fo_03c := F_e1750.
Definition Do_03c := D_e1750.
Definition Fo_040 := F_e1754.
Definition Do_040 := D_e1754.
Definition Fo_044 := F_e1758.
Definition Do_044 := D_e1758.
Definition Fo_048 := F_e175c.
Definition Do_048 := D_e175c.
Definition Fo_04c := F_e1760.
Definition Do_04c := D_e1760.
Definition Fo_050 := F_e1764.
Definition Do_050 := D_e1764.
Definition Fo_054 := F_e1768.
Definition Do_054 := D_e1768.
Definition Fo_058 := F_e176c.
Definition Do_058 := D_e176c.
Definition Fo_05c := F_e1770.
Definition Do_05c := D_e1770.
Definition Fo_060 := F_e1774.
Definition Do_060 := D_e1774.
Definition Fo_064 := F_e1778.
Definition Do_064 := D_e1778.
Definition Fo_068 := F_e177c.
Definition Do_068 := D_e177c.
Definition Fo_06c := F_e1780.
Definition Do_06c := D_e1780.
Definition Fo_070 := F_e1784.
Definition Do_070 := D_e1784.
Definition Fo_074 := F_e1788.
Definition Do_074 := D_e1788.
Definition Fo_078 := F_e178c.
Definition Do_078 := D_e178c.
Definition Fo_07c := F_e1790.
Definition Do_07c := D_e1790.
Definition Fo_080 := F_e1794.
Definition Do_080 := D_e1794.
Definition Fo_084 := F_e1798.
Definition Do_084 := D_e1798.
Definition Fo_088 := F_e179c.
Definition Do_088 := D_e179c.
Definition Fo_08c := F_e17a0.
Definition Do_08c := D_e17a0.
Definition Fo_090 := F_e17a4.
Definition Do_090 := D_e17a4.
Definition Fo_094 := F_e17a8.
Definition Do_094 := D_e17a8.
Definition Fo_098 := F_e17ac.
Definition Do_098 := D_e17ac.
Definition Fo_09c := F_e17b0.
Definition Do_09c := D_e17b0.
Definition Fo_0a0 := F_e17b4.
Definition Do_0a0 := D_e17b4.
Definition Fo_0a4 := F_e17b8.
Definition Do_0a4 := D_e17b8.
Definition Fo_0a8 := F_e17bc.
Definition Do_0a8 := D_e17bc.
Definition Fo_0ac := F_e17c0.
Definition Do_0ac := D_e17c0.
Definition Fo_0b0 := F_e17c4.
Definition Do_0b0 := D_e17c4.
Definition Fo_0b4 := F_e17c8.
Definition Do_0b4 := D_e17c8.
Definition Fo_0b8 := F_e17cc.
Definition Do_0b8 := D_e17cc.
Definition Fo_0bc := F_e17d0.
Definition Do_0bc := D_e17d0.
Definition Fo_0c0 := F_e17d4.
Definition Do_0c0 := D_e17d4.
Definition Fo_0c4 := F_e17d8.
Definition Do_0c4 := D_e17d8.
Definition Fo_0c8 := F_e17dc.
Definition Do_0c8 := D_e17dc.
Definition Fo_0cc := F_e17e0.
Definition Do_0cc := D_e17e0.
Definition Fo_0d0 := F_e17e4.
Definition Do_0d0 := D_e17e4.
Definition Fo_0d4 := F_e17e8.
Definition Do_0d4 := D_e17e8.
Definition Fo_0d8 := F_e17ec.
Definition Do_0d8 := D_e17ec.
Definition Fo_0dc := F_e17f0.
Definition Do_0dc := D_e17f0.
Definition Fo_0e0 := F_e17f4.
Definition Do_0e0 := D_e17f4.
Definition Fo_0e4 := F_e17f8.
Definition Do_0e4 := D_e17f8.
Definition Fo_0e8 := F_e17fc.
Definition Do_0e8 := D_e17fc.
Definition Fo_0ec := F_e1800.
Definition Do_0ec := D_e1800.
Definition Fo_0f0 := F_e1804.
Definition Do_0f0 := D_e1804.
Definition Fo_0f4 := F_e1808.
Definition Do_0f4 := D_e1808.
