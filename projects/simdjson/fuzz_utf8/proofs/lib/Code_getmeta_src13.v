(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_b56b4 : bv 32 := 0x00f57593.
Lemma F_b56b4 : fetch_word Plain.M.loaded_segments (0xb586c : word) = Some W_b56b4.
Proof. vm_refl. Qed.
Lemma D_b56b4 : decode_any W_b56b4 = Some (OpImm ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56b8 : bv 32 := 0x00058463.
Lemma F_b56b8 : fetch_word Plain.M.loaded_segments (0xb5870 : word) = Some W_b56b8.
Proof. vm_refl. Qed.
Lemma D_b56b8 : decode_any W_b56b8 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56bc : bv 32 := 0x00000023.
Lemma F_b56bc : fetch_word Plain.M.loaded_segments (0xb5874 : word) = Some W_b56bc.
Proof. vm_refl. Qed.
Lemma D_b56bc : decode_any W_b56bc = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56c0 : bv 32 := 0xffc54603.
Lemma F_b56c0 : fetch_word Plain.M.loaded_segments (0xb5878 : word) = Some W_b56c0.
Proof. vm_refl. Qed.
Lemma D_b56c0 : decode_any W_b56c0 = Some (Load SZ1 false 12 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56c4 : bv 32 := 0xffd54683.
Lemma F_b56c4 : fetch_word Plain.M.loaded_segments (0xb587c : word) = Some W_b56c4.
Proof. vm_refl. Qed.
Lemma D_b56c4 : decode_any W_b56c4 = Some (Load SZ1 false 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56c8 : bv 32 := 0xffe55583.
Lemma F_b56c8 : fetch_word Plain.M.loaded_segments (0xb5880 : word) = Some W_b56c8.
Proof. vm_refl. Qed.
Lemma D_b56c8 : decode_any W_b56c8 = Some (Load SZ2 false 11 10 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56cc : bv 32 := 0x00060e63.
Lemma F_b56cc : fetch_word Plain.M.loaded_segments (0xb5884 : word) = Some W_b56cc.
Proof. vm_refl. Qed.
Lemma D_b56cc : decode_any W_b56cc = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56d0 : bv 32 := 0x00058463.
Lemma F_b56d0 : fetch_word Plain.M.loaded_segments (0xb5888 : word) = Some W_b56d0.
Proof. vm_refl. Qed.
Lemma D_b56d0 : decode_any W_b56d0 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56d4 : bv 32 := 0x00000023.
Lemma F_b56d4 : fetch_word Plain.M.loaded_segments (0xb588c : word) = Some W_b56d4.
Proof. vm_refl. Qed.
Lemma D_b56d4 : decode_any W_b56d4 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56d8 : bv 32 := 0xff856583.
Lemma F_b56d8 : fetch_word Plain.M.loaded_segments (0xb5890 : word) = Some W_b56d8.
Proof. vm_refl. Qed.
Lemma D_b56d8 : decode_any W_b56d8 = Some (Load SZ4 false 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56dc : bv 32 := 0x0105d613.
Lemma F_b56dc : fetch_word Plain.M.loaded_segments (0xb5894 : word) = Some W_b56dc.
Proof. vm_refl. Qed.
Lemma D_b56dc : decode_any W_b56dc = Some (ShiftImm ALU_SRL 12 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56e0 : bv 32 := 0x00061463.
Lemma F_b56e0 : fetch_word Plain.M.loaded_segments (0xb5898 : word) = Some W_b56e0.
Proof. vm_refl. Qed.
Lemma D_b56e0 : decode_any W_b56e0 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56e4 : bv 32 := 0x00000023.
Lemma F_b56e4 : fetch_word Plain.M.loaded_segments (0xb589c : word) = Some W_b56e4.
Proof. vm_refl. Qed.
Lemma D_b56e4 : decode_any W_b56e4 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56e8 : bv 32 := 0x00459613.
Lemma F_b56e8 : fetch_word Plain.M.loaded_segments (0xb58a0 : word) = Some W_b56e8.
Proof. vm_refl. Qed.
Lemma D_b56e8 : decode_any W_b56e8 = Some (ShiftImm ALU_SLL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56ec : bv 32 := 0x40c50633.
Lemma F_b56ec : fetch_word Plain.M.loaded_segments (0xb58a4 : word) = Some W_b56ec.
Proof. vm_refl. Qed.
Lemma D_b56ec : decode_any W_b56ec = Some (Op ALU_SUB 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56f0 : bv 32 := 0xff063503.
Lemma F_b56f0 : fetch_word Plain.M.loaded_segments (0xb58a8 : word) = Some W_b56f0.
Proof. vm_refl. Qed.
Lemma D_b56f0 : decode_any W_b56f0 = Some (Load SZ8 true 10 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56f4 : bv 32 := 0x01053703.
Lemma F_b56f4 : fetch_word Plain.M.loaded_segments (0xb58ac : word) = Some W_b56f4.
Proof. vm_refl. Qed.
Lemma D_b56f4 : decode_any W_b56f4 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56f8 : bv 32 := 0xff060613.
Lemma F_b56f8 : fetch_word Plain.M.loaded_segments (0xb58b0 : word) = Some W_b56f8.
Proof. vm_refl. Qed.
Lemma D_b56f8 : decode_any W_b56f8 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b56fc : bv 32 := 0x01f6f693.
Lemma F_b56fc : fetch_word Plain.M.loaded_segments (0xb58b4 : word) = Some W_b56fc.
Proof. vm_refl. Qed.
Lemma D_b56fc : decode_any W_b56fc = Some (OpImm ALU_AND 13 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5700 : bv 32 := 0x00c70463.
Lemma F_b5700 : fetch_word Plain.M.loaded_segments (0xb58b8 : word) = Some W_b5700.
Proof. vm_refl. Qed.
Lemma D_b5700 : decode_any W_b5700 = Some (Branch BC_EQ 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5704 : bv 32 := 0x00000023.
Lemma F_b5704 : fetch_word Plain.M.loaded_segments (0xb58bc : word) = Some W_b5704.
Proof. vm_refl. Qed.
Lemma D_b5704 : decode_any W_b5704 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5708 : bv 32 := 0x02053603.
Lemma F_b5708 : fetch_word Plain.M.loaded_segments (0xb58c0 : word) = Some W_b5708.
Proof. vm_refl. Qed.
Lemma D_b5708 : decode_any W_b5708 = Some (Load SZ8 true 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b570c : bv 32 := 0x01f67713.
Lemma F_b570c : fetch_word Plain.M.loaded_segments (0xb58c4 : word) = Some W_b570c.
Proof. vm_refl. Qed.
Lemma D_b570c : decode_any W_b570c = Some (OpImm ALU_AND 14 12 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5710 : bv 32 := 0x00d77463.
Lemma F_b5710 : fetch_word Plain.M.loaded_segments (0xb58c8 : word) = Some W_b5710.
Proof. vm_refl. Qed.
Lemma D_b5710 : decode_any W_b5710 = Some (Branch BC_GEU 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5714 : bv 32 := 0x00000023.
Lemma F_b5714 : fetch_word Plain.M.loaded_segments (0xb58cc : word) = Some W_b5714.
Proof. vm_refl. Qed.
Lemma D_b5714 : decode_any W_b5714 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5718 : bv 32 := 0x01852783.
Lemma F_b5718 : fetch_word Plain.M.loaded_segments (0xb58d0 : word) = Some W_b5718.
Proof. vm_refl. Qed.
Lemma D_b5718 : decode_any W_b5718 = Some (Load SZ4 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b571c : bv 32 := 0x00100713.
Lemma F_b571c : fetch_word Plain.M.loaded_segments (0xb58d4 : word) = Some W_b571c.
Proof. vm_refl. Qed.
Lemma D_b571c : decode_any W_b571c = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5720 : bv 32 := 0x00d7173b.
Lemma F_b5720 : fetch_word Plain.M.loaded_segments (0xb58d8 : word) = Some W_b5720.
Proof. vm_refl. Qed.
Lemma D_b5720 : decode_any W_b5720 = Some (Op32 ALU_SLL 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5724 : bv 32 := 0x00e7f7b3.
Lemma F_b5724 : fetch_word Plain.M.loaded_segments (0xb58dc : word) = Some W_b5724.
Proof. vm_refl. Qed.
Lemma D_b5724 : decode_any W_b5724 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5728 : bv 32 := 0x00078463.
Lemma F_b5728 : fetch_word Plain.M.loaded_segments (0xb58e0 : word) = Some W_b5728.
Proof. vm_refl. Qed.
Lemma D_b5728 : decode_any W_b5728 = Some (Branch BC_EQ 15 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b572c : bv 32 := 0x00000023.
Lemma F_b572c : fetch_word Plain.M.loaded_segments (0xb58e4 : word) = Some W_b572c.
Proof. vm_refl. Qed.
Lemma D_b572c : decode_any W_b572c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5730 : bv 32 := 0x01c52783.
Lemma F_b5730 : fetch_word Plain.M.loaded_segments (0xb58e8 : word) = Some W_b5730.
Proof. vm_refl. Qed.
Lemma D_b5730 : decode_any W_b5730 = Some (Load SZ4 true 15 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5734 : bv 32 := 0x00e7f733.
Lemma F_b5734 : fetch_word Plain.M.loaded_segments (0xb58ec : word) = Some W_b5734.
Proof. vm_refl. Qed.
Lemma D_b5734 : decode_any W_b5734 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5738 : bv 32 := 0x00070463.
Lemma F_b5738 : fetch_word Plain.M.loaded_segments (0xb58f0 : word) = Some W_b5738.
Proof. vm_refl. Qed.
Lemma D_b5738 : decode_any W_b5738 = Some (Branch BC_EQ 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b573c : bv 32 := 0x00000023.
Lemma F_b573c : fetch_word Plain.M.loaded_segments (0xb58f4 : word) = Some W_b573c.
Proof. vm_refl. Qed.
Lemma D_b573c : decode_any W_b573c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5740 : bv 32 := 0xfffff737.
Lemma F_b5740 : fetch_word Plain.M.loaded_segments (0xb58f8 : word) = Some W_b5740.
Proof. vm_refl. Qed.
Lemma D_b5740 : decode_any W_b5740 = Some (Lui 14 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5744 : bv 32 := 0x0004e797.
Lemma F_b5744 : fetch_word Plain.M.loaded_segments (0xb58fc : word) = Some W_b5744.
Proof. vm_refl. Qed.
Lemma D_b5744 : decode_any W_b5744 = Some (Auipc 15 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5748 : bv 32 := 0x00e57733.
Lemma F_b5748 : fetch_word Plain.M.loaded_segments (0xb5900 : word) = Some W_b5748.
Proof. vm_refl. Qed.
Lemma D_b5748 : decode_any W_b5748 = Some (Op ALU_AND 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b574c : bv 32 := 0x00073703.
Lemma F_b574c : fetch_word Plain.M.loaded_segments (0xb5904 : word) = Some W_b574c.
Proof. vm_refl. Qed.
Lemma D_b574c : decode_any W_b574c = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5750 : bv 32 := 0x0dc7b783.
Lemma F_b5750 : fetch_word Plain.M.loaded_segments (0xb5908 : word) = Some W_b5750.
Proof. vm_refl. Qed.
Lemma D_b5750 : decode_any W_b5750 = Some (Load SZ8 true 15 15 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5754 : bv 32 := 0x00f70463.
Lemma F_b5754 : fetch_word Plain.M.loaded_segments (0xb590c : word) = Some W_b5754.
Proof. vm_refl. Qed.
Lemma D_b5754 : decode_any W_b5754 = Some (Branch BC_EQ 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5758 : bv 32 := 0x00000023.
Lemma F_b5758 : fetch_word Plain.M.loaded_segments (0xb5910 : word) = Some W_b5758.
Proof. vm_refl. Qed.
Lemma D_b5758 : decode_any W_b5758 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b575c : bv 32 := 0x03461713.
Lemma F_b575c : fetch_word Plain.M.loaded_segments (0xb5914 : word) = Some W_b575c.
Proof. vm_refl. Qed.
Lemma D_b575c : decode_any W_b575c = Some (ShiftImm ALU_SLL 14 12 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5760 : bv 32 := 0x03a75713.
Lemma F_b5760 : fetch_word Plain.M.loaded_segments (0xb5918 : word) = Some W_b5760.
Proof. vm_refl. Qed.
Lemma D_b5760 : decode_any W_b5760 = Some (ShiftImm ALU_SRL 14 14 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5764 : bv 32 := 0x02f00793.
Lemma F_b5764 : fetch_word Plain.M.loaded_segments (0xb591c : word) = Some W_b5764.
Proof. vm_refl. Qed.
Lemma D_b5764 : decode_any W_b5764 = Some (OpImm ALU_ADD 15 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5768 : bv 32 := 0x02e7ea63.
Lemma F_b5768 : fetch_word Plain.M.loaded_segments (0xb5920 : word) = Some W_b5768.
Proof. vm_refl. Qed.
Lemma D_b5768 : decode_any W_b5768 = Some (Branch BC_LTU 15 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b576c : bv 32 := 0x00171713.
Lemma F_b576c : fetch_word Plain.M.loaded_segments (0xb5924 : word) = Some W_b576c.
Proof. vm_refl. Qed.
Lemma D_b576c : decode_any W_b576c = Some (ShiftImm ALU_SLL 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5770 : bv 32 := 0xfff6c797.
Lemma F_b5770 : fetch_word Plain.M.loaded_segments (0xb5928 : word) = Some W_b5770.
Proof. vm_refl. Qed.
Lemma D_b5770 : decode_any W_b5770 = Some (Auipc 15 1048428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5774 : bv 32 := 0xf2878793.
Lemma F_b5774 : fetch_word Plain.M.loaded_segments (0xb592c : word) = Some W_b5774.
Proof. vm_refl. Qed.
Lemma D_b5774 : decode_any W_b5774 = Some (OpImm ALU_ADD 15 15 3880, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5778 : bv 32 := 0x00e78733.
Lemma F_b5778 : fetch_word Plain.M.loaded_segments (0xb5930 : word) = Some W_b5778.
Proof. vm_refl. Qed.
Lemma D_b5778 : decode_any W_b5778 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b577c : bv 32 := 0x00075703.
Lemma F_b577c : fetch_word Plain.M.loaded_segments (0xb5934 : word) = Some W_b577c.
Proof. vm_refl. Qed.
Lemma D_b577c : decode_any W_b577c = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5780 : bv 32 := 0x02d707b3.
Lemma F_b5780 : fetch_word Plain.M.loaded_segments (0xb5938 : word) = Some W_b5780.
Proof. vm_refl. Qed.
Lemma D_b5780 : decode_any W_b5780 = Some (Mul M_MUL 15 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5784 : bv 32 := 0x00f5f463.
Lemma F_b5784 : fetch_word Plain.M.loaded_segments (0xb593c : word) = Some W_b5784.
Proof. vm_refl. Qed.
Lemma D_b5784 : decode_any W_b5784 = Some (Branch BC_GEU 11 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5788 : bv 32 := 0x00000023.
Lemma F_b5788 : fetch_word Plain.M.loaded_segments (0xb5940 : word) = Some W_b5788.
Proof. vm_refl. Qed.
Lemma D_b5788 : decode_any W_b5788 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b578c : bv 32 := 0x00168693.
Lemma F_b578c : fetch_word Plain.M.loaded_segments (0xb5944 : word) = Some W_b578c.
Proof. vm_refl. Qed.
Lemma D_b578c : decode_any W_b578c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5790 : bv 32 := 0x02e686b3.
Lemma F_b5790 : fetch_word Plain.M.loaded_segments (0xb5948 : word) = Some W_b5790.
Proof. vm_refl. Qed.
Lemma D_b5790 : decode_any W_b5790 = Some (Mul M_MUL 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5794 : bv 32 := 0x00d5f863.
Lemma F_b5794 : fetch_word Plain.M.loaded_segments (0xb594c : word) = Some W_b5794.
Proof. vm_refl. Qed.
Lemma D_b5794 : decode_any W_b5794 = Some (Branch BC_GEU 11 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5798 : bv 32 := 0x0100006f.
Lemma F_b5798 : fetch_word Plain.M.loaded_segments (0xb5950 : word) = Some W_b5798.
Proof. vm_refl. Qed.
Lemma D_b5798 : decode_any W_b5798 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b579c : bv 32 := 0x03f00693.
Lemma F_b579c : fetch_word Plain.M.loaded_segments (0xb5954 : word) = Some W_b579c.
Proof. vm_refl. Qed.
Lemma D_b579c : decode_any W_b579c = Some (OpImm ALU_ADD 13 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b57a0 : bv 32 := 0x00d70463.
Lemma F_b57a0 : fetch_word Plain.M.loaded_segments (0xb5958 : word) = Some W_b57a0.
Proof. vm_refl. Qed.
Lemma D_b57a0 : decode_any W_b57a0 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b57a4 : bv 32 := 0x00000023.
Lemma F_b57a4 : fetch_word Plain.M.loaded_segments (0xb595c : word) = Some W_b57a4.
Proof. vm_refl. Qed.
Lemma D_b57a4 : decode_any W_b57a4 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b57a8 : bv 32 := 0x00c65613.
Lemma F_b57a8 : fetch_word Plain.M.loaded_segments (0xb5960 : word) = Some W_b57a8.
Proof. vm_refl. Qed.
Lemma D_b57a8 : decode_any W_b57a8 = Some (ShiftImm ALU_SRL 12 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b57ac : bv 32 := 0x00060a63.
Lemma F_b57ac : fetch_word Plain.M.loaded_segments (0xb5964 : word) = Some W_b57ac.
Proof. vm_refl. Qed.
Lemma D_b57ac : decode_any W_b57ac = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b57b0 : bv 32 := 0x00861613.
Lemma F_b57b0 : fetch_word Plain.M.loaded_segments (0xb5968 : word) = Some W_b57b0.
Proof. vm_refl. Qed.
Lemma D_b57b0 : decode_any W_b57b0 = Some (ShiftImm ALU_SLL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b57b4 : bv 32 := 0xfff60613.
Lemma F_b57b4 : fetch_word Plain.M.loaded_segments (0xb596c : word) = Some W_b57b4.
Proof. vm_refl. Qed.
Lemma D_b57b4 : decode_any W_b57b4 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b57b8 : bv 32 := 0x00b67463.
Lemma F_b57b8 : fetch_word Plain.M.loaded_segments (0xb5970 : word) = Some W_b57b8.
Proof. vm_refl. Qed.
Lemma D_b57b8 : decode_any W_b57b8 = Some (Branch BC_GEU 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b57bc : bv 32 := 0x00000023.
Lemma F_b57bc : fetch_word Plain.M.loaded_segments (0xb5974 : word) = Some W_b57bc.
Proof. vm_refl. Qed.
Lemma D_b57bc : decode_any W_b57bc = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b57c0 : bv 32 := 0x00008067.
Lemma F_b57c0 : fetch_word Plain.M.loaded_segments (0xb5978 : word) = Some W_b57c0.
Proof. vm_refl. Qed.
Lemma D_b57c0 : decode_any W_b57c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
