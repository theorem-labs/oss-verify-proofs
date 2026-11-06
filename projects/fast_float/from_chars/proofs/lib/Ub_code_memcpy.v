(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_600a8 : bv 32 := 0x0035f693.
Lemma F_600a8 : fetch_word Ubsan.M.loaded_segments (0x600a8 : word) = Some W_600a8.
Proof. vm_refl. Qed.
Lemma D_600a8 : decode_any W_600a8 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600ac : bv 32 := 0x10068863.
Lemma F_600ac : fetch_word Ubsan.M.loaded_segments (0x600ac : word) = Some W_600ac.
Proof. vm_refl. Qed.
Lemma D_600ac : decode_any W_600ac = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600b0 : bv 32 := 0x02060e63.
Lemma F_600b0 : fetch_word Ubsan.M.loaded_segments (0x600b0 : word) = Some W_600b0.
Proof. vm_refl. Qed.
Lemma D_600b0 : decode_any W_600b0 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600b4 : bv 32 := 0x00158713.
Lemma F_600b4 : fetch_word Ubsan.M.loaded_segments (0x600b4 : word) = Some W_600b4.
Proof. vm_refl. Qed.
Lemma D_600b4 : decode_any W_600b4 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600b8 : bv 32 := 0x00100793.
Lemma F_600b8 : fetch_word Ubsan.M.loaded_segments (0x600b8 : word) = Some W_600b8.
Proof. vm_refl. Qed.
Lemma D_600b8 : decode_any W_600b8 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600bc : bv 32 := 0x00050693.
Lemma F_600bc : fetch_word Ubsan.M.loaded_segments (0x600bc : word) = Some W_600bc.
Proof. vm_refl. Qed.
Lemma D_600bc : decode_any W_600bc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600c0 : bv 32 := 0x0005c883.
Lemma F_600c0 : fetch_word Ubsan.M.loaded_segments (0x600c0 : word) = Some W_600c0.
Proof. vm_refl. Qed.
Lemma D_600c0 : decode_any W_600c0 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600c4 : bv 32 := 0x00060813.
Lemma F_600c4 : fetch_word Ubsan.M.loaded_segments (0x600c4 : word) = Some W_600c4.
Proof. vm_refl. Qed.
Lemma D_600c4 : decode_any W_600c4 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600c8 : bv 32 := 0x00158593.
Lemma F_600c8 : fetch_word Ubsan.M.loaded_segments (0x600c8 : word) = Some W_600c8.
Proof. vm_refl. Qed.
Lemma D_600c8 : decode_any W_600c8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600cc : bv 32 := 0x00377293.
Lemma F_600cc : fetch_word Ubsan.M.loaded_segments (0x600cc : word) = Some W_600cc.
Proof. vm_refl. Qed.
Lemma D_600cc : decode_any W_600cc = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600d0 : bv 32 := 0x01168023.
Lemma F_600d0 : fetch_word Ubsan.M.loaded_segments (0x600d0 : word) = Some W_600d0.
Proof. vm_refl. Qed.
Lemma D_600d0 : decode_any W_600d0 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600d4 : bv 32 := 0x00168693.
Lemma F_600d4 : fetch_word Ubsan.M.loaded_segments (0x600d4 : word) = Some W_600d4.
Proof. vm_refl. Qed.
Lemma D_600d4 : decode_any W_600d4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600d8 : bv 32 := 0xfff60613.
Lemma F_600d8 : fetch_word Ubsan.M.loaded_segments (0x600d8 : word) = Some W_600d8.
Proof. vm_refl. Qed.
Lemma D_600d8 : decode_any W_600d8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600dc : bv 32 := 0x00028a63.
Lemma F_600dc : fetch_word Ubsan.M.loaded_segments (0x600dc : word) = Some W_600dc.
Proof. vm_refl. Qed.
Lemma D_600dc : decode_any W_600dc = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600e0 : bv 32 := 0x00170713.
Lemma F_600e0 : fetch_word Ubsan.M.loaded_segments (0x600e0 : word) = Some W_600e0.
Proof. vm_refl. Qed.
Lemma D_600e0 : decode_any W_600e0 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600e4 : bv 32 := 0xfcf81ee3.
Lemma F_600e4 : fetch_word Ubsan.M.loaded_segments (0x600e4 : word) = Some W_600e4.
Proof. vm_refl. Qed.
Lemma D_600e4 : decode_any W_600e4 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600e8 : bv 32 := 0x0080006f.
Lemma F_600e8 : fetch_word Ubsan.M.loaded_segments (0x600e8 : word) = Some W_600e8.
Proof. vm_refl. Qed.
Lemma D_600e8 : decode_any W_600e8 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600ec : bv 32 := 0x00050693.
Lemma F_600ec : fetch_word Ubsan.M.loaded_segments (0x600ec : word) = Some W_600ec.
Proof. vm_refl. Qed.
Lemma D_600ec : decode_any W_600ec = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600f0 : bv 32 := 0x0036f793.
Lemma F_600f0 : fetch_word Ubsan.M.loaded_segments (0x600f0 : word) = Some W_600f0.
Proof. vm_refl. Qed.
Lemma D_600f0 : decode_any W_600f0 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600f4 : bv 32 := 0x0c078a63.
Lemma F_600f4 : fetch_word Ubsan.M.loaded_segments (0x600f4 : word) = Some W_600f4.
Proof. vm_refl. Qed.
Lemma D_600f4 : decode_any W_600f4 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600f8 : bv 32 := 0x02000713.
Lemma F_600f8 : fetch_word Ubsan.M.loaded_segments (0x600f8 : word) = Some W_600f8.
Proof. vm_refl. Qed.
Lemma D_600f8 : decode_any W_600f8 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600fc : bv 32 := 0x02e67063.
Lemma F_600fc : fetch_word Ubsan.M.loaded_segments (0x600fc : word) = Some W_600fc.
Proof. vm_refl. Qed.
Lemma D_600fc : decode_any W_600fc = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60100 : bv 32 := 0x01000713.
Lemma F_60100 : fetch_word Ubsan.M.loaded_segments (0x60100 : word) = Some W_60100.
Proof. vm_refl. Qed.
Lemma D_60100 : decode_any W_60100 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60104 : bv 32 := 0x24e67863.
Lemma F_60104 : fetch_word Ubsan.M.loaded_segments (0x60104 : word) = Some W_60104.
Proof. vm_refl. Qed.
Lemma D_60104 : decode_any W_60104 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60108 : bv 32 := 0x00867713.
Lemma F_60108 : fetch_word Ubsan.M.loaded_segments (0x60108 : word) = Some W_60108.
Proof. vm_refl. Qed.
Lemma D_60108 : decode_any W_60108 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6010c : bv 32 := 0x2c071e63.
Lemma F_6010c : fetch_word Ubsan.M.loaded_segments (0x6010c : word) = Some W_6010c.
Proof. vm_refl. Qed.
Lemma D_6010c : decode_any W_6010c = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60110 : bv 32 := 0x00467713.
Lemma F_60110 : fetch_word Ubsan.M.loaded_segments (0x60110 : word) = Some W_60110.
Proof. vm_refl. Qed.
Lemma D_60110 : decode_any W_60110 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60114 : bv 32 := 0x32071463.
Lemma F_60114 : fetch_word Ubsan.M.loaded_segments (0x60114 : word) = Some W_60114.
Proof. vm_refl. Qed.
Lemma D_60114 : decode_any W_60114 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60118 : bv 32 := 0x3500006f.
Lemma F_60118 : fetch_word Ubsan.M.loaded_segments (0x60118 : word) = Some W_60118.
Proof. vm_refl. Qed.
Lemma D_60118 : decode_any W_60118 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6011c : bv 32 := 0x0005a703.
Lemma F_6011c : fetch_word Ubsan.M.loaded_segments (0x6011c : word) = Some W_6011c.
Proof. vm_refl. Qed.
Lemma D_6011c : decode_any W_6011c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60120 : bv 32 := 0x00300813.
Lemma F_60120 : fetch_word Ubsan.M.loaded_segments (0x60120 : word) = Some W_60120.
Proof. vm_refl. Qed.
Lemma D_60120 : decode_any W_60120 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60124 : bv 32 := 0x11078e63.
Lemma F_60124 : fetch_word Ubsan.M.loaded_segments (0x60124 : word) = Some W_60124.
Proof. vm_refl. Qed.
Lemma D_60124 : decode_any W_60124 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60128 : bv 32 := 0x00200813.
Lemma F_60128 : fetch_word Ubsan.M.loaded_segments (0x60128 : word) = Some W_60128.
Proof. vm_refl. Qed.
Lemma D_60128 : decode_any W_60128 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6012c : bv 32 := 0x19079c63.
Lemma F_6012c : fetch_word Ubsan.M.loaded_segments (0x6012c : word) = Some W_6012c.
Proof. vm_refl. Qed.
Lemma D_6012c : decode_any W_6012c = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60130 : bv 32 := 0x00875793.
Lemma F_60130 : fetch_word Ubsan.M.loaded_segments (0x60130 : word) = Some W_60130.
Proof. vm_refl. Qed.
Lemma D_60130 : decode_any W_60130 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60134 : bv 32 := 0xffe60613.
Lemma F_60134 : fetch_word Ubsan.M.loaded_segments (0x60134 : word) = Some W_60134.
Proof. vm_refl. Qed.
Lemma D_60134 : decode_any W_60134 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60138 : bv 32 := 0x00e68023.
Lemma F_60138 : fetch_word Ubsan.M.loaded_segments (0x60138 : word) = Some W_60138.
Proof. vm_refl. Qed.
Lemma D_60138 : decode_any W_60138 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6013c : bv 32 := 0x00f680a3.
Lemma F_6013c : fetch_word Ubsan.M.loaded_segments (0x6013c : word) = Some W_6013c.
Proof. vm_refl. Qed.
Lemma D_6013c : decode_any W_6013c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60140 : bv 32 := 0x00268693.
Lemma F_60140 : fetch_word Ubsan.M.loaded_segments (0x60140 : word) = Some W_60140.
Proof. vm_refl. Qed.
Lemma D_60140 : decode_any W_60140 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60144 : bv 32 := 0x01058593.
Lemma F_60144 : fetch_word Ubsan.M.loaded_segments (0x60144 : word) = Some W_60144.
Proof. vm_refl. Qed.
Lemma D_60144 : decode_any W_60144 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60148 : bv 32 := 0x01100793.
Lemma F_60148 : fetch_word Ubsan.M.loaded_segments (0x60148 : word) = Some W_60148.
Proof. vm_refl. Qed.
Lemma D_60148 : decode_any W_60148 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6014c : bv 32 := 0x0107581b.
Lemma F_6014c : fetch_word Ubsan.M.loaded_segments (0x6014c : word) = Some W_6014c.
Proof. vm_refl. Qed.
Lemma D_6014c : decode_any W_6014c = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60150 : bv 32 := 0xff45a883.
Lemma F_60150 : fetch_word Ubsan.M.loaded_segments (0x60150 : word) = Some W_60150.
Proof. vm_refl. Qed.
Lemma D_60150 : decode_any W_60150 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60154 : bv 32 := 0xff85a283.
Lemma F_60154 : fetch_word Ubsan.M.loaded_segments (0x60154 : word) = Some W_60154.
Proof. vm_refl. Qed.
Lemma D_60154 : decode_any W_60154 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60158 : bv 32 := 0xffc5a303.
Lemma F_60158 : fetch_word Ubsan.M.loaded_segments (0x60158 : word) = Some W_60158.
Proof. vm_refl. Qed.
Lemma D_60158 : decode_any W_60158 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6015c : bv 32 := 0x0005a703.
Lemma F_6015c : fetch_word Ubsan.M.loaded_segments (0x6015c : word) = Some W_6015c.
Proof. vm_refl. Qed.
Lemma D_6015c : decode_any W_6015c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60160 : bv 32 := 0x01089393.
Lemma F_60160 : fetch_word Ubsan.M.loaded_segments (0x60160 : word) = Some W_60160.
Proof. vm_refl. Qed.
Lemma D_60160 : decode_any W_60160 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60164 : bv 32 := 0x0108d89b.
Lemma F_60164 : fetch_word Ubsan.M.loaded_segments (0x60164 : word) = Some W_60164.
Proof. vm_refl. Qed.
Lemma D_60164 : decode_any W_60164 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60168 : bv 32 := 0x0103e833.
Lemma F_60168 : fetch_word Ubsan.M.loaded_segments (0x60168 : word) = Some W_60168.
Proof. vm_refl. Qed.
Lemma D_60168 : decode_any W_60168 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6016c : bv 32 := 0x01029393.
Lemma F_6016c : fetch_word Ubsan.M.loaded_segments (0x6016c : word) = Some W_6016c.
Proof. vm_refl. Qed.
Lemma D_6016c : decode_any W_6016c = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60170 : bv 32 := 0x0102d29b.
Lemma F_60170 : fetch_word Ubsan.M.loaded_segments (0x60170 : word) = Some W_60170.
Proof. vm_refl. Qed.
Lemma D_60170 : decode_any W_60170 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60174 : bv 32 := 0x0113e8b3.
Lemma F_60174 : fetch_word Ubsan.M.loaded_segments (0x60174 : word) = Some W_60174.
Proof. vm_refl. Qed.
Lemma D_60174 : decode_any W_60174 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60178 : bv 32 := 0x01031393.
Lemma F_60178 : fetch_word Ubsan.M.loaded_segments (0x60178 : word) = Some W_60178.
Proof. vm_refl. Qed.
Lemma D_60178 : decode_any W_60178 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6017c : bv 32 := 0x0103531b.
Lemma F_6017c : fetch_word Ubsan.M.loaded_segments (0x6017c : word) = Some W_6017c.
Proof. vm_refl. Qed.
Lemma D_6017c : decode_any W_6017c = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60180 : bv 32 := 0x0053e2b3.
Lemma F_60180 : fetch_word Ubsan.M.loaded_segments (0x60180 : word) = Some W_60180.
Proof. vm_refl. Qed.
Lemma D_60180 : decode_any W_60180 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60184 : bv 32 := 0x01071393.
Lemma F_60184 : fetch_word Ubsan.M.loaded_segments (0x60184 : word) = Some W_60184.
Proof. vm_refl. Qed.
Lemma D_60184 : decode_any W_60184 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60188 : bv 32 := 0x0063e333.
Lemma F_60188 : fetch_word Ubsan.M.loaded_segments (0x60188 : word) = Some W_60188.
Proof. vm_refl. Qed.
Lemma D_60188 : decode_any W_60188 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6018c : bv 32 := 0xff060613.
Lemma F_6018c : fetch_word Ubsan.M.loaded_segments (0x6018c : word) = Some W_6018c.
Proof. vm_refl. Qed.
Lemma D_6018c : decode_any W_6018c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60190 : bv 32 := 0x0106a023.
Lemma F_60190 : fetch_word Ubsan.M.loaded_segments (0x60190 : word) = Some W_60190.
Proof. vm_refl. Qed.
Lemma D_60190 : decode_any W_60190 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60194 : bv 32 := 0x0116a223.
Lemma F_60194 : fetch_word Ubsan.M.loaded_segments (0x60194 : word) = Some W_60194.
Proof. vm_refl. Qed.
Lemma D_60194 : decode_any W_60194 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60198 : bv 32 := 0x0056a423.
Lemma F_60198 : fetch_word Ubsan.M.loaded_segments (0x60198 : word) = Some W_60198.
Proof. vm_refl. Qed.
Lemma D_60198 : decode_any W_60198 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6019c : bv 32 := 0x0066a623.
Lemma F_6019c : fetch_word Ubsan.M.loaded_segments (0x6019c : word) = Some W_6019c.
Proof. vm_refl. Qed.
Lemma D_6019c : decode_any W_6019c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601a0 : bv 32 := 0x01068693.
Lemma F_601a0 : fetch_word Ubsan.M.loaded_segments (0x601a0 : word) = Some W_601a0.
Proof. vm_refl. Qed.
Lemma D_601a0 : decode_any W_601a0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601a4 : bv 32 := 0x01058593.
Lemma F_601a4 : fetch_word Ubsan.M.loaded_segments (0x601a4 : word) = Some W_601a4.
Proof. vm_refl. Qed.
Lemma D_601a4 : decode_any W_601a4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601a8 : bv 32 := 0xfac7e2e3.
Lemma F_601a8 : fetch_word Ubsan.M.loaded_segments (0x601a8 : word) = Some W_601a8.
Proof. vm_refl. Qed.
Lemma D_601a8 : decode_any W_601a8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601ac : bv 32 := 0xff258593.
Lemma F_601ac : fetch_word Ubsan.M.loaded_segments (0x601ac : word) = Some W_601ac.
Proof. vm_refl. Qed.
Lemma D_601ac : decode_any W_601ac = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601b0 : bv 32 := 0x01000713.
Lemma F_601b0 : fetch_word Ubsan.M.loaded_segments (0x601b0 : word) = Some W_601b0.
Proof. vm_refl. Qed.
Lemma D_601b0 : decode_any W_601b0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601b4 : bv 32 := 0xf4e66ae3.
Lemma F_601b4 : fetch_word Ubsan.M.loaded_segments (0x601b4 : word) = Some W_601b4.
Proof. vm_refl. Qed.
Lemma D_601b4 : decode_any W_601b4 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601b8 : bv 32 := 0x19c0006f.
Lemma F_601b8 : fetch_word Ubsan.M.loaded_segments (0x601b8 : word) = Some W_601b8.
Proof. vm_refl. Qed.
Lemma D_601b8 : decode_any W_601b8 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601bc : bv 32 := 0x00050693.
Lemma F_601bc : fetch_word Ubsan.M.loaded_segments (0x601bc : word) = Some W_601bc.
Proof. vm_refl. Qed.
Lemma D_601bc : decode_any W_601bc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601c0 : bv 32 := 0x00357793.
Lemma F_601c0 : fetch_word Ubsan.M.loaded_segments (0x601c0 : word) = Some W_601c0.
Proof. vm_refl. Qed.
Lemma D_601c0 : decode_any W_601c0 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601c4 : bv 32 := 0xf2079ae3.
Lemma F_601c4 : fetch_word Ubsan.M.loaded_segments (0x601c4 : word) = Some W_601c4.
Proof. vm_refl. Qed.
Lemma D_601c4 : decode_any W_601c4 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601c8 : bv 32 := 0x01000713.
Lemma F_601c8 : fetch_word Ubsan.M.loaded_segments (0x601c8 : word) = Some W_601c8.
Proof. vm_refl. Qed.
Lemma D_601c8 : decode_any W_601c8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601cc : bv 32 := 0x02e66c63.
Lemma F_601cc : fetch_word Ubsan.M.loaded_segments (0x601cc : word) = Some W_601cc.
Proof. vm_refl. Qed.
Lemma D_601cc : decode_any W_601cc = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601d0 : bv 32 := 0x00f00713.
Lemma F_601d0 : fetch_word Ubsan.M.loaded_segments (0x601d0 : word) = Some W_601d0.
Proof. vm_refl. Qed.
Lemma D_601d0 : decode_any W_601d0 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601d4 : bv 32 := 0x0005a783.
Lemma F_601d4 : fetch_word Ubsan.M.loaded_segments (0x601d4 : word) = Some W_601d4.
Proof. vm_refl. Qed.
Lemma D_601d4 : decode_any W_601d4 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601d8 : bv 32 := 0x0045a803.
Lemma F_601d8 : fetch_word Ubsan.M.loaded_segments (0x601d8 : word) = Some W_601d8.
Proof. vm_refl. Qed.
Lemma D_601d8 : decode_any W_601d8 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601dc : bv 32 := 0x0085a883.
Lemma F_601dc : fetch_word Ubsan.M.loaded_segments (0x601dc : word) = Some W_601dc.
Proof. vm_refl. Qed.
Lemma D_601dc : decode_any W_601dc = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601e0 : bv 32 := 0x00c5a283.
Lemma F_601e0 : fetch_word Ubsan.M.loaded_segments (0x601e0 : word) = Some W_601e0.
Proof. vm_refl. Qed.
Lemma D_601e0 : decode_any W_601e0 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601e4 : bv 32 := 0x01058593.
Lemma F_601e4 : fetch_word Ubsan.M.loaded_segments (0x601e4 : word) = Some W_601e4.
Proof. vm_refl. Qed.
Lemma D_601e4 : decode_any W_601e4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601e8 : bv 32 := 0xff060613.
Lemma F_601e8 : fetch_word Ubsan.M.loaded_segments (0x601e8 : word) = Some W_601e8.
Proof. vm_refl. Qed.
Lemma D_601e8 : decode_any W_601e8 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601ec : bv 32 := 0x00f6a023.
Lemma F_601ec : fetch_word Ubsan.M.loaded_segments (0x601ec : word) = Some W_601ec.
Proof. vm_refl. Qed.
Lemma D_601ec : decode_any W_601ec = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601f0 : bv 32 := 0x0106a223.
Lemma F_601f0 : fetch_word Ubsan.M.loaded_segments (0x601f0 : word) = Some W_601f0.
Proof. vm_refl. Qed.
Lemma D_601f0 : decode_any W_601f0 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601f4 : bv 32 := 0x0116a423.
Lemma F_601f4 : fetch_word Ubsan.M.loaded_segments (0x601f4 : word) = Some W_601f4.
Proof. vm_refl. Qed.
Lemma D_601f4 : decode_any W_601f4 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601f8 : bv 32 := 0x0056a623.
Lemma F_601f8 : fetch_word Ubsan.M.loaded_segments (0x601f8 : word) = Some W_601f8.
Proof. vm_refl. Qed.
Lemma D_601f8 : decode_any W_601f8 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601fc : bv 32 := 0x01068693.
Lemma F_601fc : fetch_word Ubsan.M.loaded_segments (0x601fc : word) = Some W_601fc.
Proof. vm_refl. Qed.
Lemma D_601fc : decode_any W_601fc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60200 : bv 32 := 0xfcc76ae3.
Lemma F_60200 : fetch_word Ubsan.M.loaded_segments (0x60200 : word) = Some W_60200.
Proof. vm_refl. Qed.
Lemma D_60200 : decode_any W_60200 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60204 : bv 32 := 0x00800713.
Lemma F_60204 : fetch_word Ubsan.M.loaded_segments (0x60204 : word) = Some W_60204.
Proof. vm_refl. Qed.
Lemma D_60204 : decode_any W_60204 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60208 : bv 32 := 0x00e66e63.
Lemma F_60208 : fetch_word Ubsan.M.loaded_segments (0x60208 : word) = Some W_60208.
Proof. vm_refl. Qed.
Lemma D_60208 : decode_any W_60208 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6020c : bv 32 := 0x0005a703.
Lemma F_6020c : fetch_word Ubsan.M.loaded_segments (0x6020c : word) = Some W_6020c.
Proof. vm_refl. Qed.
Lemma D_6020c : decode_any W_6020c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60210 : bv 32 := 0x0045a783.
Lemma F_60210 : fetch_word Ubsan.M.loaded_segments (0x60210 : word) = Some W_60210.
Proof. vm_refl. Qed.
Lemma D_60210 : decode_any W_60210 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60214 : bv 32 := 0x00e6a023.
Lemma F_60214 : fetch_word Ubsan.M.loaded_segments (0x60214 : word) = Some W_60214.
Proof. vm_refl. Qed.
Lemma D_60214 : decode_any W_60214 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60218 : bv 32 := 0x00f6a223.
Lemma F_60218 : fetch_word Ubsan.M.loaded_segments (0x60218 : word) = Some W_60218.
Proof. vm_refl. Qed.
Lemma D_60218 : decode_any W_60218 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6021c : bv 32 := 0x00868693.
Lemma F_6021c : fetch_word Ubsan.M.loaded_segments (0x6021c : word) = Some W_6021c.
Proof. vm_refl. Qed.
Lemma D_6021c : decode_any W_6021c = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60220 : bv 32 := 0x00858593.
Lemma F_60220 : fetch_word Ubsan.M.loaded_segments (0x60220 : word) = Some W_60220.
Proof. vm_refl. Qed.
Lemma D_60220 : decode_any W_60220 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60224 : bv 32 := 0x00467713.
Lemma F_60224 : fetch_word Ubsan.M.loaded_segments (0x60224 : word) = Some W_60224.
Proof. vm_refl. Qed.
Lemma D_60224 : decode_any W_60224 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60228 : bv 32 := 0x24070063.
Lemma F_60228 : fetch_word Ubsan.M.loaded_segments (0x60228 : word) = Some W_60228.
Proof. vm_refl. Qed.
Lemma D_60228 : decode_any W_60228 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6022c : bv 32 := 0x0005a703.
Lemma F_6022c : fetch_word Ubsan.M.loaded_segments (0x6022c : word) = Some W_6022c.
Proof. vm_refl. Qed.
Lemma D_6022c : decode_any W_6022c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60230 : bv 32 := 0x00458593.
Lemma F_60230 : fetch_word Ubsan.M.loaded_segments (0x60230 : word) = Some W_60230.
Proof. vm_refl. Qed.
Lemma D_60230 : decode_any W_60230 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60234 : bv 32 := 0x00e6a023.
Lemma F_60234 : fetch_word Ubsan.M.loaded_segments (0x60234 : word) = Some W_60234.
Proof. vm_refl. Qed.
Lemma D_60234 : decode_any W_60234 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60238 : bv 32 := 0x00468693.
Lemma F_60238 : fetch_word Ubsan.M.loaded_segments (0x60238 : word) = Some W_60238.
Proof. vm_refl. Qed.
Lemma D_60238 : decode_any W_60238 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6023c : bv 32 := 0x22c0006f.
Lemma F_6023c : fetch_word Ubsan.M.loaded_segments (0x6023c : word) = Some W_6023c.
Proof. vm_refl. Qed.
Lemma D_6023c : decode_any W_6023c = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60240 : bv 32 := 0x00e68023.
Lemma F_60240 : fetch_word Ubsan.M.loaded_segments (0x60240 : word) = Some W_60240.
Proof. vm_refl. Qed.
Lemma D_60240 : decode_any W_60240 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60244 : bv 32 := 0x00168693.
Lemma F_60244 : fetch_word Ubsan.M.loaded_segments (0x60244 : word) = Some W_60244.
Proof. vm_refl. Qed.
Lemma D_60244 : decode_any W_60244 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60248 : bv 32 := 0xfff60613.
Lemma F_60248 : fetch_word Ubsan.M.loaded_segments (0x60248 : word) = Some W_60248.
Proof. vm_refl. Qed.
Lemma D_60248 : decode_any W_60248 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6024c : bv 32 := 0x01058593.
Lemma F_6024c : fetch_word Ubsan.M.loaded_segments (0x6024c : word) = Some W_6024c.
Proof. vm_refl. Qed.
Lemma D_6024c : decode_any W_6024c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60250 : bv 32 := 0x01200793.
Lemma F_60250 : fetch_word Ubsan.M.loaded_segments (0x60250 : word) = Some W_60250.
Proof. vm_refl. Qed.
Lemma D_60250 : decode_any W_60250 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60254 : bv 32 := 0x0087581b.
Lemma F_60254 : fetch_word Ubsan.M.loaded_segments (0x60254 : word) = Some W_60254.
Proof. vm_refl. Qed.
Lemma D_60254 : decode_any W_60254 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60258 : bv 32 := 0xff45a883.
Lemma F_60258 : fetch_word Ubsan.M.loaded_segments (0x60258 : word) = Some W_60258.
Proof. vm_refl. Qed.
Lemma D_60258 : decode_any W_60258 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6025c : bv 32 := 0xff85a283.
Lemma F_6025c : fetch_word Ubsan.M.loaded_segments (0x6025c : word) = Some W_6025c.
Proof. vm_refl. Qed.
Lemma D_6025c : decode_any W_6025c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60260 : bv 32 := 0xffc5a303.
Lemma F_60260 : fetch_word Ubsan.M.loaded_segments (0x60260 : word) = Some W_60260.
Proof. vm_refl. Qed.
Lemma D_60260 : decode_any W_60260 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60264 : bv 32 := 0x0005a703.
Lemma F_60264 : fetch_word Ubsan.M.loaded_segments (0x60264 : word) = Some W_60264.
Proof. vm_refl. Qed.
Lemma D_60264 : decode_any W_60264 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60268 : bv 32 := 0x01889393.
Lemma F_60268 : fetch_word Ubsan.M.loaded_segments (0x60268 : word) = Some W_60268.
Proof. vm_refl. Qed.
Lemma D_60268 : decode_any W_60268 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6026c : bv 32 := 0x0088d89b.
Lemma F_6026c : fetch_word Ubsan.M.loaded_segments (0x6026c : word) = Some W_6026c.
Proof. vm_refl. Qed.
Lemma D_6026c : decode_any W_6026c = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60270 : bv 32 := 0x0103e833.
Lemma F_60270 : fetch_word Ubsan.M.loaded_segments (0x60270 : word) = Some W_60270.
Proof. vm_refl. Qed.
Lemma D_60270 : decode_any W_60270 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60274 : bv 32 := 0x01829393.
Lemma F_60274 : fetch_word Ubsan.M.loaded_segments (0x60274 : word) = Some W_60274.
Proof. vm_refl. Qed.
Lemma D_60274 : decode_any W_60274 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60278 : bv 32 := 0x0082d29b.
Lemma F_60278 : fetch_word Ubsan.M.loaded_segments (0x60278 : word) = Some W_60278.
Proof. vm_refl. Qed.
Lemma D_60278 : decode_any W_60278 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6027c : bv 32 := 0x0113e8b3.
Lemma F_6027c : fetch_word Ubsan.M.loaded_segments (0x6027c : word) = Some W_6027c.
Proof. vm_refl. Qed.
Lemma D_6027c : decode_any W_6027c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60280 : bv 32 := 0x01831393.
Lemma F_60280 : fetch_word Ubsan.M.loaded_segments (0x60280 : word) = Some W_60280.
Proof. vm_refl. Qed.
Lemma D_60280 : decode_any W_60280 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60284 : bv 32 := 0x0083531b.
Lemma F_60284 : fetch_word Ubsan.M.loaded_segments (0x60284 : word) = Some W_60284.
Proof. vm_refl. Qed.
Lemma D_60284 : decode_any W_60284 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60288 : bv 32 := 0x0053e2b3.
Lemma F_60288 : fetch_word Ubsan.M.loaded_segments (0x60288 : word) = Some W_60288.
Proof. vm_refl. Qed.
Lemma D_60288 : decode_any W_60288 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6028c : bv 32 := 0x01871393.
Lemma F_6028c : fetch_word Ubsan.M.loaded_segments (0x6028c : word) = Some W_6028c.
Proof. vm_refl. Qed.
Lemma D_6028c : decode_any W_6028c = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60290 : bv 32 := 0x0063e333.
Lemma F_60290 : fetch_word Ubsan.M.loaded_segments (0x60290 : word) = Some W_60290.
Proof. vm_refl. Qed.
Lemma D_60290 : decode_any W_60290 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60294 : bv 32 := 0xff060613.
Lemma F_60294 : fetch_word Ubsan.M.loaded_segments (0x60294 : word) = Some W_60294.
Proof. vm_refl. Qed.
Lemma D_60294 : decode_any W_60294 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60298 : bv 32 := 0x0106a023.
Lemma F_60298 : fetch_word Ubsan.M.loaded_segments (0x60298 : word) = Some W_60298.
Proof. vm_refl. Qed.
Lemma D_60298 : decode_any W_60298 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6029c : bv 32 := 0x0116a223.
Lemma F_6029c : fetch_word Ubsan.M.loaded_segments (0x6029c : word) = Some W_6029c.
Proof. vm_refl. Qed.
Lemma D_6029c : decode_any W_6029c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602a0 : bv 32 := 0x0056a423.
Lemma F_602a0 : fetch_word Ubsan.M.loaded_segments (0x602a0 : word) = Some W_602a0.
Proof. vm_refl. Qed.
Lemma D_602a0 : decode_any W_602a0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602a4 : bv 32 := 0x0066a623.
Lemma F_602a4 : fetch_word Ubsan.M.loaded_segments (0x602a4 : word) = Some W_602a4.
Proof. vm_refl. Qed.
Lemma D_602a4 : decode_any W_602a4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602a8 : bv 32 := 0x01068693.
Lemma F_602a8 : fetch_word Ubsan.M.loaded_segments (0x602a8 : word) = Some W_602a8.
Proof. vm_refl. Qed.
Lemma D_602a8 : decode_any W_602a8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602ac : bv 32 := 0x01058593.
Lemma F_602ac : fetch_word Ubsan.M.loaded_segments (0x602ac : word) = Some W_602ac.
Proof. vm_refl. Qed.
Lemma D_602ac : decode_any W_602ac = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602b0 : bv 32 := 0xfac7e2e3.
Lemma F_602b0 : fetch_word Ubsan.M.loaded_segments (0x602b0 : word) = Some W_602b0.
Proof. vm_refl. Qed.
Lemma D_602b0 : decode_any W_602b0 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602b4 : bv 32 := 0xff158593.
Lemma F_602b4 : fetch_word Ubsan.M.loaded_segments (0x602b4 : word) = Some W_602b4.
Proof. vm_refl. Qed.
Lemma D_602b4 : decode_any W_602b4 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602b8 : bv 32 := 0x01000713.
Lemma F_602b8 : fetch_word Ubsan.M.loaded_segments (0x602b8 : word) = Some W_602b8.
Proof. vm_refl. Qed.
Lemma D_602b8 : decode_any W_602b8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602bc : bv 32 := 0xe4e666e3.
Lemma F_602bc : fetch_word Ubsan.M.loaded_segments (0x602bc : word) = Some W_602bc.
Proof. vm_refl. Qed.
Lemma D_602bc : decode_any W_602bc = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602c0 : bv 32 := 0x0940006f.
Lemma F_602c0 : fetch_word Ubsan.M.loaded_segments (0x602c0 : word) = Some W_602c0.
Proof. vm_refl. Qed.
Lemma D_602c0 : decode_any W_602c0 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602c4 : bv 32 := 0x00875793.
Lemma F_602c4 : fetch_word Ubsan.M.loaded_segments (0x602c4 : word) = Some W_602c4.
Proof. vm_refl. Qed.
Lemma D_602c4 : decode_any W_602c4 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602c8 : bv 32 := 0x01075813.
Lemma F_602c8 : fetch_word Ubsan.M.loaded_segments (0x602c8 : word) = Some W_602c8.
Proof. vm_refl. Qed.
Lemma D_602c8 : decode_any W_602c8 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602cc : bv 32 := 0xffd60613.
Lemma F_602cc : fetch_word Ubsan.M.loaded_segments (0x602cc : word) = Some W_602cc.
Proof. vm_refl. Qed.
Lemma D_602cc : decode_any W_602cc = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602d0 : bv 32 := 0x00e68023.
Lemma F_602d0 : fetch_word Ubsan.M.loaded_segments (0x602d0 : word) = Some W_602d0.
Proof. vm_refl. Qed.
Lemma D_602d0 : decode_any W_602d0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602d4 : bv 32 := 0x00f680a3.
Lemma F_602d4 : fetch_word Ubsan.M.loaded_segments (0x602d4 : word) = Some W_602d4.
Proof. vm_refl. Qed.
Lemma D_602d4 : decode_any W_602d4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602d8 : bv 32 := 0x01068123.
Lemma F_602d8 : fetch_word Ubsan.M.loaded_segments (0x602d8 : word) = Some W_602d8.
Proof. vm_refl. Qed.
Lemma D_602d8 : decode_any W_602d8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602dc : bv 32 := 0x00368693.
Lemma F_602dc : fetch_word Ubsan.M.loaded_segments (0x602dc : word) = Some W_602dc.
Proof. vm_refl. Qed.
Lemma D_602dc : decode_any W_602dc = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602e0 : bv 32 := 0x01058593.
Lemma F_602e0 : fetch_word Ubsan.M.loaded_segments (0x602e0 : word) = Some W_602e0.
Proof. vm_refl. Qed.
Lemma D_602e0 : decode_any W_602e0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602e4 : bv 32 := 0x01000793.
Lemma F_602e4 : fetch_word Ubsan.M.loaded_segments (0x602e4 : word) = Some W_602e4.
Proof. vm_refl. Qed.
Lemma D_602e4 : decode_any W_602e4 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602e8 : bv 32 := 0x0187581b.
Lemma F_602e8 : fetch_word Ubsan.M.loaded_segments (0x602e8 : word) = Some W_602e8.
Proof. vm_refl. Qed.
Lemma D_602e8 : decode_any W_602e8 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602ec : bv 32 := 0xff45a883.
Lemma F_602ec : fetch_word Ubsan.M.loaded_segments (0x602ec : word) = Some W_602ec.
Proof. vm_refl. Qed.
Lemma D_602ec : decode_any W_602ec = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602f0 : bv 32 := 0xff85a283.
Lemma F_602f0 : fetch_word Ubsan.M.loaded_segments (0x602f0 : word) = Some W_602f0.
Proof. vm_refl. Qed.
Lemma D_602f0 : decode_any W_602f0 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602f4 : bv 32 := 0xffc5a303.
Lemma F_602f4 : fetch_word Ubsan.M.loaded_segments (0x602f4 : word) = Some W_602f4.
Proof. vm_refl. Qed.
Lemma D_602f4 : decode_any W_602f4 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602f8 : bv 32 := 0x0005a703.
Lemma F_602f8 : fetch_word Ubsan.M.loaded_segments (0x602f8 : word) = Some W_602f8.
Proof. vm_refl. Qed.
Lemma D_602f8 : decode_any W_602f8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602fc : bv 32 := 0x00889393.
Lemma F_602fc : fetch_word Ubsan.M.loaded_segments (0x602fc : word) = Some W_602fc.
Proof. vm_refl. Qed.
Lemma D_602fc : decode_any W_602fc = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60300 : bv 32 := 0x0188d89b.
Lemma F_60300 : fetch_word Ubsan.M.loaded_segments (0x60300 : word) = Some W_60300.
Proof. vm_refl. Qed.
Lemma D_60300 : decode_any W_60300 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60304 : bv 32 := 0x0103e833.
Lemma F_60304 : fetch_word Ubsan.M.loaded_segments (0x60304 : word) = Some W_60304.
Proof. vm_refl. Qed.
Lemma D_60304 : decode_any W_60304 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60308 : bv 32 := 0x00829393.
Lemma F_60308 : fetch_word Ubsan.M.loaded_segments (0x60308 : word) = Some W_60308.
Proof. vm_refl. Qed.
Lemma D_60308 : decode_any W_60308 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6030c : bv 32 := 0x0182d29b.
Lemma F_6030c : fetch_word Ubsan.M.loaded_segments (0x6030c : word) = Some W_6030c.
Proof. vm_refl. Qed.
Lemma D_6030c : decode_any W_6030c = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60310 : bv 32 := 0x0113e8b3.
Lemma F_60310 : fetch_word Ubsan.M.loaded_segments (0x60310 : word) = Some W_60310.
Proof. vm_refl. Qed.
Lemma D_60310 : decode_any W_60310 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60314 : bv 32 := 0x00831393.
Lemma F_60314 : fetch_word Ubsan.M.loaded_segments (0x60314 : word) = Some W_60314.
Proof. vm_refl. Qed.
Lemma D_60314 : decode_any W_60314 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60318 : bv 32 := 0x0183531b.
Lemma F_60318 : fetch_word Ubsan.M.loaded_segments (0x60318 : word) = Some W_60318.
Proof. vm_refl. Qed.
Lemma D_60318 : decode_any W_60318 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6031c : bv 32 := 0x0053e2b3.
Lemma F_6031c : fetch_word Ubsan.M.loaded_segments (0x6031c : word) = Some W_6031c.
Proof. vm_refl. Qed.
Lemma D_6031c : decode_any W_6031c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60320 : bv 32 := 0x00871393.
Lemma F_60320 : fetch_word Ubsan.M.loaded_segments (0x60320 : word) = Some W_60320.
Proof. vm_refl. Qed.
Lemma D_60320 : decode_any W_60320 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60324 : bv 32 := 0x0063e333.
Lemma F_60324 : fetch_word Ubsan.M.loaded_segments (0x60324 : word) = Some W_60324.
Proof. vm_refl. Qed.
Lemma D_60324 : decode_any W_60324 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60328 : bv 32 := 0xff060613.
Lemma F_60328 : fetch_word Ubsan.M.loaded_segments (0x60328 : word) = Some W_60328.
Proof. vm_refl. Qed.
Lemma D_60328 : decode_any W_60328 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6032c : bv 32 := 0x0106a023.
Lemma F_6032c : fetch_word Ubsan.M.loaded_segments (0x6032c : word) = Some W_6032c.
Proof. vm_refl. Qed.
Lemma D_6032c : decode_any W_6032c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60330 : bv 32 := 0x0116a223.
Lemma F_60330 : fetch_word Ubsan.M.loaded_segments (0x60330 : word) = Some W_60330.
Proof. vm_refl. Qed.
Lemma D_60330 : decode_any W_60330 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60334 : bv 32 := 0x0056a423.
Lemma F_60334 : fetch_word Ubsan.M.loaded_segments (0x60334 : word) = Some W_60334.
Proof. vm_refl. Qed.
Lemma D_60334 : decode_any W_60334 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60338 : bv 32 := 0x0066a623.
Lemma F_60338 : fetch_word Ubsan.M.loaded_segments (0x60338 : word) = Some W_60338.
Proof. vm_refl. Qed.
Lemma D_60338 : decode_any W_60338 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6033c : bv 32 := 0x01068693.
Lemma F_6033c : fetch_word Ubsan.M.loaded_segments (0x6033c : word) = Some W_6033c.
Proof. vm_refl. Qed.
Lemma D_6033c : decode_any W_6033c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60340 : bv 32 := 0x01058593.
Lemma F_60340 : fetch_word Ubsan.M.loaded_segments (0x60340 : word) = Some W_60340.
Proof. vm_refl. Qed.
Lemma D_60340 : decode_any W_60340 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60344 : bv 32 := 0xfac7e2e3.
Lemma F_60344 : fetch_word Ubsan.M.loaded_segments (0x60344 : word) = Some W_60344.
Proof. vm_refl. Qed.
Lemma D_60344 : decode_any W_60344 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60348 : bv 32 := 0xff358593.
Lemma F_60348 : fetch_word Ubsan.M.loaded_segments (0x60348 : word) = Some W_60348.
Proof. vm_refl. Qed.
Lemma D_60348 : decode_any W_60348 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6034c : bv 32 := 0x01000713.
Lemma F_6034c : fetch_word Ubsan.M.loaded_segments (0x6034c : word) = Some W_6034c.
Proof. vm_refl. Qed.
Lemma D_6034c : decode_any W_6034c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60350 : bv 32 := 0xdae66ce3.
Lemma F_60350 : fetch_word Ubsan.M.loaded_segments (0x60350 : word) = Some W_60350.
Proof. vm_refl. Qed.
Lemma D_60350 : decode_any W_60350 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60354 : bv 32 := 0x0005c703.
Lemma F_60354 : fetch_word Ubsan.M.loaded_segments (0x60354 : word) = Some W_60354.
Proof. vm_refl. Qed.
Lemma D_60354 : decode_any W_60354 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60358 : bv 32 := 0x0015c783.
Lemma F_60358 : fetch_word Ubsan.M.loaded_segments (0x60358 : word) = Some W_60358.
Proof. vm_refl. Qed.
Lemma D_60358 : decode_any W_60358 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6035c : bv 32 := 0x0025c803.
Lemma F_6035c : fetch_word Ubsan.M.loaded_segments (0x6035c : word) = Some W_6035c.
Proof. vm_refl. Qed.
Lemma D_6035c : decode_any W_6035c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60360 : bv 32 := 0x0035c883.
Lemma F_60360 : fetch_word Ubsan.M.loaded_segments (0x60360 : word) = Some W_60360.
Proof. vm_refl. Qed.
Lemma D_60360 : decode_any W_60360 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60364 : bv 32 := 0x0045c283.
Lemma F_60364 : fetch_word Ubsan.M.loaded_segments (0x60364 : word) = Some W_60364.
Proof. vm_refl. Qed.
Lemma D_60364 : decode_any W_60364 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60368 : bv 32 := 0x0055c303.
Lemma F_60368 : fetch_word Ubsan.M.loaded_segments (0x60368 : word) = Some W_60368.
Proof. vm_refl. Qed.
Lemma D_60368 : decode_any W_60368 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6036c : bv 32 := 0x0065c383.
Lemma F_6036c : fetch_word Ubsan.M.loaded_segments (0x6036c : word) = Some W_6036c.
Proof. vm_refl. Qed.
Lemma D_6036c : decode_any W_6036c = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60370 : bv 32 := 0x0075ce03.
Lemma F_60370 : fetch_word Ubsan.M.loaded_segments (0x60370 : word) = Some W_60370.
Proof. vm_refl. Qed.
Lemma D_60370 : decode_any W_60370 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60374 : bv 32 := 0x00e68023.
Lemma F_60374 : fetch_word Ubsan.M.loaded_segments (0x60374 : word) = Some W_60374.
Proof. vm_refl. Qed.
Lemma D_60374 : decode_any W_60374 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60378 : bv 32 := 0x00f680a3.
Lemma F_60378 : fetch_word Ubsan.M.loaded_segments (0x60378 : word) = Some W_60378.
Proof. vm_refl. Qed.
Lemma D_60378 : decode_any W_60378 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6037c : bv 32 := 0x01068123.
Lemma F_6037c : fetch_word Ubsan.M.loaded_segments (0x6037c : word) = Some W_6037c.
Proof. vm_refl. Qed.
Lemma D_6037c : decode_any W_6037c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60380 : bv 32 := 0x011681a3.
Lemma F_60380 : fetch_word Ubsan.M.loaded_segments (0x60380 : word) = Some W_60380.
Proof. vm_refl. Qed.
Lemma D_60380 : decode_any W_60380 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60384 : bv 32 := 0x0085c703.
Lemma F_60384 : fetch_word Ubsan.M.loaded_segments (0x60384 : word) = Some W_60384.
Proof. vm_refl. Qed.
Lemma D_60384 : decode_any W_60384 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60388 : bv 32 := 0x0095c783.
Lemma F_60388 : fetch_word Ubsan.M.loaded_segments (0x60388 : word) = Some W_60388.
Proof. vm_refl. Qed.
Lemma D_60388 : decode_any W_60388 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6038c : bv 32 := 0x00a5c803.
Lemma F_6038c : fetch_word Ubsan.M.loaded_segments (0x6038c : word) = Some W_6038c.
Proof. vm_refl. Qed.
Lemma D_6038c : decode_any W_6038c = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60390 : bv 32 := 0x00b5c883.
Lemma F_60390 : fetch_word Ubsan.M.loaded_segments (0x60390 : word) = Some W_60390.
Proof. vm_refl. Qed.
Lemma D_60390 : decode_any W_60390 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60394 : bv 32 := 0x00568223.
Lemma F_60394 : fetch_word Ubsan.M.loaded_segments (0x60394 : word) = Some W_60394.
Proof. vm_refl. Qed.
Lemma D_60394 : decode_any W_60394 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60398 : bv 32 := 0x006682a3.
Lemma F_60398 : fetch_word Ubsan.M.loaded_segments (0x60398 : word) = Some W_60398.
Proof. vm_refl. Qed.
Lemma D_60398 : decode_any W_60398 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6039c : bv 32 := 0x00768323.
Lemma F_6039c : fetch_word Ubsan.M.loaded_segments (0x6039c : word) = Some W_6039c.
Proof. vm_refl. Qed.
Lemma D_6039c : decode_any W_6039c = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603a0 : bv 32 := 0x01c683a3.
Lemma F_603a0 : fetch_word Ubsan.M.loaded_segments (0x603a0 : word) = Some W_603a0.
Proof. vm_refl. Qed.
Lemma D_603a0 : decode_any W_603a0 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603a4 : bv 32 := 0x00c5c283.
Lemma F_603a4 : fetch_word Ubsan.M.loaded_segments (0x603a4 : word) = Some W_603a4.
Proof. vm_refl. Qed.
Lemma D_603a4 : decode_any W_603a4 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603a8 : bv 32 := 0x00d5c303.
Lemma F_603a8 : fetch_word Ubsan.M.loaded_segments (0x603a8 : word) = Some W_603a8.
Proof. vm_refl. Qed.
Lemma D_603a8 : decode_any W_603a8 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603ac : bv 32 := 0x00e5c383.
Lemma F_603ac : fetch_word Ubsan.M.loaded_segments (0x603ac : word) = Some W_603ac.
Proof. vm_refl. Qed.
Lemma D_603ac : decode_any W_603ac = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603b0 : bv 32 := 0x00f5ce03.
Lemma F_603b0 : fetch_word Ubsan.M.loaded_segments (0x603b0 : word) = Some W_603b0.
Proof. vm_refl. Qed.
Lemma D_603b0 : decode_any W_603b0 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603b4 : bv 32 := 0x01058593.
Lemma F_603b4 : fetch_word Ubsan.M.loaded_segments (0x603b4 : word) = Some W_603b4.
Proof. vm_refl. Qed.
Lemma D_603b4 : decode_any W_603b4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603b8 : bv 32 := 0x00e68423.
Lemma F_603b8 : fetch_word Ubsan.M.loaded_segments (0x603b8 : word) = Some W_603b8.
Proof. vm_refl. Qed.
Lemma D_603b8 : decode_any W_603b8 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603bc : bv 32 := 0x00f684a3.
Lemma F_603bc : fetch_word Ubsan.M.loaded_segments (0x603bc : word) = Some W_603bc.
Proof. vm_refl. Qed.
Lemma D_603bc : decode_any W_603bc = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603c0 : bv 32 := 0x01068523.
Lemma F_603c0 : fetch_word Ubsan.M.loaded_segments (0x603c0 : word) = Some W_603c0.
Proof. vm_refl. Qed.
Lemma D_603c0 : decode_any W_603c0 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603c4 : bv 32 := 0x011685a3.
Lemma F_603c4 : fetch_word Ubsan.M.loaded_segments (0x603c4 : word) = Some W_603c4.
Proof. vm_refl. Qed.
Lemma D_603c4 : decode_any W_603c4 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603c8 : bv 32 := 0x01068713.
Lemma F_603c8 : fetch_word Ubsan.M.loaded_segments (0x603c8 : word) = Some W_603c8.
Proof. vm_refl. Qed.
Lemma D_603c8 : decode_any W_603c8 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603cc : bv 32 := 0x00568623.
Lemma F_603cc : fetch_word Ubsan.M.loaded_segments (0x603cc : word) = Some W_603cc.
Proof. vm_refl. Qed.
Lemma D_603cc : decode_any W_603cc = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603d0 : bv 32 := 0x006686a3.
Lemma F_603d0 : fetch_word Ubsan.M.loaded_segments (0x603d0 : word) = Some W_603d0.
Proof. vm_refl. Qed.
Lemma D_603d0 : decode_any W_603d0 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603d4 : bv 32 := 0x00768723.
Lemma F_603d4 : fetch_word Ubsan.M.loaded_segments (0x603d4 : word) = Some W_603d4.
Proof. vm_refl. Qed.
Lemma D_603d4 : decode_any W_603d4 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603d8 : bv 32 := 0x01c687a3.
Lemma F_603d8 : fetch_word Ubsan.M.loaded_segments (0x603d8 : word) = Some W_603d8.
Proof. vm_refl. Qed.
Lemma D_603d8 : decode_any W_603d8 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603dc : bv 32 := 0x00070693.
Lemma F_603dc : fetch_word Ubsan.M.loaded_segments (0x603dc : word) = Some W_603dc.
Proof. vm_refl. Qed.
Lemma D_603dc : decode_any W_603dc = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603e0 : bv 32 := 0x00867713.
Lemma F_603e0 : fetch_word Ubsan.M.loaded_segments (0x603e0 : word) = Some W_603e0.
Proof. vm_refl. Qed.
Lemma D_603e0 : decode_any W_603e0 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603e4 : bv 32 := 0xd20706e3.
Lemma F_603e4 : fetch_word Ubsan.M.loaded_segments (0x603e4 : word) = Some W_603e4.
Proof. vm_refl. Qed.
Lemma D_603e4 : decode_any W_603e4 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603e8 : bv 32 := 0x0005c703.
Lemma F_603e8 : fetch_word Ubsan.M.loaded_segments (0x603e8 : word) = Some W_603e8.
Proof. vm_refl. Qed.
Lemma D_603e8 : decode_any W_603e8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603ec : bv 32 := 0x0015c783.
Lemma F_603ec : fetch_word Ubsan.M.loaded_segments (0x603ec : word) = Some W_603ec.
Proof. vm_refl. Qed.
Lemma D_603ec : decode_any W_603ec = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603f0 : bv 32 := 0x0025c803.
Lemma F_603f0 : fetch_word Ubsan.M.loaded_segments (0x603f0 : word) = Some W_603f0.
Proof. vm_refl. Qed.
Lemma D_603f0 : decode_any W_603f0 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603f4 : bv 32 := 0x0035c883.
Lemma F_603f4 : fetch_word Ubsan.M.loaded_segments (0x603f4 : word) = Some W_603f4.
Proof. vm_refl. Qed.
Lemma D_603f4 : decode_any W_603f4 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603f8 : bv 32 := 0x0045c283.
Lemma F_603f8 : fetch_word Ubsan.M.loaded_segments (0x603f8 : word) = Some W_603f8.
Proof. vm_refl. Qed.
Lemma D_603f8 : decode_any W_603f8 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603fc : bv 32 := 0x0055c303.
Lemma F_603fc : fetch_word Ubsan.M.loaded_segments (0x603fc : word) = Some W_603fc.
Proof. vm_refl. Qed.
Lemma D_603fc : decode_any W_603fc = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60400 : bv 32 := 0x0065c383.
Lemma F_60400 : fetch_word Ubsan.M.loaded_segments (0x60400 : word) = Some W_60400.
Proof. vm_refl. Qed.
Lemma D_60400 : decode_any W_60400 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60404 : bv 32 := 0x0075ce03.
Lemma F_60404 : fetch_word Ubsan.M.loaded_segments (0x60404 : word) = Some W_60404.
Proof. vm_refl. Qed.
Lemma D_60404 : decode_any W_60404 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60408 : bv 32 := 0x00858593.
Lemma F_60408 : fetch_word Ubsan.M.loaded_segments (0x60408 : word) = Some W_60408.
Proof. vm_refl. Qed.
Lemma D_60408 : decode_any W_60408 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6040c : bv 32 := 0x00e68023.
Lemma F_6040c : fetch_word Ubsan.M.loaded_segments (0x6040c : word) = Some W_6040c.
Proof. vm_refl. Qed.
Lemma D_6040c : decode_any W_6040c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60410 : bv 32 := 0x00f680a3.
Lemma F_60410 : fetch_word Ubsan.M.loaded_segments (0x60410 : word) = Some W_60410.
Proof. vm_refl. Qed.
Lemma D_60410 : decode_any W_60410 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60414 : bv 32 := 0x01068123.
Lemma F_60414 : fetch_word Ubsan.M.loaded_segments (0x60414 : word) = Some W_60414.
Proof. vm_refl. Qed.
Lemma D_60414 : decode_any W_60414 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60418 : bv 32 := 0x011681a3.
Lemma F_60418 : fetch_word Ubsan.M.loaded_segments (0x60418 : word) = Some W_60418.
Proof. vm_refl. Qed.
Lemma D_60418 : decode_any W_60418 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6041c : bv 32 := 0x00868713.
Lemma F_6041c : fetch_word Ubsan.M.loaded_segments (0x6041c : word) = Some W_6041c.
Proof. vm_refl. Qed.
Lemma D_6041c : decode_any W_6041c = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60420 : bv 32 := 0x00568223.
Lemma F_60420 : fetch_word Ubsan.M.loaded_segments (0x60420 : word) = Some W_60420.
Proof. vm_refl. Qed.
Lemma D_60420 : decode_any W_60420 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60424 : bv 32 := 0x006682a3.
Lemma F_60424 : fetch_word Ubsan.M.loaded_segments (0x60424 : word) = Some W_60424.
Proof. vm_refl. Qed.
Lemma D_60424 : decode_any W_60424 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60428 : bv 32 := 0x00768323.
Lemma F_60428 : fetch_word Ubsan.M.loaded_segments (0x60428 : word) = Some W_60428.
Proof. vm_refl. Qed.
Lemma D_60428 : decode_any W_60428 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6042c : bv 32 := 0x01c683a3.
Lemma F_6042c : fetch_word Ubsan.M.loaded_segments (0x6042c : word) = Some W_6042c.
Proof. vm_refl. Qed.
Lemma D_6042c : decode_any W_6042c = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60430 : bv 32 := 0x00070693.
Lemma F_60430 : fetch_word Ubsan.M.loaded_segments (0x60430 : word) = Some W_60430.
Proof. vm_refl. Qed.
Lemma D_60430 : decode_any W_60430 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60434 : bv 32 := 0x00467713.
Lemma F_60434 : fetch_word Ubsan.M.loaded_segments (0x60434 : word) = Some W_60434.
Proof. vm_refl. Qed.
Lemma D_60434 : decode_any W_60434 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60438 : bv 32 := 0x02070863.
Lemma F_60438 : fetch_word Ubsan.M.loaded_segments (0x60438 : word) = Some W_60438.
Proof. vm_refl. Qed.
Lemma D_60438 : decode_any W_60438 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6043c : bv 32 := 0x0005c703.
Lemma F_6043c : fetch_word Ubsan.M.loaded_segments (0x6043c : word) = Some W_6043c.
Proof. vm_refl. Qed.
Lemma D_6043c : decode_any W_6043c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60440 : bv 32 := 0x0015c783.
Lemma F_60440 : fetch_word Ubsan.M.loaded_segments (0x60440 : word) = Some W_60440.
Proof. vm_refl. Qed.
Lemma D_60440 : decode_any W_60440 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60444 : bv 32 := 0x0025c803.
Lemma F_60444 : fetch_word Ubsan.M.loaded_segments (0x60444 : word) = Some W_60444.
Proof. vm_refl. Qed.
Lemma D_60444 : decode_any W_60444 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60448 : bv 32 := 0x0035c883.
Lemma F_60448 : fetch_word Ubsan.M.loaded_segments (0x60448 : word) = Some W_60448.
Proof. vm_refl. Qed.
Lemma D_60448 : decode_any W_60448 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6044c : bv 32 := 0x00458593.
Lemma F_6044c : fetch_word Ubsan.M.loaded_segments (0x6044c : word) = Some W_6044c.
Proof. vm_refl. Qed.
Lemma D_6044c : decode_any W_6044c = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60450 : bv 32 := 0x00468293.
Lemma F_60450 : fetch_word Ubsan.M.loaded_segments (0x60450 : word) = Some W_60450.
Proof. vm_refl. Qed.
Lemma D_60450 : decode_any W_60450 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60454 : bv 32 := 0x00e68023.
Lemma F_60454 : fetch_word Ubsan.M.loaded_segments (0x60454 : word) = Some W_60454.
Proof. vm_refl. Qed.
Lemma D_60454 : decode_any W_60454 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60458 : bv 32 := 0x00f680a3.
Lemma F_60458 : fetch_word Ubsan.M.loaded_segments (0x60458 : word) = Some W_60458.
Proof. vm_refl. Qed.
Lemma D_60458 : decode_any W_60458 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6045c : bv 32 := 0x01068123.
Lemma F_6045c : fetch_word Ubsan.M.loaded_segments (0x6045c : word) = Some W_6045c.
Proof. vm_refl. Qed.
Lemma D_6045c : decode_any W_6045c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60460 : bv 32 := 0x011681a3.
Lemma F_60460 : fetch_word Ubsan.M.loaded_segments (0x60460 : word) = Some W_60460.
Proof. vm_refl. Qed.
Lemma D_60460 : decode_any W_60460 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60464 : bv 32 := 0x00028693.
Lemma F_60464 : fetch_word Ubsan.M.loaded_segments (0x60464 : word) = Some W_60464.
Proof. vm_refl. Qed.
Lemma D_60464 : decode_any W_60464 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60468 : bv 32 := 0x00267713.
Lemma F_60468 : fetch_word Ubsan.M.loaded_segments (0x60468 : word) = Some W_60468.
Proof. vm_refl. Qed.
Lemma D_60468 : decode_any W_60468 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6046c : bv 32 := 0x00071863.
Lemma F_6046c : fetch_word Ubsan.M.loaded_segments (0x6046c : word) = Some W_6046c.
Proof. vm_refl. Qed.
Lemma D_6046c : decode_any W_6046c = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60470 : bv 32 := 0x00167613.
Lemma F_60470 : fetch_word Ubsan.M.loaded_segments (0x60470 : word) = Some W_60470.
Proof. vm_refl. Qed.
Lemma D_60470 : decode_any W_60470 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60474 : bv 32 := 0x02061663.
Lemma F_60474 : fetch_word Ubsan.M.loaded_segments (0x60474 : word) = Some W_60474.
Proof. vm_refl. Qed.
Lemma D_60474 : decode_any W_60474 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60478 : bv 32 := 0x00008067.
Lemma F_60478 : fetch_word Ubsan.M.loaded_segments (0x60478 : word) = Some W_60478.
Proof. vm_refl. Qed.
Lemma D_60478 : decode_any W_60478 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6047c : bv 32 := 0x0005c703.
Lemma F_6047c : fetch_word Ubsan.M.loaded_segments (0x6047c : word) = Some W_6047c.
Proof. vm_refl. Qed.
Lemma D_6047c : decode_any W_6047c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60480 : bv 32 := 0x0015c783.
Lemma F_60480 : fetch_word Ubsan.M.loaded_segments (0x60480 : word) = Some W_60480.
Proof. vm_refl. Qed.
Lemma D_60480 : decode_any W_60480 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60484 : bv 32 := 0x00258593.
Lemma F_60484 : fetch_word Ubsan.M.loaded_segments (0x60484 : word) = Some W_60484.
Proof. vm_refl. Qed.
Lemma D_60484 : decode_any W_60484 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60488 : bv 32 := 0x00268813.
Lemma F_60488 : fetch_word Ubsan.M.loaded_segments (0x60488 : word) = Some W_60488.
Proof. vm_refl. Qed.
Lemma D_60488 : decode_any W_60488 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6048c : bv 32 := 0x00e68023.
Lemma F_6048c : fetch_word Ubsan.M.loaded_segments (0x6048c : word) = Some W_6048c.
Proof. vm_refl. Qed.
Lemma D_6048c : decode_any W_6048c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60490 : bv 32 := 0x00f680a3.
Lemma F_60490 : fetch_word Ubsan.M.loaded_segments (0x60490 : word) = Some W_60490.
Proof. vm_refl. Qed.
Lemma D_60490 : decode_any W_60490 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60494 : bv 32 := 0x00080693.
Lemma F_60494 : fetch_word Ubsan.M.loaded_segments (0x60494 : word) = Some W_60494.
Proof. vm_refl. Qed.
Lemma D_60494 : decode_any W_60494 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60498 : bv 32 := 0x00167613.
Lemma F_60498 : fetch_word Ubsan.M.loaded_segments (0x60498 : word) = Some W_60498.
Proof. vm_refl. Qed.
Lemma D_60498 : decode_any W_60498 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6049c : bv 32 := 0xfc060ee3.
Lemma F_6049c : fetch_word Ubsan.M.loaded_segments (0x6049c : word) = Some W_6049c.
Proof. vm_refl. Qed.
Lemma D_6049c : decode_any W_6049c = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604a0 : bv 32 := 0x0005c583.
Lemma F_604a0 : fetch_word Ubsan.M.loaded_segments (0x604a0 : word) = Some W_604a0.
Proof. vm_refl. Qed.
Lemma D_604a0 : decode_any W_604a0 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604a4 : bv 32 := 0x00b68023.
Lemma F_604a4 : fetch_word Ubsan.M.loaded_segments (0x604a4 : word) = Some W_604a4.
Proof. vm_refl. Qed.
Lemma D_604a4 : decode_any W_604a4 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604a8 : bv 32 := 0x00008067.
Lemma F_604a8 : fetch_word Ubsan.M.loaded_segments (0x604a8 : word) = Some W_604a8.
Proof. vm_refl. Qed.
Lemma D_604a8 : decode_any W_604a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
