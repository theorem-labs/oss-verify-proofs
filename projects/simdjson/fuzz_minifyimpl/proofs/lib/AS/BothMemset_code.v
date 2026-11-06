(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
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
From OSSVerify.simdjson.fuzz_minifyimpl.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_166260 : bv 32 := 0x0e060a63.
Lemma F_166260 : fetch_word AsanUbsan.M.loaded_segments (0x1661dc : word) = Some W_166260.
Proof. vm_refl. Qed.
Lemma D_166260 : decode_any W_166260 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166264 : bv 32 := 0x00b50023.
Lemma F_166264 : fetch_word AsanUbsan.M.loaded_segments (0x1661e0 : word) = Some W_166264.
Proof. vm_refl. Qed.
Lemma D_166264 : decode_any W_166264 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166268 : bv 32 := 0x00c506b3.
Lemma F_166268 : fetch_word AsanUbsan.M.loaded_segments (0x1661e4 : word) = Some W_166268.
Proof. vm_refl. Qed.
Lemma D_166268 : decode_any W_166268 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16626c : bv 32 := 0x00300713.
Lemma F_16626c : fetch_word AsanUbsan.M.loaded_segments (0x1661e8 : word) = Some W_16626c.
Proof. vm_refl. Qed.
Lemma D_16626c : decode_any W_16626c = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166270 : bv 32 := 0xfeb68fa3.
Lemma F_166270 : fetch_word AsanUbsan.M.loaded_segments (0x1661ec : word) = Some W_166270.
Proof. vm_refl. Qed.
Lemma D_166270 : decode_any W_166270 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166274 : bv 32 := 0x0ee66063.
Lemma F_166274 : fetch_word AsanUbsan.M.loaded_segments (0x1661f0 : word) = Some W_166274.
Proof. vm_refl. Qed.
Lemma D_166274 : decode_any W_166274 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166278 : bv 32 := 0x00b500a3.
Lemma F_166278 : fetch_word AsanUbsan.M.loaded_segments (0x1661f4 : word) = Some W_166278.
Proof. vm_refl. Qed.
Lemma D_166278 : decode_any W_166278 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16627c : bv 32 := 0x00b50123.
Lemma F_16627c : fetch_word AsanUbsan.M.loaded_segments (0x1661f8 : word) = Some W_16627c.
Proof. vm_refl. Qed.
Lemma D_16627c : decode_any W_16627c = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166280 : bv 32 := 0x00700713.
Lemma F_166280 : fetch_word AsanUbsan.M.loaded_segments (0x1661fc : word) = Some W_166280.
Proof. vm_refl. Qed.
Lemma D_166280 : decode_any W_166280 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166284 : bv 32 := 0xfeb68ea3.
Lemma F_166284 : fetch_word AsanUbsan.M.loaded_segments (0x166200 : word) = Some W_166284.
Proof. vm_refl. Qed.
Lemma D_166284 : decode_any W_166284 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166288 : bv 32 := 0xfeb68f23.
Lemma F_166288 : fetch_word AsanUbsan.M.loaded_segments (0x166204 : word) = Some W_166288.
Proof. vm_refl. Qed.
Lemma D_166288 : decode_any W_166288 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16628c : bv 32 := 0x0ce66463.
Lemma F_16628c : fetch_word AsanUbsan.M.loaded_segments (0x166208 : word) = Some W_16628c.
Proof. vm_refl. Qed.
Lemma D_16628c : decode_any W_16628c = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166290 : bv 32 := 0x00b501a3.
Lemma F_166290 : fetch_word AsanUbsan.M.loaded_segments (0x16620c : word) = Some W_166290.
Proof. vm_refl. Qed.
Lemma D_166290 : decode_any W_166290 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166294 : bv 32 := 0x00900793.
Lemma F_166294 : fetch_word AsanUbsan.M.loaded_segments (0x166210 : word) = Some W_166294.
Proof. vm_refl. Qed.
Lemma D_166294 : decode_any W_166294 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166298 : bv 32 := 0xfeb68e23.
Lemma F_166298 : fetch_word AsanUbsan.M.loaded_segments (0x166214 : word) = Some W_166298.
Proof. vm_refl. Qed.
Lemma D_166298 : decode_any W_166298 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16629c : bv 32 := 0x0af66c63.
Lemma F_16629c : fetch_word AsanUbsan.M.loaded_segments (0x166218 : word) = Some W_16629c.
Proof. vm_refl. Qed.
Lemma D_16629c : decode_any W_16629c = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662a0 : bv 32 := 0x40a006bb.
Lemma F_1662a0 : fetch_word AsanUbsan.M.loaded_segments (0x16621c : word) = Some W_1662a0.
Proof. vm_refl. Qed.
Lemma D_1662a0 : decode_any W_1662a0 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662a4 : bv 32 := 0x03859813.
Lemma F_1662a4 : fetch_word AsanUbsan.M.loaded_segments (0x166220 : word) = Some W_1662a4.
Proof. vm_refl. Qed.
Lemma D_1662a4 : decode_any W_1662a4 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662a8 : bv 32 := 0x101015b7.
Lemma F_1662a8 : fetch_word AsanUbsan.M.loaded_segments (0x166224 : word) = Some W_1662a8.
Proof. vm_refl. Qed.
Lemma D_1662a8 : decode_any W_1662a8 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662ac : bv 32 := 0x0036f693.
Lemma F_1662ac : fetch_word AsanUbsan.M.loaded_segments (0x166228 : word) = Some W_1662ac.
Proof. vm_refl. Qed.
Lemma D_1662ac : decode_any W_1662ac = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662b0 : bv 32 := 0x00459713.
Lemma F_1662b0 : fetch_word AsanUbsan.M.loaded_segments (0x16622c : word) = Some W_1662b0.
Proof. vm_refl. Qed.
Lemma D_1662b0 : decode_any W_1662b0 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662b4 : bv 32 := 0x40d60633.
Lemma F_1662b4 : fetch_word AsanUbsan.M.loaded_segments (0x166230 : word) = Some W_1662b4.
Proof. vm_refl. Qed.
Lemma D_1662b4 : decode_any W_1662b4 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662b8 : bv 32 := 0x00d505b3.
Lemma F_1662b8 : fetch_word AsanUbsan.M.loaded_segments (0x166234 : word) = Some W_1662b8.
Proof. vm_refl. Qed.
Lemma D_1662b8 : decode_any W_1662b8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662bc : bv 32 := 0x10070693.
Lemma F_1662bc : fetch_word AsanUbsan.M.loaded_segments (0x166238 : word) = Some W_1662bc.
Proof. vm_refl. Qed.
Lemma D_1662bc : decode_any W_1662bc = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662c0 : bv 32 := 0xffc67713.
Lemma F_1662c0 : fetch_word AsanUbsan.M.loaded_segments (0x16623c : word) = Some W_1662c0.
Proof. vm_refl. Qed.
Lemma D_1662c0 : decode_any W_1662c0 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662c4 : bv 32 := 0x02d83633.
Lemma F_1662c4 : fetch_word AsanUbsan.M.loaded_segments (0x166240 : word) = Some W_1662c4.
Proof. vm_refl. Qed.
Lemma D_1662c4 : decode_any W_1662c4 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662c8 : bv 32 := 0x00c5a023.
Lemma F_1662c8 : fetch_word AsanUbsan.M.loaded_segments (0x166244 : word) = Some W_1662c8.
Proof. vm_refl. Qed.
Lemma D_1662c8 : decode_any W_1662c8 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662cc : bv 32 := 0x00e586b3.
Lemma F_1662cc : fetch_word AsanUbsan.M.loaded_segments (0x166248 : word) = Some W_1662cc.
Proof. vm_refl. Qed.
Lemma D_1662cc : decode_any W_1662cc = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662d0 : bv 32 := 0xfec6ae23.
Lemma F_1662d0 : fetch_word AsanUbsan.M.loaded_segments (0x16624c : word) = Some W_1662d0.
Proof. vm_refl. Qed.
Lemma D_1662d0 : decode_any W_1662d0 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662d4 : bv 32 := 0x08f76063.
Lemma F_1662d4 : fetch_word AsanUbsan.M.loaded_segments (0x166250 : word) = Some W_1662d4.
Proof. vm_refl. Qed.
Lemma D_1662d4 : decode_any W_1662d4 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662d8 : bv 32 := 0x00c5a223.
Lemma F_1662d8 : fetch_word AsanUbsan.M.loaded_segments (0x166254 : word) = Some W_1662d8.
Proof. vm_refl. Qed.
Lemma D_1662d8 : decode_any W_1662d8 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662dc : bv 32 := 0x00c5a423.
Lemma F_1662dc : fetch_word AsanUbsan.M.loaded_segments (0x166258 : word) = Some W_1662dc.
Proof. vm_refl. Qed.
Lemma D_1662dc : decode_any W_1662dc = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662e0 : bv 32 := 0x01900793.
Lemma F_1662e0 : fetch_word AsanUbsan.M.loaded_segments (0x16625c : word) = Some W_1662e0.
Proof. vm_refl. Qed.
Lemma D_1662e0 : decode_any W_1662e0 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662e4 : bv 32 := 0xfec6aa23.
Lemma F_1662e4 : fetch_word AsanUbsan.M.loaded_segments (0x166260 : word) = Some W_1662e4.
Proof. vm_refl. Qed.
Lemma D_1662e4 : decode_any W_1662e4 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662e8 : bv 32 := 0xfec6ac23.
Lemma F_1662e8 : fetch_word AsanUbsan.M.loaded_segments (0x166264 : word) = Some W_1662e8.
Proof. vm_refl. Qed.
Lemma D_1662e8 : decode_any W_1662e8 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662ec : bv 32 := 0x06f76463.
Lemma F_1662ec : fetch_word AsanUbsan.M.loaded_segments (0x166268 : word) = Some W_1662ec.
Proof. vm_refl. Qed.
Lemma D_1662ec : decode_any W_1662ec = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662f0 : bv 32 := 0x00c5a623.
Lemma F_1662f0 : fetch_word AsanUbsan.M.loaded_segments (0x16626c : word) = Some W_1662f0.
Proof. vm_refl. Qed.
Lemma D_1662f0 : decode_any W_1662f0 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662f4 : bv 32 := 0x00c5a823.
Lemma F_1662f4 : fetch_word AsanUbsan.M.loaded_segments (0x166270 : word) = Some W_1662f4.
Proof. vm_refl. Qed.
Lemma D_1662f4 : decode_any W_1662f4 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662f8 : bv 32 := 0x00c5aa23.
Lemma F_1662f8 : fetch_word AsanUbsan.M.loaded_segments (0x166274 : word) = Some W_1662f8.
Proof. vm_refl. Qed.
Lemma D_1662f8 : decode_any W_1662f8 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662fc : bv 32 := 0x00c5ac23.
Lemma F_1662fc : fetch_word AsanUbsan.M.loaded_segments (0x166278 : word) = Some W_1662fc.
Proof. vm_refl. Qed.
Lemma D_1662fc : decode_any W_1662fc = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166300 : bv 32 := 0x0045f793.
Lemma F_166300 : fetch_word AsanUbsan.M.loaded_segments (0x16627c : word) = Some W_166300.
Proof. vm_refl. Qed.
Lemma D_166300 : decode_any W_166300 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166304 : bv 32 := 0x02000813.
Lemma F_166304 : fetch_word AsanUbsan.M.loaded_segments (0x166280 : word) = Some W_166304.
Proof. vm_refl. Qed.
Lemma D_166304 : decode_any W_166304 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166308 : bv 32 := 0x01878793.
Lemma F_166308 : fetch_word AsanUbsan.M.loaded_segments (0x166284 : word) = Some W_166308.
Proof. vm_refl. Qed.
Lemma D_166308 : decode_any W_166308 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16630c : bv 32 := 0x40f70733.
Lemma F_16630c : fetch_word AsanUbsan.M.loaded_segments (0x166288 : word) = Some W_16630c.
Proof. vm_refl. Qed.
Lemma D_16630c : decode_any W_16630c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166310 : bv 32 := 0xfec6a223.
Lemma F_166310 : fetch_word AsanUbsan.M.loaded_segments (0x16628c : word) = Some W_166310.
Proof. vm_refl. Qed.
Lemma D_166310 : decode_any W_166310 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166314 : bv 32 := 0xfec6a423.
Lemma F_166314 : fetch_word AsanUbsan.M.loaded_segments (0x166290 : word) = Some W_166314.
Proof. vm_refl. Qed.
Lemma D_166314 : decode_any W_166314 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166318 : bv 32 := 0xfec6a623.
Lemma F_166318 : fetch_word AsanUbsan.M.loaded_segments (0x166294 : word) = Some W_166318.
Proof. vm_refl. Qed.
Lemma D_166318 : decode_any W_166318 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16631c : bv 32 := 0xfec6a823.
Lemma F_16631c : fetch_word AsanUbsan.M.loaded_segments (0x166298 : word) = Some W_16631c.
Proof. vm_refl. Qed.
Lemma D_16631c : decode_any W_16631c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166320 : bv 32 := 0x03076a63.
Lemma F_166320 : fetch_word AsanUbsan.M.loaded_segments (0x16629c : word) = Some W_166320.
Proof. vm_refl. Qed.
Lemma D_166320 : decode_any W_166320 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166324 : bv 32 := 0x02061613.
Lemma F_166324 : fetch_word AsanUbsan.M.loaded_segments (0x1662a0 : word) = Some W_166324.
Proof. vm_refl. Qed.
Lemma D_166324 : decode_any W_166324 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166328 : bv 32 := 0x00f585b3.
Lemma F_166328 : fetch_word AsanUbsan.M.loaded_segments (0x1662a4 : word) = Some W_166328.
Proof. vm_refl. Qed.
Lemma D_166328 : decode_any W_166328 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16632c : bv 32 := 0x02065693.
Lemma F_16632c : fetch_word AsanUbsan.M.loaded_segments (0x1662a8 : word) = Some W_16632c.
Proof. vm_refl. Qed.
Lemma D_16632c : decode_any W_16632c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166330 : bv 32 := 0x00d66633.
Lemma F_166330 : fetch_word AsanUbsan.M.loaded_segments (0x1662ac : word) = Some W_166330.
Proof. vm_refl. Qed.
Lemma D_166330 : decode_any W_166330 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166334 : bv 32 := 0x01f00693.
Lemma F_166334 : fetch_word AsanUbsan.M.loaded_segments (0x1662b0 : word) = Some W_166334.
Proof. vm_refl. Qed.
Lemma D_166334 : decode_any W_166334 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166338 : bv 32 := 0x00c5b023.
Lemma F_166338 : fetch_word AsanUbsan.M.loaded_segments (0x1662b4 : word) = Some W_166338.
Proof. vm_refl. Qed.
Lemma D_166338 : decode_any W_166338 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16633c : bv 32 := 0x00c5b423.
Lemma F_16633c : fetch_word AsanUbsan.M.loaded_segments (0x1662b8 : word) = Some W_16633c.
Proof. vm_refl. Qed.
Lemma D_16633c : decode_any W_16633c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166340 : bv 32 := 0x00c5b823.
Lemma F_166340 : fetch_word AsanUbsan.M.loaded_segments (0x1662bc : word) = Some W_166340.
Proof. vm_refl. Qed.
Lemma D_166340 : decode_any W_166340 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166344 : bv 32 := 0x00c5bc23.
Lemma F_166344 : fetch_word AsanUbsan.M.loaded_segments (0x1662c0 : word) = Some W_166344.
Proof. vm_refl. Qed.
Lemma D_166344 : decode_any W_166344 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166348 : bv 32 := 0xfe070713.
Lemma F_166348 : fetch_word AsanUbsan.M.loaded_segments (0x1662c4 : word) = Some W_166348.
Proof. vm_refl. Qed.
Lemma D_166348 : decode_any W_166348 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16634c : bv 32 := 0x02058593.
Lemma F_16634c : fetch_word AsanUbsan.M.loaded_segments (0x1662c8 : word) = Some W_16634c.
Proof. vm_refl. Qed.
Lemma D_16634c : decode_any W_16634c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166350 : bv 32 := 0xfee6e4e3.
Lemma F_166350 : fetch_word AsanUbsan.M.loaded_segments (0x1662cc : word) = Some W_166350.
Proof. vm_refl. Qed.
Lemma D_166350 : decode_any W_166350 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166354 : bv 32 := 0x00008067.
Lemma F_166354 : fetch_word AsanUbsan.M.loaded_segments (0x1662d0 : word) = Some W_166354.
Proof. vm_refl. Qed.
Lemma D_166354 : decode_any W_166354 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x1661dc%Z.
Definition Fo_000 := F_166260.
Definition Do_000 := D_166260.
Definition Fo_004 := F_166264.
Definition Do_004 := D_166264.
Definition Fo_008 := F_166268.
Definition Do_008 := D_166268.
Definition Fo_00c := F_16626c.
Definition Do_00c := D_16626c.
Definition Fo_010 := F_166270.
Definition Do_010 := D_166270.
Definition Fo_014 := F_166274.
Definition Do_014 := D_166274.
Definition Fo_018 := F_166278.
Definition Do_018 := D_166278.
Definition Fo_01c := F_16627c.
Definition Do_01c := D_16627c.
Definition Fo_020 := F_166280.
Definition Do_020 := D_166280.
Definition Fo_024 := F_166284.
Definition Do_024 := D_166284.
Definition Fo_028 := F_166288.
Definition Do_028 := D_166288.
Definition Fo_02c := F_16628c.
Definition Do_02c := D_16628c.
Definition Fo_030 := F_166290.
Definition Do_030 := D_166290.
Definition Fo_034 := F_166294.
Definition Do_034 := D_166294.
Definition Fo_038 := F_166298.
Definition Do_038 := D_166298.
Definition Fo_03c := F_16629c.
Definition Do_03c := D_16629c.
Definition Fo_040 := F_1662a0.
Definition Do_040 := D_1662a0.
Definition Fo_044 := F_1662a4.
Definition Do_044 := D_1662a4.
Definition Fo_048 := F_1662a8.
Definition Do_048 := D_1662a8.
Definition Fo_04c := F_1662ac.
Definition Do_04c := D_1662ac.
Definition Fo_050 := F_1662b0.
Definition Do_050 := D_1662b0.
Definition Fo_054 := F_1662b4.
Definition Do_054 := D_1662b4.
Definition Fo_058 := F_1662b8.
Definition Do_058 := D_1662b8.
Definition Fo_05c := F_1662bc.
Definition Do_05c := D_1662bc.
Definition Fo_060 := F_1662c0.
Definition Do_060 := D_1662c0.
Definition Fo_064 := F_1662c4.
Definition Do_064 := D_1662c4.
Definition Fo_068 := F_1662c8.
Definition Do_068 := D_1662c8.
Definition Fo_06c := F_1662cc.
Definition Do_06c := D_1662cc.
Definition Fo_070 := F_1662d0.
Definition Do_070 := D_1662d0.
Definition Fo_074 := F_1662d4.
Definition Do_074 := D_1662d4.
Definition Fo_078 := F_1662d8.
Definition Do_078 := D_1662d8.
Definition Fo_07c := F_1662dc.
Definition Do_07c := D_1662dc.
Definition Fo_080 := F_1662e0.
Definition Do_080 := D_1662e0.
Definition Fo_084 := F_1662e4.
Definition Do_084 := D_1662e4.
Definition Fo_088 := F_1662e8.
Definition Do_088 := D_1662e8.
Definition Fo_08c := F_1662ec.
Definition Do_08c := D_1662ec.
Definition Fo_090 := F_1662f0.
Definition Do_090 := D_1662f0.
Definition Fo_094 := F_1662f4.
Definition Do_094 := D_1662f4.
Definition Fo_098 := F_1662f8.
Definition Do_098 := D_1662f8.
Definition Fo_09c := F_1662fc.
Definition Do_09c := D_1662fc.
Definition Fo_0a0 := F_166300.
Definition Do_0a0 := D_166300.
Definition Fo_0a4 := F_166304.
Definition Do_0a4 := D_166304.
Definition Fo_0a8 := F_166308.
Definition Do_0a8 := D_166308.
Definition Fo_0ac := F_16630c.
Definition Do_0ac := D_16630c.
Definition Fo_0b0 := F_166310.
Definition Do_0b0 := D_166310.
Definition Fo_0b4 := F_166314.
Definition Do_0b4 := D_166314.
Definition Fo_0b8 := F_166318.
Definition Do_0b8 := D_166318.
Definition Fo_0bc := F_16631c.
Definition Do_0bc := D_16631c.
Definition Fo_0c0 := F_166320.
Definition Do_0c0 := D_166320.
Definition Fo_0c4 := F_166324.
Definition Do_0c4 := D_166324.
Definition Fo_0c8 := F_166328.
Definition Do_0c8 := D_166328.
Definition Fo_0cc := F_16632c.
Definition Do_0cc := D_16632c.
Definition Fo_0d0 := F_166330.
Definition Do_0d0 := D_166330.
Definition Fo_0d4 := F_166334.
Definition Do_0d4 := D_166334.
Definition Fo_0d8 := F_166338.
Definition Do_0d8 := D_166338.
Definition Fo_0dc := F_16633c.
Definition Do_0dc := D_16633c.
Definition Fo_0e0 := F_166340.
Definition Do_0e0 := D_166340.
Definition Fo_0e4 := F_166344.
Definition Do_0e4 := D_166344.
Definition Fo_0e8 := F_166348.
Definition Do_0e8 := D_166348.
Definition Fo_0ec := F_16634c.
Definition Do_0ec := D_16634c.
Definition Fo_0f0 := F_166350.
Definition Do_0f0 := D_166350.
Definition Fo_0f4 := F_166354.
Definition Do_0f4 := D_166354.
