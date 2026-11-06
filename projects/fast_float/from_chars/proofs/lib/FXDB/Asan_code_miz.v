(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_73964 : bv 32 := 0xff010113.
Lemma F_73964 : fetch_word AsanUbsan.M.loaded_segments (0x73964 : word) = Some W_73964.
Proof. vm_refl. Qed.
Lemma D_73964 : decode_any W_73964 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73968 : bv 32 := 0x00113423.
Lemma F_73968 : fetch_word AsanUbsan.M.loaded_segments (0x73968 : word) = Some W_73968.
Proof. vm_refl. Qed.
Lemma D_73968 : decode_any W_73968 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7396c : bv 32 := 0x00058693.
Lemma F_7396c : fetch_word AsanUbsan.M.loaded_segments (0x7396c : word) = Some W_7396c.
Proof. vm_refl. Qed.
Lemma D_7396c : decode_any W_7396c = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73970 : bv 32 := 0x00100713.
Lemma F_73970 : fetch_word AsanUbsan.M.loaded_segments (0x73970 : word) = Some W_73970.
Proof. vm_refl. Qed.
Lemma D_73970 : decode_any W_73970 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73974 : bv 32 := 0x02871713.
Lemma F_73974 : fetch_word AsanUbsan.M.loaded_segments (0x73974 : word) = Some W_73974.
Proof. vm_refl. Qed.
Lemma D_73974 : decode_any W_73974 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73978 : bv 32 := 0x00170593.
Lemma F_73978 : fetch_word AsanUbsan.M.loaded_segments (0x73978 : word) = Some W_73978.
Proof. vm_refl. Qed.
Lemma D_73978 : decode_any W_73978 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7397c : bv 32 := 0x08b6f263.
Lemma F_7397c : fetch_word AsanUbsan.M.loaded_segments (0x7397c : word) = Some W_7397c.
Proof. vm_refl. Qed.
Lemma D_7397c : decode_any W_7397c = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73980 : bv 32 := 0x00000593.
Lemma F_73980 : fetch_word AsanUbsan.M.loaded_segments (0x73980 : word) = Some W_73980.
Proof. vm_refl. Qed.
Lemma D_73980 : decode_any W_73980 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73984 : bv 32 := 0x00d50733.
Lemma F_73984 : fetch_word AsanUbsan.M.loaded_segments (0x73984 : word) = Some W_73984.
Proof. vm_refl. Qed.
Lemma D_73984 : decode_any W_73984 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73988 : bv 32 := 0x00750793.
Lemma F_73988 : fetch_word AsanUbsan.M.loaded_segments (0x73988 : word) = Some W_73988.
Proof. vm_refl. Qed.
Lemma D_73988 : decode_any W_73988 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7398c : bv 32 := 0xff87f793.
Lemma F_7398c : fetch_word AsanUbsan.M.loaded_segments (0x7398c : word) = Some W_7398c.
Proof. vm_refl. Qed.
Lemma D_7398c : decode_any W_7398c = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73990 : bv 32 := 0xff877613.
Lemma F_73990 : fetch_word AsanUbsan.M.loaded_segments (0x73990 : word) = Some W_73990.
Proof. vm_refl. Qed.
Lemma D_73990 : decode_any W_73990 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73994 : bv 32 := 0x02f57463.
Lemma F_73994 : fetch_word AsanUbsan.M.loaded_segments (0x73994 : word) = Some W_73994.
Proof. vm_refl. Qed.
Lemma D_73994 : decode_any W_73994 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73998 : bv 32 := 0x02068263.
Lemma F_73998 : fetch_word AsanUbsan.M.loaded_segments (0x73998 : word) = Some W_73998.
Proof. vm_refl. Qed.
Lemma D_73998 : decode_any W_73998 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7399c : bv 32 := 0x00000593.
Lemma F_7399c : fetch_word AsanUbsan.M.loaded_segments (0x7399c : word) = Some W_7399c.
Proof. vm_refl. Qed.
Lemma D_7399c : decode_any W_7399c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739a0 : bv 32 := 0x00150693.
Lemma F_739a0 : fetch_word AsanUbsan.M.loaded_segments (0x739a0 : word) = Some W_739a0.
Proof. vm_refl. Qed.
Lemma D_739a0 : decode_any W_739a0 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739a4 : bv 32 := 0x00068813.
Lemma F_739a4 : fetch_word AsanUbsan.M.loaded_segments (0x739a4 : word) = Some W_739a4.
Proof. vm_refl. Qed.
Lemma D_739a4 : decode_any W_739a4 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739a8 : bv 32 := 0xfff6c683.
Lemma F_739a8 : fetch_word AsanUbsan.M.loaded_segments (0x739a8 : word) = Some W_739a8.
Proof. vm_refl. Qed.
Lemma D_739a8 : decode_any W_739a8 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739ac : bv 32 := 0x00d5e5b3.
Lemma F_739ac : fetch_word AsanUbsan.M.loaded_segments (0x739ac : word) = Some W_739ac.
Proof. vm_refl. Qed.
Lemma D_739ac : decode_any W_739ac = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739b0 : bv 32 := 0x00f87663.
Lemma F_739b0 : fetch_word AsanUbsan.M.loaded_segments (0x739b0 : word) = Some W_739b0.
Proof. vm_refl. Qed.
Lemma D_739b0 : decode_any W_739b0 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739b4 : bv 32 := 0x00180693.
Lemma F_739b4 : fetch_word AsanUbsan.M.loaded_segments (0x739b4 : word) = Some W_739b4.
Proof. vm_refl. Qed.
Lemma D_739b4 : decode_any W_739b4 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739b8 : bv 32 := 0xfee866e3.
Lemma F_739b8 : fetch_word AsanUbsan.M.loaded_segments (0x739b8 : word) = Some W_739b8.
Proof. vm_refl. Qed.
Lemma D_739b8 : decode_any W_739b8 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739bc : bv 32 := 0x00c7fa63.
Lemma F_739bc : fetch_word AsanUbsan.M.loaded_segments (0x739bc : word) = Some W_739bc.
Proof. vm_refl. Qed.
Lemma D_739bc : decode_any W_739bc = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739c0 : bv 32 := 0x0007b683.
Lemma F_739c0 : fetch_word AsanUbsan.M.loaded_segments (0x739c0 : word) = Some W_739c0.
Proof. vm_refl. Qed.
Lemma D_739c0 : decode_any W_739c0 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739c4 : bv 32 := 0x00878793.
Lemma F_739c4 : fetch_word AsanUbsan.M.loaded_segments (0x739c4 : word) = Some W_739c4.
Proof. vm_refl. Qed.
Lemma D_739c4 : decode_any W_739c4 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739c8 : bv 32 := 0x00b6e5b3.
Lemma F_739c8 : fetch_word AsanUbsan.M.loaded_segments (0x739c8 : word) = Some W_739c8.
Proof. vm_refl. Qed.
Lemma D_739c8 : decode_any W_739c8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739cc : bv 32 := 0xfec7eae3.
Lemma F_739cc : fetch_word AsanUbsan.M.loaded_segments (0x739cc : word) = Some W_739cc.
Proof. vm_refl. Qed.
Lemma D_739cc : decode_any W_739cc = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739d0 : bv 32 := 0x02a66063.
Lemma F_739d0 : fetch_word AsanUbsan.M.loaded_segments (0x739d0 : word) = Some W_739d0.
Proof. vm_refl. Qed.
Lemma D_739d0 : decode_any W_739d0 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739d4 : bv 32 := 0x00e67e63.
Lemma F_739d4 : fetch_word AsanUbsan.M.loaded_segments (0x739d4 : word) = Some W_739d4.
Proof. vm_refl. Qed.
Lemma D_739d4 : decode_any W_739d4 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739d8 : bv 32 := 0x40c70733.
Lemma F_739d8 : fetch_word AsanUbsan.M.loaded_segments (0x739d8 : word) = Some W_739d8.
Proof. vm_refl. Qed.
Lemma D_739d8 : decode_any W_739d8 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739dc : bv 32 := 0x00064503.
Lemma F_739dc : fetch_word AsanUbsan.M.loaded_segments (0x739dc : word) = Some W_739dc.
Proof. vm_refl. Qed.
Lemma D_739dc : decode_any W_739dc = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739e0 : bv 32 := 0xfff70713.
Lemma F_739e0 : fetch_word AsanUbsan.M.loaded_segments (0x739e0 : word) = Some W_739e0.
Proof. vm_refl. Qed.
Lemma D_739e0 : decode_any W_739e0 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739e4 : bv 32 := 0x00a5e5b3.
Lemma F_739e4 : fetch_word AsanUbsan.M.loaded_segments (0x739e4 : word) = Some W_739e4.
Proof. vm_refl. Qed.
Lemma D_739e4 : decode_any W_739e4 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739e8 : bv 32 := 0x00160613.
Lemma F_739e8 : fetch_word AsanUbsan.M.loaded_segments (0x739e8 : word) = Some W_739e8.
Proof. vm_refl. Qed.
Lemma D_739e8 : decode_any W_739e8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739ec : bv 32 := 0xfe0718e3.
Lemma F_739ec : fetch_word AsanUbsan.M.loaded_segments (0x739ec : word) = Some W_739ec.
Proof. vm_refl. Qed.
Lemma D_739ec : decode_any W_739ec = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739f0 : bv 32 := 0x0015b513.
Lemma F_739f0 : fetch_word AsanUbsan.M.loaded_segments (0x739f0 : word) = Some W_739f0.
Proof. vm_refl. Qed.
Lemma D_739f0 : decode_any W_739f0 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739f4 : bv 32 := 0x00813083.
Lemma F_739f4 : fetch_word AsanUbsan.M.loaded_segments (0x739f4 : word) = Some W_739f4.
Proof. vm_refl. Qed.
Lemma D_739f4 : decode_any W_739f4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739f8 : bv 32 := 0x01010113.
Lemma F_739f8 : fetch_word AsanUbsan.M.loaded_segments (0x739f8 : word) = Some W_739f8.
Proof. vm_refl. Qed.
Lemma D_739f8 : decode_any W_739f8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_739fc : bv 32 := 0x00008067.
Lemma F_739fc : fetch_word AsanUbsan.M.loaded_segments (0x739fc : word) = Some W_739fc.
Proof. vm_refl. Qed.
Lemma D_739fc : decode_any W_739fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
