(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_35ea0 : bv 32 := 0x00195593.
Lemma F_35ea0 : fetch_word AsanUbsan.M.loaded_segments (0x35ea0 : word) = Some W_35ea0.
Proof. vm_refl. Qed.
Lemma D_35ea0 : decode_any W_35ea0 = Some (ShiftImm ALU_SRL 11 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35ea4 : bv 32 := 0x55555637.
Lemma F_35ea4 : fetch_word AsanUbsan.M.loaded_segments (0x35ea4 : word) = Some W_35ea4.
Proof. vm_refl. Qed.
Lemma D_35ea4 : decode_any W_35ea4 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35ea8 : bv 32 := 0x33333737.
Lemma F_35ea8 : fetch_word AsanUbsan.M.loaded_segments (0x35ea8 : word) = Some W_35ea8.
Proof. vm_refl. Qed.
Lemma D_35ea8 : decode_any W_35ea8 = Some (Lui 14 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35eac : bv 32 := 0x0f0f17b7.
Lemma F_35eac : fetch_word AsanUbsan.M.loaded_segments (0x35eac : word) = Some W_35eac.
Proof. vm_refl. Qed.
Lemma D_35eac : decode_any W_35eac = Some (Lui 15 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35eb0 : bv 32 := 0x00b965b3.
Lemma F_35eb0 : fetch_word AsanUbsan.M.loaded_segments (0x35eb0 : word) = Some W_35eb0.
Proof. vm_refl. Qed.
Lemma D_35eb0 : decode_any W_35eb0 = Some (Op ALU_OR 11 18 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35eb4 : bv 32 := 0x5556061b.
Lemma F_35eb4 : fetch_word AsanUbsan.M.loaded_segments (0x35eb4 : word) = Some W_35eb4.
Proof. vm_refl. Qed.
Lemma D_35eb4 : decode_any W_35eb4 = Some (OpImm32 12 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35eb8 : bv 32 := 0x3337071b.
Lemma F_35eb8 : fetch_word AsanUbsan.M.loaded_segments (0x35eb8 : word) = Some W_35eb8.
Proof. vm_refl. Qed.
Lemma D_35eb8 : decode_any W_35eb8 = Some (OpImm32 14 14 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35ebc : bv 32 := 0xf0f7879b.
Lemma F_35ebc : fetch_word AsanUbsan.M.loaded_segments (0x35ebc : word) = Some W_35ebc.
Proof. vm_refl. Qed.
Lemma D_35ebc : decode_any W_35ebc = Some (OpImm32 15 15 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35ec0 : bv 32 := 0x0025d813.
Lemma F_35ec0 : fetch_word AsanUbsan.M.loaded_segments (0x35ec0 : word) = Some W_35ec0.
Proof. vm_refl. Qed.
Lemma D_35ec0 : decode_any W_35ec0 = Some (ShiftImm ALU_SRL 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35ec4 : bv 32 := 0x0105e5b3.
Lemma F_35ec4 : fetch_word AsanUbsan.M.loaded_segments (0x35ec4 : word) = Some W_35ec4.
Proof. vm_refl. Qed.
Lemma D_35ec4 : decode_any W_35ec4 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35ec8 : bv 32 := 0x02061813.
Lemma F_35ec8 : fetch_word AsanUbsan.M.loaded_segments (0x35ec8 : word) = Some W_35ec8.
Proof. vm_refl. Qed.
Lemma D_35ec8 : decode_any W_35ec8 = Some (ShiftImm ALU_SLL 16 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35ecc : bv 32 := 0x01060633.
Lemma F_35ecc : fetch_word AsanUbsan.M.loaded_segments (0x35ecc : word) = Some W_35ecc.
Proof. vm_refl. Qed.
Lemma D_35ecc : decode_any W_35ecc = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35ed0 : bv 32 := 0x02071813.
Lemma F_35ed0 : fetch_word AsanUbsan.M.loaded_segments (0x35ed0 : word) = Some W_35ed0.
Proof. vm_refl. Qed.
Lemma D_35ed0 : decode_any W_35ed0 = Some (ShiftImm ALU_SLL 16 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35ed4 : bv 32 := 0x01070733.
Lemma F_35ed4 : fetch_word AsanUbsan.M.loaded_segments (0x35ed4 : word) = Some W_35ed4.
Proof. vm_refl. Qed.
Lemma D_35ed4 : decode_any W_35ed4 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35ed8 : bv 32 := 0x02079813.
Lemma F_35ed8 : fetch_word AsanUbsan.M.loaded_segments (0x35ed8 : word) = Some W_35ed8.
Proof. vm_refl. Qed.
Lemma D_35ed8 : decode_any W_35ed8 = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35edc : bv 32 := 0x010787b3.
Lemma F_35edc : fetch_word AsanUbsan.M.loaded_segments (0x35edc : word) = Some W_35edc.
Proof. vm_refl. Qed.
Lemma D_35edc : decode_any W_35edc = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35ee0 : bv 32 := 0x0045d813.
Lemma F_35ee0 : fetch_word AsanUbsan.M.loaded_segments (0x35ee0 : word) = Some W_35ee0.
Proof. vm_refl. Qed.
Lemma D_35ee0 : decode_any W_35ee0 = Some (ShiftImm ALU_SRL 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35ee4 : bv 32 := 0x0105e5b3.
Lemma F_35ee4 : fetch_word AsanUbsan.M.loaded_segments (0x35ee4 : word) = Some W_35ee4.
Proof. vm_refl. Qed.
Lemma D_35ee4 : decode_any W_35ee4 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35ee8 : bv 32 := 0x0085d813.
Lemma F_35ee8 : fetch_word AsanUbsan.M.loaded_segments (0x35ee8 : word) = Some W_35ee8.
Proof. vm_refl. Qed.
Lemma D_35ee8 : decode_any W_35ee8 = Some (ShiftImm ALU_SRL 16 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35eec : bv 32 := 0x0105e5b3.
Lemma F_35eec : fetch_word AsanUbsan.M.loaded_segments (0x35eec : word) = Some W_35eec.
Proof. vm_refl. Qed.
Lemma D_35eec : decode_any W_35eec = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35ef0 : bv 32 := 0x0105d813.
Lemma F_35ef0 : fetch_word AsanUbsan.M.loaded_segments (0x35ef0 : word) = Some W_35ef0.
Proof. vm_refl. Qed.
Lemma D_35ef0 : decode_any W_35ef0 = Some (ShiftImm ALU_SRL 16 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35ef4 : bv 32 := 0x0105e5b3.
Lemma F_35ef4 : fetch_word AsanUbsan.M.loaded_segments (0x35ef4 : word) = Some W_35ef4.
Proof. vm_refl. Qed.
Lemma D_35ef4 : decode_any W_35ef4 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35ef8 : bv 32 := 0x0205d813.
Lemma F_35ef8 : fetch_word AsanUbsan.M.loaded_segments (0x35ef8 : word) = Some W_35ef8.
Proof. vm_refl. Qed.
Lemma D_35ef8 : decode_any W_35ef8 = Some (ShiftImm ALU_SRL 16 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35efc : bv 32 := 0x0105e5b3.
Lemma F_35efc : fetch_word AsanUbsan.M.loaded_segments (0x35efc : word) = Some W_35efc.
Proof. vm_refl. Qed.
Lemma D_35efc : decode_any W_35efc = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f00 : bv 32 := 0xfff5c593.
Lemma F_35f00 : fetch_word AsanUbsan.M.loaded_segments (0x35f00 : word) = Some W_35f00.
Proof. vm_refl. Qed.
Lemma D_35f00 : decode_any W_35f00 = Some (OpImm ALU_XOR 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f04 : bv 32 := 0x0015d813.
Lemma F_35f04 : fetch_word AsanUbsan.M.loaded_segments (0x35f04 : word) = Some W_35f04.
Proof. vm_refl. Qed.
Lemma D_35f04 : decode_any W_35f04 = Some (ShiftImm ALU_SRL 16 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f08 : bv 32 := 0x00c87633.
Lemma F_35f08 : fetch_word AsanUbsan.M.loaded_segments (0x35f08 : word) = Some W_35f08.
Proof. vm_refl. Qed.
Lemma D_35f08 : decode_any W_35f08 = Some (Op ALU_AND 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f0c : bv 32 := 0x01010837.
Lemma F_35f0c : fetch_word AsanUbsan.M.loaded_segments (0x35f0c : word) = Some W_35f0c.
Proof. vm_refl. Qed.
Lemma D_35f0c : decode_any W_35f0c = Some (Lui 16 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f10 : bv 32 := 0x40c585b3.
Lemma F_35f10 : fetch_word AsanUbsan.M.loaded_segments (0x35f10 : word) = Some W_35f10.
Proof. vm_refl. Qed.
Lemma D_35f10 : decode_any W_35f10 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f14 : bv 32 := 0x0025d613.
Lemma F_35f14 : fetch_word AsanUbsan.M.loaded_segments (0x35f14 : word) = Some W_35f14.
Proof. vm_refl. Qed.
Lemma D_35f14 : decode_any W_35f14 = Some (ShiftImm ALU_SRL 12 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f18 : bv 32 := 0x00e5f5b3.
Lemma F_35f18 : fetch_word AsanUbsan.M.loaded_segments (0x35f18 : word) = Some W_35f18.
Proof. vm_refl. Qed.
Lemma D_35f18 : decode_any W_35f18 = Some (Op ALU_AND 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f1c : bv 32 := 0x00e67633.
Lemma F_35f1c : fetch_word AsanUbsan.M.loaded_segments (0x35f1c : word) = Some W_35f1c.
Proof. vm_refl. Qed.
Lemma D_35f1c : decode_any W_35f1c = Some (Op ALU_AND 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f20 : bv 32 := 0x0304b703.
Lemma F_35f20 : fetch_word AsanUbsan.M.loaded_segments (0x35f20 : word) = Some W_35f20.
Proof. vm_refl. Qed.
Lemma D_35f20 : decode_any W_35f20 = Some (Load SZ8 true 14 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f24 : bv 32 := 0x1018081b.
Lemma F_35f24 : fetch_word AsanUbsan.M.loaded_segments (0x35f24 : word) = Some W_35f24.
Proof. vm_refl. Qed.
Lemma D_35f24 : decode_any W_35f24 = Some (OpImm32 16 16 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f28 : bv 32 := 0x00c585b3.
Lemma F_35f28 : fetch_word AsanUbsan.M.loaded_segments (0x35f28 : word) = Some W_35f28.
Proof. vm_refl. Qed.
Lemma D_35f28 : decode_any W_35f28 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f2c : bv 32 := 0x0045d613.
Lemma F_35f2c : fetch_word AsanUbsan.M.loaded_segments (0x35f2c : word) = Some W_35f2c.
Proof. vm_refl. Qed.
Lemma D_35f2c : decode_any W_35f2c = Some (ShiftImm ALU_SRL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f30 : bv 32 := 0x00c585b3.
Lemma F_35f30 : fetch_word AsanUbsan.M.loaded_segments (0x35f30 : word) = Some W_35f30.
Proof. vm_refl. Qed.
Lemma D_35f30 : decode_any W_35f30 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f34 : bv 32 := 0x02081613.
Lemma F_35f34 : fetch_word AsanUbsan.M.loaded_segments (0x35f34 : word) = Some W_35f34.
Proof. vm_refl. Qed.
Lemma D_35f34 : decode_any W_35f34 = Some (ShiftImm ALU_SLL 12 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f38 : bv 32 := 0x00f5f5b3.
Lemma F_35f38 : fetch_word AsanUbsan.M.loaded_segments (0x35f38 : word) = Some W_35f38.
Proof. vm_refl. Qed.
Lemma D_35f38 : decode_any W_35f38 = Some (Op ALU_AND 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f3c : bv 32 := 0x00c80633.
Lemma F_35f3c : fetch_word AsanUbsan.M.loaded_segments (0x35f3c : word) = Some W_35f3c.
Proof. vm_refl. Qed.
Lemma D_35f3c : decode_any W_35f3c = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f40 : bv 32 := 0x02c585b3.
Lemma F_35f40 : fetch_word AsanUbsan.M.loaded_segments (0x35f40 : word) = Some W_35f40.
Proof. vm_refl. Qed.
Lemma D_35f40 : decode_any W_35f40 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f44 : bv 32 := 0x0385d993.
Lemma F_35f44 : fetch_word AsanUbsan.M.loaded_segments (0x35f44 : word) = Some W_35f44.
Proof. vm_refl. Qed.
Lemma D_35f44 : decode_any W_35f44 = Some (ShiftImm ALU_SRL 19 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f48 : bv 32 := 0x1ce68c63.
Lemma F_35f48 : fetch_word AsanUbsan.M.loaded_segments (0x35f48 : word) = Some W_35f48.
Proof. vm_refl. Qed.
Lemma D_35f48 : decode_any W_35f48 = Some (Branch BC_EQ 13 14 472, 4%Z).
Proof. vm_refl. Qed.
