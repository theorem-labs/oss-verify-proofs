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
Definition W_54870 : bv 32 := 0x00056697.
Lemma F_54870 : fetch_word Asan.M.loaded_segments (0x54870 : word) = Some W_54870.
Proof. vm_refl. Qed.
Lemma D_54870 : decode_any W_54870 = Some (Auipc 13 86, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54874 : bv 32 := 0x6106b683.
Lemma F_54874 : fetch_word Asan.M.loaded_segments (0x54874 : word) = Some W_54874.
Proof. vm_refl. Qed.
Lemma D_54874 : decode_any W_54874 = Some (Load SZ8 true 13 13 1552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54878 : bv 32 := 0x0006b703.
Lemma F_54878 : fetch_word Asan.M.loaded_segments (0x54878 : word) = Some W_54878.
Proof. vm_refl. Qed.
Lemma D_54878 : decode_any W_54878 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5487c : bv 32 := 0xfff98993.
Lemma F_5487c : fetch_word Asan.M.loaded_segments (0x5487c : word) = Some W_5487c.
Proof. vm_refl. Qed.
Lemma D_5487c : decode_any W_5487c = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54880 : bv 32 := 0x0035d693.
Lemma F_54880 : fetch_word Asan.M.loaded_segments (0x54880 : word) = Some W_54880.
Proof. vm_refl. Qed.
Lemma D_54880 : decode_any W_54880 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54884 : bv 32 := 0x0039d793.
Lemma F_54884 : fetch_word Asan.M.loaded_segments (0x54884 : word) = Some W_54884.
Proof. vm_refl. Qed.
Lemma D_54884 : decode_any W_54884 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54888 : bv 32 := 0x00d706b3.
Lemma F_54888 : fetch_word Asan.M.loaded_segments (0x54888 : word) = Some W_54888.
Proof. vm_refl. Qed.
Lemma D_54888 : decode_any W_54888 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5488c : bv 32 := 0x00f70733.
Lemma F_5488c : fetch_word Asan.M.loaded_segments (0x5488c : word) = Some W_5488c.
Proof. vm_refl. Qed.
Lemma D_5488c : decode_any W_5488c = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54890 : bv 32 := 0xff86f793.
Lemma F_54890 : fetch_word Asan.M.loaded_segments (0x54890 : word) = Some W_54890.
Proof. vm_refl. Qed.
Lemma D_54890 : decode_any W_54890 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54894 : bv 32 := 0xff877813.
Lemma F_54894 : fetch_word Asan.M.loaded_segments (0x54894 : word) = Some W_54894.
Proof. vm_refl. Qed.
Lemma D_54894 : decode_any W_54894 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54898 : bv 32 := 0x0007b783.
Lemma F_54898 : fetch_word Asan.M.loaded_segments (0x54898 : word) = Some W_54898.
Proof. vm_refl. Qed.
Lemma D_54898 : decode_any W_54898 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5489c : bv 32 := 0x00083803.
Lemma F_5489c : fetch_word Asan.M.loaded_segments (0x5489c : word) = Some W_5489c.
Proof. vm_refl. Qed.
Lemma D_5489c : decode_any W_5489c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548a0 : bv 32 := 0x00f867b3.
Lemma F_548a0 : fetch_word Asan.M.loaded_segments (0x548a0 : word) = Some W_548a0.
Proof. vm_refl. Qed.
Lemma D_548a0 : decode_any W_548a0 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548a4 : bv 32 := 0x2a079e63.
Lemma F_548a4 : fetch_word Asan.M.loaded_segments (0x548a4 : word) = Some W_548a4.
Proof. vm_refl. Qed.
Lemma D_548a4 : decode_any W_548a4 = Some (Branch BC_NE 15 0 700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548a8 : bv 32 := 0xfff54693.
Lemma F_548a8 : fetch_word Asan.M.loaded_segments (0x548a8 : word) = Some W_548a8.
Proof. vm_refl. Qed.
Lemma D_548a8 : decode_any W_548a8 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548ac : bv 32 := 0x0cc6ee63.
Lemma F_548ac : fetch_word Asan.M.loaded_segments (0x548ac : word) = Some W_548ac.
Proof. vm_refl. Qed.
Lemma D_548ac : decode_any W_548ac = Some (Branch BC_LTU 13 12 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548b0 : bv 32 := 0xfbf00693.
Lemma F_548b0 : fetch_word Asan.M.loaded_segments (0x548b0 : word) = Some W_548b0.
Proof. vm_refl. Qed.
Lemma D_548b0 : decode_any W_548b0 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548b4 : bv 32 := 0x1566fc63.
Lemma F_548b4 : fetch_word Asan.M.loaded_segments (0x548b4 : word) = Some W_548b4.
Proof. vm_refl. Qed.
Lemma D_548b4 : decode_any W_548b4 = Some (Branch BC_GEU 13 22 344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548b8 : bv 32 := 0x00056697.
Lemma F_548b8 : fetch_word Asan.M.loaded_segments (0x548b8 : word) = Some W_548b8.
Proof. vm_refl. Qed.
Lemma D_548b8 : decode_any W_548b8 = Some (Auipc 13 86, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548bc : bv 32 := 0x5c86b683.
Lemma F_548bc : fetch_word Asan.M.loaded_segments (0x548bc : word) = Some W_548bc.
Proof. vm_refl. Qed.
Lemma D_548bc : decode_any W_548bc = Some (Load SZ8 true 13 13 1480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548c0 : bv 32 := 0x0006b703.
Lemma F_548c0 : fetch_word Asan.M.loaded_segments (0x548c0 : word) = Some W_548c0.
Proof. vm_refl. Qed.
Lemma D_548c0 : decode_any W_548c0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548c4 : bv 32 := 0xfffa0a13.
Lemma F_548c4 : fetch_word Asan.M.loaded_segments (0x548c4 : word) = Some W_548c4.
Proof. vm_refl. Qed.
Lemma D_548c4 : decode_any W_548c4 = Some (OpImm ALU_ADD 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548c8 : bv 32 := 0x00355693.
Lemma F_548c8 : fetch_word Asan.M.loaded_segments (0x548c8 : word) = Some W_548c8.
Proof. vm_refl. Qed.
Lemma D_548c8 : decode_any W_548c8 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548cc : bv 32 := 0x003a5793.
Lemma F_548cc : fetch_word Asan.M.loaded_segments (0x548cc : word) = Some W_548cc.
Proof. vm_refl. Qed.
Lemma D_548cc : decode_any W_548cc = Some (ShiftImm ALU_SRL 15 20 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548d0 : bv 32 := 0x00d706b3.
Lemma F_548d0 : fetch_word Asan.M.loaded_segments (0x548d0 : word) = Some W_548d0.
Proof. vm_refl. Qed.
Lemma D_548d0 : decode_any W_548d0 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548d4 : bv 32 := 0x00f70733.
Lemma F_548d4 : fetch_word Asan.M.loaded_segments (0x548d4 : word) = Some W_548d4.
Proof. vm_refl. Qed.
Lemma D_548d4 : decode_any W_548d4 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548d8 : bv 32 := 0xff86f793.
Lemma F_548d8 : fetch_word Asan.M.loaded_segments (0x548d8 : word) = Some W_548d8.
Proof. vm_refl. Qed.
Lemma D_548d8 : decode_any W_548d8 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548dc : bv 32 := 0xff877813.
Lemma F_548dc : fetch_word Asan.M.loaded_segments (0x548dc : word) = Some W_548dc.
Proof. vm_refl. Qed.
Lemma D_548dc : decode_any W_548dc = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548e0 : bv 32 := 0x0007b783.
Lemma F_548e0 : fetch_word Asan.M.loaded_segments (0x548e0 : word) = Some W_548e0.
Proof. vm_refl. Qed.
Lemma D_548e0 : decode_any W_548e0 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548e4 : bv 32 := 0x00083803.
Lemma F_548e4 : fetch_word Asan.M.loaded_segments (0x548e4 : word) = Some W_548e4.
Proof. vm_refl. Qed.
Lemma D_548e4 : decode_any W_548e4 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548e8 : bv 32 := 0x00f867b3.
Lemma F_548e8 : fetch_word Asan.M.loaded_segments (0x548e8 : word) = Some W_548e8.
Proof. vm_refl. Qed.
Lemma D_548e8 : decode_any W_548e8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548ec : bv 32 := 0x36079a63.
Lemma F_548ec : fetch_word Asan.M.loaded_segments (0x548ec : word) = Some W_548ec.
Proof. vm_refl. Qed.
Lemma D_548ec : decode_any W_548ec = Some (Branch BC_NE 15 0 884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548f0 : bv 32 := 0x00058697.
Lemma F_548f0 : fetch_word Asan.M.loaded_segments (0x548f0 : word) = Some W_548f0.
Proof. vm_refl. Qed.
Lemma D_548f0 : decode_any W_548f0 = Some (Auipc 13 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548f4 : bv 32 := 0x3f86b683.
Lemma F_548f4 : fetch_word Asan.M.loaded_segments (0x548f4 : word) = Some W_548f4.
Proof. vm_refl. Qed.
Lemma D_548f4 : decode_any W_548f4 = Some (Load SZ8 true 13 13 1016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548f8 : bv 32 := 0x000680e7.
Lemma F_548f8 : fetch_word Asan.M.loaded_segments (0x548f8 : word) = Some W_548f8.
Proof. vm_refl. Qed.
Lemma D_548f8 : decode_any W_548f8 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.
