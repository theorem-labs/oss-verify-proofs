(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.hashtable.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_2701a4 : bv 32 := 0xfc010113.
Lemma F_2701a4 : fetch_word Plain.M.loaded_segments (0x2701e8 : word) = Some W_2701a4.
Proof. vm_refl. Qed.
Lemma D_2701a4 : decode_any W_2701a4 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701a8 : bv 32 := 0x02113c23.
Lemma F_2701a8 : fetch_word Plain.M.loaded_segments (0x2701ec : word) = Some W_2701a8.
Proof. vm_refl. Qed.
Lemma D_2701a8 : decode_any W_2701a8 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701ac : bv 32 := 0x02813823.
Lemma F_2701ac : fetch_word Plain.M.loaded_segments (0x2701f0 : word) = Some W_2701ac.
Proof. vm_refl. Qed.
Lemma D_2701ac : decode_any W_2701ac = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701b0 : bv 32 := 0x02913423.
Lemma F_2701b0 : fetch_word Plain.M.loaded_segments (0x2701f4 : word) = Some W_2701b0.
Proof. vm_refl. Qed.
Lemma D_2701b0 : decode_any W_2701b0 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701b4 : bv 32 := 0x03213023.
Lemma F_2701b4 : fetch_word Plain.M.loaded_segments (0x2701f8 : word) = Some W_2701b4.
Proof. vm_refl. Qed.
Lemma D_2701b4 : decode_any W_2701b4 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701b8 : bv 32 := 0x01313c23.
Lemma F_2701b8 : fetch_word Plain.M.loaded_segments (0x2701fc : word) = Some W_2701b8.
Proof. vm_refl. Qed.
Lemma D_2701b8 : decode_any W_2701b8 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701bc : bv 32 := 0x01413823.
Lemma F_2701bc : fetch_word Plain.M.loaded_segments (0x270200 : word) = Some W_2701bc.
Proof. vm_refl. Qed.
Lemma D_2701bc : decode_any W_2701bc = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701c0 : bv 32 := 0x01513423.
Lemma F_2701c0 : fetch_word Plain.M.loaded_segments (0x270204 : word) = Some W_2701c0.
Proof. vm_refl. Qed.
Lemma D_2701c0 : decode_any W_2701c0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701c4 : bv 32 := 0x00060413.
Lemma F_2701c4 : fetch_word Plain.M.loaded_segments (0x270208 : word) = Some W_2701c4.
Proof. vm_refl. Qed.
Lemma D_2701c4 : decode_any W_2701c4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701c8 : bv 32 := 0x00058493.
Lemma F_2701c8 : fetch_word Plain.M.loaded_segments (0x27020c : word) = Some W_2701c8.
Proof. vm_refl. Qed.
Lemma D_2701c8 : decode_any W_2701c8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701cc : bv 32 := 0x02063583.
Lemma F_2701cc : fetch_word Plain.M.loaded_segments (0x270210 : word) = Some W_2701cc.
Proof. vm_refl. Qed.
Lemma D_2701cc : decode_any W_2701cc = Some (Load SZ8 true 11 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701d0 : bv 32 := 0x00050913.
Lemma F_2701d0 : fetch_word Plain.M.loaded_segments (0x270214 : word) = Some W_2701d0.
Proof. vm_refl. Qed.
Lemma D_2701d0 : decode_any W_2701d0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701d4 : bv 32 := 0x08058263.
Lemma F_2701d4 : fetch_word Plain.M.loaded_segments (0x270218 : word) = Some W_2701d4.
Proof. vm_refl. Qed.
Lemma D_2701d4 : decode_any W_2701d4 = Some (Branch BC_EQ 11 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701d8 : bv 32 := 0x02843503.
Lemma F_2701d8 : fetch_word Plain.M.loaded_segments (0x27021c : word) = Some W_2701d8.
Proof. vm_refl. Qed.
Lemma D_2701d8 : decode_any W_2701d8 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701dc : bv 32 := 0x40a585b3.
Lemma F_2701dc : fetch_word Plain.M.loaded_segments (0x270220 : word) = Some W_2701dc.
Proof. vm_refl. Qed.
Lemma D_2701dc : decode_any W_2701dc = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701e0 : bv 32 := 0x0295fc63.
Lemma F_2701e0 : fetch_word Plain.M.loaded_segments (0x270224 : word) = Some W_2701e0.
Proof. vm_refl. Qed.
Lemma D_2701e0 : decode_any W_2701e0 = Some (Branch BC_GEU 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701e4 : bv 32 := 0x04843303.
Lemma F_2701e4 : fetch_word Plain.M.loaded_segments (0x270228 : word) = Some W_2701e4.
Proof. vm_refl. Qed.
Lemma D_2701e4 : decode_any W_2701e4 = Some (Load SZ8 true 6 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701e8 : bv 32 := 0x00040513.
Lemma F_2701e8 : fetch_word Plain.M.loaded_segments (0x27022c : word) = Some W_2701e8.
Proof. vm_refl. Qed.
Lemma D_2701e8 : decode_any W_2701e8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701ec : bv 32 := 0x00090593.
Lemma F_2701ec : fetch_word Plain.M.loaded_segments (0x270230 : word) = Some W_2701ec.
Proof. vm_refl. Qed.
Lemma D_2701ec : decode_any W_2701ec = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701f0 : bv 32 := 0x00048613.
Lemma F_2701f0 : fetch_word Plain.M.loaded_segments (0x270234 : word) = Some W_2701f0.
Proof. vm_refl. Qed.
Lemma D_2701f0 : decode_any W_2701f0 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701f4 : bv 32 := 0x03813083.
Lemma F_2701f4 : fetch_word Plain.M.loaded_segments (0x270238 : word) = Some W_2701f4.
Proof. vm_refl. Qed.
Lemma D_2701f4 : decode_any W_2701f4 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701f8 : bv 32 := 0x03013403.
Lemma F_2701f8 : fetch_word Plain.M.loaded_segments (0x27023c : word) = Some W_2701f8.
Proof. vm_refl. Qed.
Lemma D_2701f8 : decode_any W_2701f8 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2701fc : bv 32 := 0x02813483.
Lemma F_2701fc : fetch_word Plain.M.loaded_segments (0x270240 : word) = Some W_2701fc.
Proof. vm_refl. Qed.
Lemma D_2701fc : decode_any W_2701fc = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270200 : bv 32 := 0x02013903.
Lemma F_270200 : fetch_word Plain.M.loaded_segments (0x270244 : word) = Some W_270200.
Proof. vm_refl. Qed.
Lemma D_270200 : decode_any W_270200 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270204 : bv 32 := 0x01813983.
Lemma F_270204 : fetch_word Plain.M.loaded_segments (0x270248 : word) = Some W_270204.
Proof. vm_refl. Qed.
Lemma D_270204 : decode_any W_270204 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270208 : bv 32 := 0x01013a03.
Lemma F_270208 : fetch_word Plain.M.loaded_segments (0x27024c : word) = Some W_270208.
Proof. vm_refl. Qed.
Lemma D_270208 : decode_any W_270208 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27020c : bv 32 := 0x00813a83.
Lemma F_27020c : fetch_word Plain.M.loaded_segments (0x270250 : word) = Some W_27020c.
Proof. vm_refl. Qed.
Lemma D_27020c : decode_any W_27020c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270210 : bv 32 := 0x04010113.
Lemma F_270210 : fetch_word Plain.M.loaded_segments (0x270254 : word) = Some W_270210.
Proof. vm_refl. Qed.
Lemma D_270210 : decode_any W_270210 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270214 : bv 32 := 0x00030067.
Lemma F_270214 : fetch_word Plain.M.loaded_segments (0x270258 : word) = Some W_270214.
Proof. vm_refl. Qed.
Lemma D_270214 : decode_any W_270214 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270218 : bv 32 := 0x09042583.
Lemma F_270218 : fetch_word Plain.M.loaded_segments (0x27025c : word) = Some W_270218.
Proof. vm_refl. Qed.
Lemma D_270218 : decode_any W_270218 = Some (Load SZ4 true 11 8 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27021c : bv 32 := 0x00000993.
Lemma F_27021c : fetch_word Plain.M.loaded_segments (0x270260 : word) = Some W_27021c.
Proof. vm_refl. Qed.
Lemma D_27021c : decode_any W_27021c = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270220 : bv 32 := 0x0605ce63.
Lemma F_270220 : fetch_word Plain.M.loaded_segments (0x270264 : word) = Some W_270220.
Proof. vm_refl. Qed.
Lemma D_270220 : decode_any W_270220 = Some (Branch BC_LT 11 0 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270224 : bv 32 := 0x06048c63.
Lemma F_270224 : fetch_word Plain.M.loaded_segments (0x270268 : word) = Some W_270224.
Proof. vm_refl. Qed.
Lemma D_270224 : decode_any W_270224 = Some (Branch BC_EQ 9 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270228 : bv 32 := 0x00000a13.
Lemma F_270228 : fetch_word Plain.M.loaded_segments (0x27026c : word) = Some W_270228.
Proof. vm_refl. Qed.
Lemma D_270228 : decode_any W_270228 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27022c : bv 32 := 0x00990ab3.
Lemma F_27022c : fetch_word Plain.M.loaded_segments (0x270270 : word) = Some W_27022c.
Proof. vm_refl. Qed.
Lemma D_27022c : decode_any W_27022c = Some (Op ALU_ADD 21 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270230 : bv 32 := 0xfff00593.
Lemma F_270230 : fetch_word Plain.M.loaded_segments (0x270274 : word) = Some W_270230.
Proof. vm_refl. Qed.
Lemma D_270230 : decode_any W_270230 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270234 : bv 32 := 0x00a00613.
Lemma F_270234 : fetch_word Plain.M.loaded_segments (0x270278 : word) = Some W_270234.
Proof. vm_refl. Qed.
Lemma D_270234 : decode_any W_270234 = Some (OpImm ALU_ADD 12 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270238 : bv 32 := 0x00ba86b3.
Lemma F_270238 : fetch_word Plain.M.loaded_segments (0x27027c : word) = Some W_270238.
Proof. vm_refl. Qed.
Lemma D_270238 : decode_any W_270238 = Some (Op ALU_ADD 13 21 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27023c : bv 32 := 0x0006c683.
Lemma F_27023c : fetch_word Plain.M.loaded_segments (0x270280 : word) = Some W_27023c.
Proof. vm_refl. Qed.
Lemma D_27023c : decode_any W_27023c = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270240 : bv 32 := 0x02c68a63.
Lemma F_270240 : fetch_word Plain.M.loaded_segments (0x270284 : word) = Some W_270240.
Proof. vm_refl. Qed.
Lemma D_270240 : decode_any W_270240 = Some (Branch BC_EQ 13 12 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270244 : bv 32 := 0x001a0a13.
Lemma F_270244 : fetch_word Plain.M.loaded_segments (0x270288 : word) = Some W_270244.
Proof. vm_refl. Qed.
Lemma D_270244 : decode_any W_270244 = Some (OpImm ALU_ADD 20 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270248 : bv 32 := 0xfff58593.
Lemma F_270248 : fetch_word Plain.M.loaded_segments (0x27028c : word) = Some W_270248.
Proof. vm_refl. Qed.
Lemma D_270248 : decode_any W_270248 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27024c : bv 32 := 0xff4496e3.
Lemma F_27024c : fetch_word Plain.M.loaded_segments (0x270290 : word) = Some W_27024c.
Proof. vm_refl. Qed.
Lemma D_27024c : decode_any W_27024c = Some (Branch BC_NE 9 20 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270250 : bv 32 := 0x00000993.
Lemma F_270250 : fetch_word Plain.M.loaded_segments (0x270294 : word) = Some W_270250.
Proof. vm_refl. Qed.
Lemma D_270250 : decode_any W_270250 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270254 : bv 32 := 0x0480006f.
Lemma F_270254 : fetch_word Plain.M.loaded_segments (0x270298 : word) = Some W_270254.
Proof. vm_refl. Qed.
Lemma D_270254 : decode_any W_270254 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270258 : bv 32 := 0x00040513.
Lemma F_270258 : fetch_word Plain.M.loaded_segments (0x27029c : word) = Some W_270258.
Proof. vm_refl. Qed.
Lemma D_270258 : decode_any W_270258 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27025c : bv 32 := 0xb79ff0ef.
Lemma F_27025c : fetch_word Plain.M.loaded_segments (0x2702a0 : word) = Some W_27025c.
Proof. vm_refl. Qed.
Lemma D_27025c : decode_any W_27025c = Some (Jal 1 2095992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270260 : bv 32 := 0x00050663.
Lemma F_270260 : fetch_word Plain.M.loaded_segments (0x2702a4 : word) = Some W_270260.
Proof. vm_refl. Qed.
Lemma D_270260 : decode_any W_270260 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270264 : bv 32 := 0x00000513.
Lemma F_270264 : fetch_word Plain.M.loaded_segments (0x2702a8 : word) = Some W_270264.
Proof. vm_refl. Qed.
Lemma D_270264 : decode_any W_270264 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270268 : bv 32 := 0x0500006f.
Lemma F_270268 : fetch_word Plain.M.loaded_segments (0x2702ac : word) = Some W_270268.
Proof. vm_refl. Qed.
Lemma D_270268 : decode_any W_270268 = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27026c : bv 32 := 0x02043583.
Lemma F_27026c : fetch_word Plain.M.loaded_segments (0x2702b0 : word) = Some W_27026c.
Proof. vm_refl. Qed.
Lemma D_27026c : decode_any W_27026c = Some (Load SZ8 true 11 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270270 : bv 32 := 0xf69ff06f.
Lemma F_270270 : fetch_word Plain.M.loaded_segments (0x2702b4 : word) = Some W_270270.
Proof. vm_refl. Qed.
Lemma D_270270 : decode_any W_270270 = Some (Jal 0 2097000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270274 : bv 32 := 0x04843683.
Lemma F_270274 : fetch_word Plain.M.loaded_segments (0x2702b8 : word) = Some W_270274.
Proof. vm_refl. Qed.
Lemma D_270274 : decode_any W_270274 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270278 : bv 32 := 0x414489b3.
Lemma F_270278 : fetch_word Plain.M.loaded_segments (0x2702bc : word) = Some W_270278.
Proof. vm_refl. Qed.
Lemma D_270278 : decode_any W_270278 = Some (Op ALU_SUB 19 9 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27027c : bv 32 := 0x00040513.
Lemma F_27027c : fetch_word Plain.M.loaded_segments (0x2702c0 : word) = Some W_27027c.
Proof. vm_refl. Qed.
Lemma D_27027c : decode_any W_27027c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270280 : bv 32 := 0x00090593.
Lemma F_270280 : fetch_word Plain.M.loaded_segments (0x2702c4 : word) = Some W_270280.
Proof. vm_refl. Qed.
Lemma D_270280 : decode_any W_270280 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270284 : bv 32 := 0x00098613.
Lemma F_270284 : fetch_word Plain.M.loaded_segments (0x2702c8 : word) = Some W_270284.
Proof. vm_refl. Qed.
Lemma D_270284 : decode_any W_270284 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270288 : bv 32 := 0x000680e7.
Lemma F_270288 : fetch_word Plain.M.loaded_segments (0x2702cc : word) = Some W_270288.
Proof. vm_refl. Qed.
Lemma D_270288 : decode_any W_270288 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27028c : bv 32 := 0x03356663.
Lemma F_27028c : fetch_word Plain.M.loaded_segments (0x2702d0 : word) = Some W_27028c.
Proof. vm_refl. Qed.
Lemma D_27028c : decode_any W_27028c = Some (Branch BC_LTU 10 19 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270290 : bv 32 := 0x02843503.
Lemma F_270290 : fetch_word Plain.M.loaded_segments (0x2702d4 : word) = Some W_270290.
Proof. vm_refl. Qed.
Lemma D_270290 : decode_any W_270290 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270294 : bv 32 := 0x414a8933.
Lemma F_270294 : fetch_word Plain.M.loaded_segments (0x2702d8 : word) = Some W_270294.
Proof. vm_refl. Qed.
Lemma D_270294 : decode_any W_270294 = Some (Op ALU_SUB 18 21 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270298 : bv 32 := 0x000a0493.
Lemma F_270298 : fetch_word Plain.M.loaded_segments (0x2702dc : word) = Some W_270298.
Proof. vm_refl. Qed.
Lemma D_270298 : decode_any W_270298 = Some (OpImm ALU_ADD 9 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27029c : bv 32 := 0x00090593.
Lemma F_27029c : fetch_word Plain.M.loaded_segments (0x2702e0 : word) = Some W_27029c.
Proof. vm_refl. Qed.
Lemma D_27029c : decode_any W_27029c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702a0 : bv 32 := 0x00048613.
Lemma F_2702a0 : fetch_word Plain.M.loaded_segments (0x2702e4 : word) = Some W_2702a0.
Proof. vm_refl. Qed.
Lemma D_2702a0 : decode_any W_2702a0 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702a4 : bv 32 := 0x194060ef.
Lemma F_2702a4 : fetch_word Plain.M.loaded_segments (0x2702e8 : word) = Some W_2702a4.
Proof. vm_refl. Qed.
Lemma D_2702a4 : decode_any W_2702a4 = Some (Jal 1 24980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702a8 : bv 32 := 0x02843503.
Lemma F_2702a8 : fetch_word Plain.M.loaded_segments (0x2702ec : word) = Some W_2702a8.
Proof. vm_refl. Qed.
Lemma D_2702a8 : decode_any W_2702a8 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702ac : bv 32 := 0x00950533.
Lemma F_2702ac : fetch_word Plain.M.loaded_segments (0x2702f0 : word) = Some W_2702ac.
Proof. vm_refl. Qed.
Lemma D_2702ac : decode_any W_2702ac = Some (Op ALU_ADD 10 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702b0 : bv 32 := 0x02a43423.
Lemma F_2702b0 : fetch_word Plain.M.loaded_segments (0x2702f4 : word) = Some W_2702b0.
Proof. vm_refl. Qed.
Lemma D_2702b0 : decode_any W_2702b0 = Some (Store SZ8 8 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702b4 : bv 32 := 0x00998533.
Lemma F_2702b4 : fetch_word Plain.M.loaded_segments (0x2702f8 : word) = Some W_2702b4.
Proof. vm_refl. Qed.
Lemma D_2702b4 : decode_any W_2702b4 = Some (Op ALU_ADD 10 19 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702b8 : bv 32 := 0x03813083.
Lemma F_2702b8 : fetch_word Plain.M.loaded_segments (0x2702fc : word) = Some W_2702b8.
Proof. vm_refl. Qed.
Lemma D_2702b8 : decode_any W_2702b8 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702bc : bv 32 := 0x03013403.
Lemma F_2702bc : fetch_word Plain.M.loaded_segments (0x270300 : word) = Some W_2702bc.
Proof. vm_refl. Qed.
Lemma D_2702bc : decode_any W_2702bc = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702c0 : bv 32 := 0x02813483.
Lemma F_2702c0 : fetch_word Plain.M.loaded_segments (0x270304 : word) = Some W_2702c0.
Proof. vm_refl. Qed.
Lemma D_2702c0 : decode_any W_2702c0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702c4 : bv 32 := 0x02013903.
Lemma F_2702c4 : fetch_word Plain.M.loaded_segments (0x270308 : word) = Some W_2702c4.
Proof. vm_refl. Qed.
Lemma D_2702c4 : decode_any W_2702c4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702c8 : bv 32 := 0x01813983.
Lemma F_2702c8 : fetch_word Plain.M.loaded_segments (0x27030c : word) = Some W_2702c8.
Proof. vm_refl. Qed.
Lemma D_2702c8 : decode_any W_2702c8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702cc : bv 32 := 0x01013a03.
Lemma F_2702cc : fetch_word Plain.M.loaded_segments (0x270310 : word) = Some W_2702cc.
Proof. vm_refl. Qed.
Lemma D_2702cc : decode_any W_2702cc = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702d0 : bv 32 := 0x00813a83.
Lemma F_2702d0 : fetch_word Plain.M.loaded_segments (0x270314 : word) = Some W_2702d0.
Proof. vm_refl. Qed.
Lemma D_2702d0 : decode_any W_2702d0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702d4 : bv 32 := 0x04010113.
Lemma F_2702d4 : fetch_word Plain.M.loaded_segments (0x270318 : word) = Some W_2702d4.
Proof. vm_refl. Qed.
Lemma D_2702d4 : decode_any W_2702d4 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702d8 : bv 32 := 0x00008067.
Lemma F_2702d8 : fetch_word Plain.M.loaded_segments (0x27031c : word) = Some W_2702d8.
Proof. vm_refl. Qed.
Lemma D_2702d8 : decode_any W_2702d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702dc : bv 32 := 0xfc010113.
Lemma F_2702dc : fetch_word Plain.M.loaded_segments (0x270320 : word) = Some W_2702dc.
Proof. vm_refl. Qed.
Lemma D_2702dc : decode_any W_2702dc = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702e0 : bv 32 := 0x02113c23.
Lemma F_2702e0 : fetch_word Plain.M.loaded_segments (0x270324 : word) = Some W_2702e0.
Proof. vm_refl. Qed.
Lemma D_2702e0 : decode_any W_2702e0 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702e4 : bv 32 := 0x02813823.
Lemma F_2702e4 : fetch_word Plain.M.loaded_segments (0x270328 : word) = Some W_2702e4.
Proof. vm_refl. Qed.
Lemma D_2702e4 : decode_any W_2702e4 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702e8 : bv 32 := 0x02913423.
Lemma F_2702e8 : fetch_word Plain.M.loaded_segments (0x27032c : word) = Some W_2702e8.
Proof. vm_refl. Qed.
Lemma D_2702e8 : decode_any W_2702e8 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702ec : bv 32 := 0x03213023.
Lemma F_2702ec : fetch_word Plain.M.loaded_segments (0x270330 : word) = Some W_2702ec.
Proof. vm_refl. Qed.
Lemma D_2702ec : decode_any W_2702ec = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702f0 : bv 32 := 0x01313c23.
Lemma F_2702f0 : fetch_word Plain.M.loaded_segments (0x270334 : word) = Some W_2702f0.
Proof. vm_refl. Qed.
Lemma D_2702f0 : decode_any W_2702f0 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702f4 : bv 32 := 0x01413823.
Lemma F_2702f4 : fetch_word Plain.M.loaded_segments (0x270338 : word) = Some W_2702f4.
Proof. vm_refl. Qed.
Lemma D_2702f4 : decode_any W_2702f4 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702f8 : bv 32 := 0x01513423.
Lemma F_2702f8 : fetch_word Plain.M.loaded_segments (0x27033c : word) = Some W_2702f8.
Proof. vm_refl. Qed.
Lemma D_2702f8 : decode_any W_2702f8 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2702fc : bv 32 := 0x00068993.
Lemma F_2702fc : fetch_word Plain.M.loaded_segments (0x270340 : word) = Some W_2702fc.
Proof. vm_refl. Qed.
Lemma D_2702fc : decode_any W_2702fc = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270300 : bv 32 := 0x00060413.
Lemma F_270300 : fetch_word Plain.M.loaded_segments (0x270344 : word) = Some W_270300.
Proof. vm_refl. Qed.
Lemma D_270300 : decode_any W_270300 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270304 : bv 32 := 0x00058493.
Lemma F_270304 : fetch_word Plain.M.loaded_segments (0x270348 : word) = Some W_270304.
Proof. vm_refl. Qed.
Lemma D_270304 : decode_any W_270304 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270308 : bv 32 := 0x08c6a583.
Lemma F_270308 : fetch_word Plain.M.loaded_segments (0x27034c : word) = Some W_270308.
Proof. vm_refl. Qed.
Lemma D_270308 : decode_any W_270308 = Some (Load SZ4 true 11 13 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27030c : bv 32 := 0x02960933.
Lemma F_27030c : fetch_word Plain.M.loaded_segments (0x270350 : word) = Some W_27030c.
Proof. vm_refl. Qed.
Lemma D_27030c : decode_any W_27030c = Some (Mul M_MUL 18 12 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270310 : bv 32 := 0x0405c463.
Lemma F_270310 : fetch_word Plain.M.loaded_segments (0x270354 : word) = Some W_270310.
Proof. vm_refl. Qed.
Lemma D_270310 : decode_any W_270310 = Some (Branch BC_LT 11 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270314 : bv 32 := 0x00050a13.
Lemma F_270314 : fetch_word Plain.M.loaded_segments (0x270358 : word) = Some W_270314.
Proof. vm_refl. Qed.
Lemma D_270314 : decode_any W_270314 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270318 : bv 32 := 0x00098513.
Lemma F_270318 : fetch_word Plain.M.loaded_segments (0x27035c : word) = Some W_270318.
Proof. vm_refl. Qed.
Lemma D_270318 : decode_any W_270318 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27031c : bv 32 := 0xb2dfe0ef.
Lemma F_27031c : fetch_word Plain.M.loaded_segments (0x270360 : word) = Some W_27031c.
Proof. vm_refl. Qed.
Lemma D_27031c : decode_any W_27031c = Some (Jal 1 2091820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270320 : bv 32 := 0x00050a93.
Lemma F_270320 : fetch_word Plain.M.loaded_segments (0x270364 : word) = Some W_270320.
Proof. vm_refl. Qed.
Lemma D_270320 : decode_any W_270320 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270324 : bv 32 := 0x000a0513.
Lemma F_270324 : fetch_word Plain.M.loaded_segments (0x270368 : word) = Some W_270324.
Proof. vm_refl. Qed.
Lemma D_270324 : decode_any W_270324 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270328 : bv 32 := 0x00090593.
Lemma F_270328 : fetch_word Plain.M.loaded_segments (0x27036c : word) = Some W_270328.
Proof. vm_refl. Qed.
Lemma D_270328 : decode_any W_270328 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27032c : bv 32 := 0x00098613.
Lemma F_27032c : fetch_word Plain.M.loaded_segments (0x270370 : word) = Some W_27032c.
Proof. vm_refl. Qed.
Lemma D_27032c : decode_any W_27032c = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270330 : bv 32 := 0xe75ff0ef.
Lemma F_270330 : fetch_word Plain.M.loaded_segments (0x270374 : word) = Some W_270330.
Proof. vm_refl. Qed.
Lemma D_270330 : decode_any W_270330 = Some (Jal 1 2096756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270334 : bv 32 := 0x00050a13.
Lemma F_270334 : fetch_word Plain.M.loaded_segments (0x270378 : word) = Some W_270334.
Proof. vm_refl. Qed.
Lemma D_270334 : decode_any W_270334 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270338 : bv 32 := 0x000a8663.
Lemma F_270338 : fetch_word Plain.M.loaded_segments (0x27037c : word) = Some W_270338.
Proof. vm_refl. Qed.
Lemma D_270338 : decode_any W_270338 = Some (Branch BC_EQ 21 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27033c : bv 32 := 0x00098513.
Lemma F_27033c : fetch_word Plain.M.loaded_segments (0x270380 : word) = Some W_27033c.
Proof. vm_refl. Qed.
Lemma D_27033c : decode_any W_27033c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270340 : bv 32 := 0xc05fe0ef.
Lemma F_270340 : fetch_word Plain.M.loaded_segments (0x270384 : word) = Some W_270340.
Proof. vm_refl. Qed.
Lemma D_270340 : decode_any W_270340 = Some (Jal 1 2092036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270344 : bv 32 := 0x032a1463.
Lemma F_270344 : fetch_word Plain.M.loaded_segments (0x270388 : word) = Some W_270344.
Proof. vm_refl. Qed.
Lemma D_270344 : decode_any W_270344 = Some (Branch BC_NE 20 18 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270348 : bv 32 := 0x0014b513.
Lemma F_270348 : fetch_word Plain.M.loaded_segments (0x27038c : word) = Some W_270348.
Proof. vm_refl. Qed.
Lemma D_270348 : decode_any W_270348 = Some (OpImm ALU_SLTU 10 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27034c : bv 32 := 0xfff50513.
Lemma F_27034c : fetch_word Plain.M.loaded_segments (0x270390 : word) = Some W_27034c.
Proof. vm_refl. Qed.
Lemma D_27034c : decode_any W_27034c = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270350 : bv 32 := 0x00857533.
Lemma F_270350 : fetch_word Plain.M.loaded_segments (0x270394 : word) = Some W_270350.
Proof. vm_refl. Qed.
Lemma D_270350 : decode_any W_270350 = Some (Op ALU_AND 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270354 : bv 32 := 0x01c0006f.
Lemma F_270354 : fetch_word Plain.M.loaded_segments (0x270398 : word) = Some W_270354.
Proof. vm_refl. Qed.
Lemma D_270354 : decode_any W_270354 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270358 : bv 32 := 0x00090593.
Lemma F_270358 : fetch_word Plain.M.loaded_segments (0x27039c : word) = Some W_270358.
Proof. vm_refl. Qed.
Lemma D_270358 : decode_any W_270358 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27035c : bv 32 := 0x00098613.
Lemma F_27035c : fetch_word Plain.M.loaded_segments (0x2703a0 : word) = Some W_27035c.
Proof. vm_refl. Qed.
Lemma D_27035c : decode_any W_27035c = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270360 : bv 32 := 0xe45ff0ef.
Lemma F_270360 : fetch_word Plain.M.loaded_segments (0x2703a4 : word) = Some W_270360.
Proof. vm_refl. Qed.
Lemma D_270360 : decode_any W_270360 = Some (Jal 1 2096708, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270364 : bv 32 := 0x00050a13.
Lemma F_270364 : fetch_word Plain.M.loaded_segments (0x2703a8 : word) = Some W_270364.
Proof. vm_refl. Qed.
Lemma D_270364 : decode_any W_270364 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270368 : bv 32 := 0xff2500e3.
Lemma F_270368 : fetch_word Plain.M.loaded_segments (0x2703ac : word) = Some W_270368.
Proof. vm_refl. Qed.
Lemma D_270368 : decode_any W_270368 = Some (Branch BC_EQ 10 18 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27036c : bv 32 := 0x029a5533.
Lemma F_27036c : fetch_word Plain.M.loaded_segments (0x2703b0 : word) = Some W_27036c.
Proof. vm_refl. Qed.
Lemma D_27036c : decode_any W_27036c = Some (Mul M_DIVU 10 20 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270370 : bv 32 := 0x03813083.
Lemma F_270370 : fetch_word Plain.M.loaded_segments (0x2703b4 : word) = Some W_270370.
Proof. vm_refl. Qed.
Lemma D_270370 : decode_any W_270370 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270374 : bv 32 := 0x03013403.
Lemma F_270374 : fetch_word Plain.M.loaded_segments (0x2703b8 : word) = Some W_270374.
Proof. vm_refl. Qed.
Lemma D_270374 : decode_any W_270374 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270378 : bv 32 := 0x02813483.
Lemma F_270378 : fetch_word Plain.M.loaded_segments (0x2703bc : word) = Some W_270378.
Proof. vm_refl. Qed.
Lemma D_270378 : decode_any W_270378 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27037c : bv 32 := 0x02013903.
Lemma F_27037c : fetch_word Plain.M.loaded_segments (0x2703c0 : word) = Some W_27037c.
Proof. vm_refl. Qed.
Lemma D_27037c : decode_any W_27037c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270380 : bv 32 := 0x01813983.
Lemma F_270380 : fetch_word Plain.M.loaded_segments (0x2703c4 : word) = Some W_270380.
Proof. vm_refl. Qed.
Lemma D_270380 : decode_any W_270380 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270384 : bv 32 := 0x01013a03.
Lemma F_270384 : fetch_word Plain.M.loaded_segments (0x2703c8 : word) = Some W_270384.
Proof. vm_refl. Qed.
Lemma D_270384 : decode_any W_270384 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270388 : bv 32 := 0x00813a83.
Lemma F_270388 : fetch_word Plain.M.loaded_segments (0x2703cc : word) = Some W_270388.
Proof. vm_refl. Qed.
Lemma D_270388 : decode_any W_270388 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27038c : bv 32 := 0x04010113.
Lemma F_27038c : fetch_word Plain.M.loaded_segments (0x2703d0 : word) = Some W_27038c.
Proof. vm_refl. Qed.
Lemma D_27038c : decode_any W_27038c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270390 : bv 32 := 0x00008067.
Lemma F_270390 : fetch_word Plain.M.loaded_segments (0x2703d4 : word) = Some W_270390.
Proof. vm_refl. Qed.
Lemma D_270390 : decode_any W_270390 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270394 : bv 32 := 0xff010113.
Lemma F_270394 : fetch_word Plain.M.loaded_segments (0x2703d8 : word) = Some W_270394.
Proof. vm_refl. Qed.
Lemma D_270394 : decode_any W_270394 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270398 : bv 32 := 0x00113423.
Lemma F_270398 : fetch_word Plain.M.loaded_segments (0x2703dc : word) = Some W_270398.
Proof. vm_refl. Qed.
Lemma D_270398 : decode_any W_270398 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27039c : bv 32 := 0x00813023.
Lemma F_27039c : fetch_word Plain.M.loaded_segments (0x2703e0 : word) = Some W_27039c.
Proof. vm_refl. Qed.
Lemma D_27039c : decode_any W_27039c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2703a0 : bv 32 := 0x0009c517.
Lemma F_2703a0 : fetch_word Plain.M.loaded_segments (0x2703e4 : word) = Some W_2703a0.
Proof. vm_refl. Qed.
Lemma D_2703a0 : decode_any W_2703a0 = Some (Auipc 10 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2703a4 : bv 32 := 0x23450413.
Lemma F_2703a4 : fetch_word Plain.M.loaded_segments (0x2703e8 : word) = Some W_2703a4.
Proof. vm_refl. Qed.
Lemma D_2703a4 : decode_any W_2703a4 = Some (OpImm ALU_ADD 8 10 564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2703a8 : bv 32 := 0x00040513.
Lemma F_2703a8 : fetch_word Plain.M.loaded_segments (0x2703ec : word) = Some W_2703a8.
Proof. vm_refl. Qed.
Lemma D_2703a8 : decode_any W_2703a8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2703ac : bv 32 := 0x72d060ef.
Lemma F_2703ac : fetch_word Plain.M.loaded_segments (0x2703f0 : word) = Some W_2703ac.
Proof. vm_refl. Qed.
Lemma D_2703ac : decode_any W_2703ac = Some (Jal 1 28460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2703b0 : bv 32 := 0x00840513.
Lemma F_2703b0 : fetch_word Plain.M.loaded_segments (0x2703f4 : word) = Some W_2703b0.
Proof. vm_refl. Qed.
Lemma D_2703b0 : decode_any W_2703b0 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2703b4 : bv 32 := 0x00813083.
Lemma F_2703b4 : fetch_word Plain.M.loaded_segments (0x2703f8 : word) = Some W_2703b4.
Proof. vm_refl. Qed.
Lemma D_2703b4 : decode_any W_2703b4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2703b8 : bv 32 := 0x00013403.
Lemma F_2703b8 : fetch_word Plain.M.loaded_segments (0x2703fc : word) = Some W_2703b8.
Proof. vm_refl. Qed.
Lemma D_2703b8 : decode_any W_2703b8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2703bc : bv 32 := 0x01010113.
Lemma F_2703bc : fetch_word Plain.M.loaded_segments (0x270400 : word) = Some W_2703bc.
Proof. vm_refl. Qed.
Lemma D_2703bc : decode_any W_2703bc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2703c0 : bv 32 := 0x00008067.
Lemma F_2703c0 : fetch_word Plain.M.loaded_segments (0x270404 : word) = Some W_2703c0.
Proof. vm_refl. Qed.
Lemma D_2703c0 : decode_any W_2703c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270470 : bv 32 := 0xfe010113.
Lemma F_270470 : fetch_word Plain.M.loaded_segments (0x2704b4 : word) = Some W_270470.
Proof. vm_refl. Qed.
Lemma D_270470 : decode_any W_270470 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270474 : bv 32 := 0x00113c23.
Lemma F_270474 : fetch_word Plain.M.loaded_segments (0x2704b8 : word) = Some W_270474.
Proof. vm_refl. Qed.
Lemma D_270474 : decode_any W_270474 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270478 : bv 32 := 0x00813823.
Lemma F_270478 : fetch_word Plain.M.loaded_segments (0x2704bc : word) = Some W_270478.
Proof. vm_refl. Qed.
Lemma D_270478 : decode_any W_270478 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27047c : bv 32 := 0x00067697.
Lemma F_27047c : fetch_word Plain.M.loaded_segments (0x2704c0 : word) = Some W_27047c.
Proof. vm_refl. Qed.
Lemma D_27047c : decode_any W_27047c = Some (Auipc 13 103, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270480 : bv 32 := 0x6e06b403.
Lemma F_270480 : fetch_word Plain.M.loaded_segments (0x2704c4 : word) = Some W_270480.
Proof. vm_refl. Qed.
Lemma D_270480 : decode_any W_270480 = Some (Load SZ8 true 8 13 1760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270484 : bv 32 := 0x00043683.
Lemma F_270484 : fetch_word Plain.M.loaded_segments (0x2704c8 : word) = Some W_270484.
Proof. vm_refl. Qed.
Lemma D_270484 : decode_any W_270484 = Some (Load SZ8 true 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270488 : bv 32 := 0x00d13423.
Lemma F_270488 : fetch_word Plain.M.loaded_segments (0x2704cc : word) = Some W_270488.
Proof. vm_refl. Qed.
Lemma D_270488 : decode_any W_270488 = Some (Store SZ8 2 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27048c : bv 32 := 0x00054683.
Lemma F_27048c : fetch_word Plain.M.loaded_segments (0x2704d0 : word) = Some W_27048c.
Proof. vm_refl. Qed.
Lemma D_27048c : decode_any W_27048c = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270490 : bv 32 := 0xfffff717.
Lemma F_270490 : fetch_word Plain.M.loaded_segments (0x2704d4 : word) = Some W_270490.
Proof. vm_refl. Qed.
Lemma D_270490 : decode_any W_270490 = Some (Auipc 14 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270494 : bv 32 := 0x53070713.
Lemma F_270494 : fetch_word Plain.M.loaded_segments (0x2704d8 : word) = Some W_270494.
Proof. vm_refl. Qed.
Lemma D_270494 : decode_any W_270494 = Some (OpImm ALU_ADD 14 14 1328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270498 : bv 32 := 0x0406f693.
Lemma F_270498 : fetch_word Plain.M.loaded_segments (0x2704dc : word) = Some W_270498.
Proof. vm_refl. Qed.
Lemma D_270498 : decode_any W_270498 = Some (OpImm ALU_AND 13 13 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27049c : bv 32 := 0x04e53423.
Lemma F_27049c : fetch_word Plain.M.loaded_segments (0x2704e0 : word) = Some W_27049c.
Proof. vm_refl. Qed.
Lemma D_27049c : decode_any W_27049c = Some (Store SZ8 10 14 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704a0 : bv 32 := 0x04069663.
Lemma F_2704a0 : fetch_word Plain.M.loaded_segments (0x2704e4 : word) = Some W_2704a0.
Proof. vm_refl. Qed.
Lemma D_2704a0 : decode_any W_2704a0 = Some (Branch BC_NE 13 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704a4 : bv 32 := 0x07852683.
Lemma F_2704a4 : fetch_word Plain.M.loaded_segments (0x2704e8 : word) = Some W_2704a4.
Proof. vm_refl. Qed.
Lemma D_2704a4 : decode_any W_2704a4 = Some (Load SZ4 true 13 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704a8 : bv 32 := 0x00005737.
Lemma F_2704a8 : fetch_word Plain.M.loaded_segments (0x2704ec : word) = Some W_2704a8.
Proof. vm_refl. Qed.
Lemma D_2704a8 : decode_any W_2704a8 = Some (Lui 14 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704ac : bv 32 := 0x4137071b.
Lemma F_2704ac : fetch_word Plain.M.loaded_segments (0x2704f0 : word) = Some W_2704ac.
Proof. vm_refl. Qed.
Lemma D_2704ac : decode_any W_2704ac = Some (OpImm32 14 14 1043, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704b0 : bv 32 := 0x01d00893.
Lemma F_2704b0 : fetch_word Plain.M.loaded_segments (0x2704f4 : word) = Some W_2704b0.
Proof. vm_refl. Qed.
Lemma D_2704b0 : decode_any W_2704b0 = Some (OpImm ALU_ADD 17 0 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704b4 : bv 32 := 0x00060793.
Lemma F_2704b4 : fetch_word Plain.M.loaded_segments (0x2704f8 : word) = Some W_2704b4.
Proof. vm_refl. Qed.
Lemma D_2704b4 : decode_any W_2704b4 = Some (OpImm ALU_ADD 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704b8 : bv 32 := 0x00010613.
Lemma F_2704b8 : fetch_word Plain.M.loaded_segments (0x2704fc : word) = Some W_2704b8.
Proof. vm_refl. Qed.
Lemma D_2704b8 : decode_any W_2704b8 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704bc : bv 32 := 0x00050813.
Lemma F_2704bc : fetch_word Plain.M.loaded_segments (0x270500 : word) = Some W_2704bc.
Proof. vm_refl. Qed.
Lemma D_2704bc : decode_any W_2704bc = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704c0 : bv 32 := 0x00068513.
Lemma F_2704c0 : fetch_word Plain.M.loaded_segments (0x270504 : word) = Some W_2704c0.
Proof. vm_refl. Qed.
Lemma D_2704c0 : decode_any W_2704c0 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704c4 : bv 32 := 0x00058693.
Lemma F_2704c4 : fetch_word Plain.M.loaded_segments (0x270508 : word) = Some W_2704c4.
Proof. vm_refl. Qed.
Lemma D_2704c4 : decode_any W_2704c4 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704c8 : bv 32 := 0x00070593.
Lemma F_2704c8 : fetch_word Plain.M.loaded_segments (0x27050c : word) = Some W_2704c8.
Proof. vm_refl. Qed.
Lemma D_2704c8 : decode_any W_2704c8 = Some (OpImm ALU_ADD 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704cc : bv 32 := 0x00000073.
Lemma F_2704cc : fetch_word Plain.M.loaded_segments (0x270510 : word) = Some W_2704cc.
Proof. vm_refl. Qed.
Lemma D_2704cc : decode_any W_2704cc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_2704cc : is_ecall W_2704cc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_2704d0 : bv 32 := 0x00068593.
Lemma F_2704d0 : fetch_word Plain.M.loaded_segments (0x270514 : word) = Some W_2704d0.
Proof. vm_refl. Qed.
Lemma D_2704d0 : decode_any W_2704d0 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704d4 : bv 32 := 0x00078613.
Lemma F_2704d4 : fetch_word Plain.M.loaded_segments (0x270518 : word) = Some W_2704d4.
Proof. vm_refl. Qed.
Lemma D_2704d4 : decode_any W_2704d4 = Some (OpImm ALU_ADD 12 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704d8 : bv 32 := 0x00050693.
Lemma F_2704d8 : fetch_word Plain.M.loaded_segments (0x27051c : word) = Some W_2704d8.
Proof. vm_refl. Qed.
Lemma D_2704d8 : decode_any W_2704d8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704dc : bv 32 := 0x00080513.
Lemma F_2704dc : fetch_word Plain.M.loaded_segments (0x270520 : word) = Some W_2704dc.
Proof. vm_refl. Qed.
Lemma D_2704dc : decode_any W_2704dc = Some (OpImm ALU_ADD 10 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704e0 : bv 32 := 0x00068663.
Lemma F_2704e0 : fetch_word Plain.M.loaded_segments (0x270524 : word) = Some W_2704e0.
Proof. vm_refl. Qed.
Lemma D_2704e0 : decode_any W_2704e0 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704e4 : bv 32 := 0xfff00693.
Lemma F_2704e4 : fetch_word Plain.M.loaded_segments (0x270528 : word) = Some W_2704e4.
Proof. vm_refl. Qed.
Lemma D_2704e4 : decode_any W_2704e4 = Some (OpImm ALU_ADD 13 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704e8 : bv 32 := 0x08d52823.
Lemma F_2704e8 : fetch_word Plain.M.loaded_segments (0x27052c : word) = Some W_2704e8.
Proof. vm_refl. Qed.
Lemma D_2704e8 : decode_any W_2704e8 = Some (Store SZ4 10 13 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704ec : bv 32 := 0xcd4ff0ef.
Lemma F_2704ec : fetch_word Plain.M.loaded_segments (0x270530 : word) = Some W_2704ec.
Proof. vm_refl. Qed.
Lemma D_2704ec : decode_any W_2704ec = Some (Jal 1 2094292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704f0 : bv 32 := 0x00043583.
Lemma F_2704f0 : fetch_word Plain.M.loaded_segments (0x270534 : word) = Some W_2704f0.
Proof. vm_refl. Qed.
Lemma D_2704f0 : decode_any W_2704f0 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704f4 : bv 32 := 0x00813603.
Lemma F_2704f4 : fetch_word Plain.M.loaded_segments (0x270538 : word) = Some W_2704f4.
Proof. vm_refl. Qed.
Lemma D_2704f4 : decode_any W_2704f4 = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704f8 : bv 32 := 0x00c59a63.
Lemma F_2704f8 : fetch_word Plain.M.loaded_segments (0x27053c : word) = Some W_2704f8.
Proof. vm_refl. Qed.
Lemma D_2704f8 : decode_any W_2704f8 = Some (Branch BC_NE 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2704fc : bv 32 := 0x01813083.
Lemma F_2704fc : fetch_word Plain.M.loaded_segments (0x270540 : word) = Some W_2704fc.
Proof. vm_refl. Qed.
Lemma D_2704fc : decode_any W_2704fc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270500 : bv 32 := 0x01013403.
Lemma F_270500 : fetch_word Plain.M.loaded_segments (0x270544 : word) = Some W_270500.
Proof. vm_refl. Qed.
Lemma D_270500 : decode_any W_270500 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270504 : bv 32 := 0x02010113.
Lemma F_270504 : fetch_word Plain.M.loaded_segments (0x270548 : word) = Some W_270504.
Proof. vm_refl. Qed.
Lemma D_270504 : decode_any W_270504 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270508 : bv 32 := 0x00008067.
Lemma F_270508 : fetch_word Plain.M.loaded_segments (0x27054c : word) = Some W_270508.
Proof. vm_refl. Qed.
Lemma D_270508 : decode_any W_270508 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27050c : bv 32 := 0xc4cfb0ef.
Lemma F_27050c : fetch_word Plain.M.loaded_segments (0x270550 : word) = Some W_27050c.
Proof. vm_refl. Qed.
Lemma D_27050c : decode_any W_27050c = Some (Jal 1 2077772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270510 : bv 32 := 0xe9010113.
Lemma F_270510 : fetch_word Plain.M.loaded_segments (0x270554 : word) = Some W_270510.
Proof. vm_refl. Qed.
Lemma D_270510 : decode_any W_270510 = Some (OpImm ALU_ADD 2 2 3728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270514 : bv 32 := 0x16113423.
Lemma F_270514 : fetch_word Plain.M.loaded_segments (0x270558 : word) = Some W_270514.
Proof. vm_refl. Qed.
Lemma D_270514 : decode_any W_270514 = Some (Store SZ8 2 1 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270518 : bv 32 := 0x16813023.
Lemma F_270518 : fetch_word Plain.M.loaded_segments (0x27055c : word) = Some W_270518.
Proof. vm_refl. Qed.
Lemma D_270518 : decode_any W_270518 = Some (Store SZ8 2 8 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27051c : bv 32 := 0x14913c23.
Lemma F_27051c : fetch_word Plain.M.loaded_segments (0x270560 : word) = Some W_27051c.
Proof. vm_refl. Qed.
Lemma D_27051c : decode_any W_27051c = Some (Store SZ8 2 9 344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270520 : bv 32 := 0x15213823.
Lemma F_270520 : fetch_word Plain.M.loaded_segments (0x270564 : word) = Some W_270520.
Proof. vm_refl. Qed.
Lemma D_270520 : decode_any W_270520 = Some (Store SZ8 2 18 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270524 : bv 32 := 0x15313423.
Lemma F_270524 : fetch_word Plain.M.loaded_segments (0x270568 : word) = Some W_270524.
Proof. vm_refl. Qed.
Lemma D_270524 : decode_any W_270524 = Some (Store SZ8 2 19 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270528 : bv 32 := 0x15413023.
Lemma F_270528 : fetch_word Plain.M.loaded_segments (0x27056c : word) = Some W_270528.
Proof. vm_refl. Qed.
Lemma D_270528 : decode_any W_270528 = Some (Store SZ8 2 20 320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27052c : bv 32 := 0x13513c23.
Lemma F_27052c : fetch_word Plain.M.loaded_segments (0x270570 : word) = Some W_27052c.
Proof. vm_refl. Qed.
Lemma D_27052c : decode_any W_27052c = Some (Store SZ8 2 21 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270530 : bv 32 := 0x00058493.
Lemma F_270530 : fetch_word Plain.M.loaded_segments (0x270574 : word) = Some W_270530.
Proof. vm_refl. Qed.
Lemma D_270530 : decode_any W_270530 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270534 : bv 32 := 0x00050413.
Lemma F_270534 : fetch_word Plain.M.loaded_segments (0x270578 : word) = Some W_270534.
Proof. vm_refl. Qed.
Lemma D_270534 : decode_any W_270534 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270538 : bv 32 := 0x00067517.
Lemma F_270538 : fetch_word Plain.M.loaded_segments (0x27057c : word) = Some W_270538.
Proof. vm_refl. Qed.
Lemma D_270538 : decode_any W_270538 = Some (Auipc 10 103, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27053c : bv 32 := 0x62453903.
Lemma F_27053c : fetch_word Plain.M.loaded_segments (0x270580 : word) = Some W_27053c.
Proof. vm_refl. Qed.
Lemma D_27053c : decode_any W_27053c = Some (Load SZ8 true 18 10 1572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270540 : bv 32 := 0x00093503.
Lemma F_270540 : fetch_word Plain.M.loaded_segments (0x270584 : word) = Some W_270540.
Proof. vm_refl. Qed.
Lemma D_270540 : decode_any W_270540 = Some (Load SZ8 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270544 : bv 32 := 0x12a13823.
Lemma F_270544 : fetch_word Plain.M.loaded_segments (0x270588 : word) = Some W_270544.
Proof. vm_refl. Qed.
Lemma D_270544 : decode_any W_270544 = Some (Store SZ8 2 10 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270548 : bv 32 := 0x00c13423.
Lemma F_270548 : fetch_word Plain.M.loaded_segments (0x27058c : word) = Some W_270548.
Proof. vm_refl. Qed.
Lemma D_270548 : decode_any W_270548 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27054c : bv 32 := 0x12013423.
Lemma F_27054c : fetch_word Plain.M.loaded_segments (0x270590 : word) = Some W_27054c.
Proof. vm_refl. Qed.
Lemma D_27054c : decode_any W_27054c = Some (Store SZ8 2 0 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270550 : bv 32 := 0x10013423.
Lemma F_270550 : fetch_word Plain.M.loaded_segments (0x270594 : word) = Some W_270550.
Proof. vm_refl. Qed.
Lemma D_270550 : decode_any W_270550 = Some (Store SZ8 2 0 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270554 : bv 32 := 0x10013823.
Lemma F_270554 : fetch_word Plain.M.loaded_segments (0x270598 : word) = Some W_270554.
Proof. vm_refl. Qed.
Lemma D_270554 : decode_any W_270554 = Some (Store SZ8 2 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270558 : bv 32 := 0x10013c23.
Lemma F_270558 : fetch_word Plain.M.loaded_segments (0x27059c : word) = Some W_270558.
Proof. vm_refl. Qed.
Lemma D_270558 : decode_any W_270558 = Some (Store SZ8 2 0 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27055c : bv 32 := 0x12013023.
Lemma F_27055c : fetch_word Plain.M.loaded_segments (0x2705a0 : word) = Some W_27055c.
Proof. vm_refl. Qed.
Lemma D_27055c : decode_any W_27055c = Some (Store SZ8 2 0 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270560 : bv 32 := 0x00c13023.
Lemma F_270560 : fetch_word Plain.M.loaded_segments (0x2705a4 : word) = Some W_270560.
Proof. vm_refl. Qed.
Lemma D_270560 : decode_any W_270560 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270564 : bv 32 := 0x00010613.
Lemma F_270564 : fetch_word Plain.M.loaded_segments (0x2705a8 : word) = Some W_270564.
Proof. vm_refl. Qed.
Lemma D_270564 : decode_any W_270564 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270568 : bv 32 := 0x06010693.
Lemma F_270568 : fetch_word Plain.M.loaded_segments (0x2705ac : word) = Some W_270568.
Proof. vm_refl. Qed.
Lemma D_270568 : decode_any W_270568 = Some (OpImm ALU_ADD 13 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27056c : bv 32 := 0x10810713.
Lemma F_27056c : fetch_word Plain.M.loaded_segments (0x2705b0 : word) = Some W_27056c.
Proof. vm_refl. Qed.
Lemma D_27056c : decode_any W_27056c = Some (OpImm ALU_ADD 14 2 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270570 : bv 32 := 0x00000513.
Lemma F_270570 : fetch_word Plain.M.loaded_segments (0x2705b4 : word) = Some W_270570.
Proof. vm_refl. Qed.
Lemma D_270570 : decode_any W_270570 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270574 : bv 32 := 0x14c000ef.
Lemma F_270574 : fetch_word Plain.M.loaded_segments (0x2705b8 : word) = Some W_270574.
Proof. vm_refl. Qed.
Lemma D_270574 : decode_any W_270574 = Some (Jal 1 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270578 : bv 32 := 0x00054e63.
Lemma F_270578 : fetch_word Plain.M.loaded_segments (0x2705bc : word) = Some W_270578.
Proof. vm_refl. Qed.
Lemma D_270578 : decode_any W_270578 = Some (Branch BC_LT 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27057c : bv 32 := 0x08c42503.
Lemma F_27057c : fetch_word Plain.M.loaded_segments (0x2705c0 : word) = Some W_27057c.
Proof. vm_refl. Qed.
Lemma D_27057c : decode_any W_27057c = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270580 : bv 32 := 0x00054e63.
Lemma F_270580 : fetch_word Plain.M.loaded_segments (0x2705c4 : word) = Some W_270580.
Proof. vm_refl. Qed.
Lemma D_270580 : decode_any W_270580 = Some (Branch BC_LT 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270584 : bv 32 := 0x00040513.
Lemma F_270584 : fetch_word Plain.M.loaded_segments (0x2705c8 : word) = Some W_270584.
Proof. vm_refl. Qed.
Lemma D_270584 : decode_any W_270584 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270588 : bv 32 := 0x8c1fe0ef.
Lemma F_270588 : fetch_word Plain.M.loaded_segments (0x2705cc : word) = Some W_270588.
Proof. vm_refl. Qed.
Lemma D_270588 : decode_any W_270588 = Some (Jal 1 2091200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27058c : bv 32 := 0x00153993.
Lemma F_27058c : fetch_word Plain.M.loaded_segments (0x2705d0 : word) = Some W_27058c.
Proof. vm_refl. Qed.
Lemma D_27058c : decode_any W_27058c = Some (OpImm ALU_SLTU 19 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270590 : bv 32 := 0x0100006f.
Lemma F_270590 : fetch_word Plain.M.loaded_segments (0x2705d4 : word) = Some W_270590.
Proof. vm_refl. Qed.
Lemma D_270590 : decode_any W_270590 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270594 : bv 32 := 0xfff00513.
Lemma F_270594 : fetch_word Plain.M.loaded_segments (0x2705d8 : word) = Some W_270594.
Proof. vm_refl. Qed.
Lemma D_270594 : decode_any W_270594 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270598 : bv 32 := 0x0f40006f.
Lemma F_270598 : fetch_word Plain.M.loaded_segments (0x2705dc : word) = Some W_270598.
Proof. vm_refl. Qed.
Lemma D_270598 : decode_any W_270598 = Some (Jal 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27059c : bv 32 := 0x00100993.
Lemma F_27059c : fetch_word Plain.M.loaded_segments (0x2705e0 : word) = Some W_27059c.
Proof. vm_refl. Qed.
Lemma D_27059c : decode_any W_27059c = Some (OpImm ALU_ADD 19 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705a0 : bv 32 := 0x00042a83.
Lemma F_2705a0 : fetch_word Plain.M.loaded_segments (0x2705e4 : word) = Some W_2705a0.
Proof. vm_refl. Qed.
Lemma D_2705a0 : decode_any W_2705a0 = Some (Load SZ4 true 21 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705a4 : bv 32 := 0x06043503.
Lemma F_2705a4 : fetch_word Plain.M.loaded_segments (0x2705e8 : word) = Some W_2705a4.
Proof. vm_refl. Qed.
Lemma D_2705a4 : decode_any W_2705a4 = Some (Load SZ8 true 10 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705a8 : bv 32 := 0xfdfaf593.
Lemma F_2705a8 : fetch_word Plain.M.loaded_segments (0x2705ec : word) = Some W_2705a8.
Proof. vm_refl. Qed.
Lemma D_2705a8 : decode_any W_2705a8 = Some (OpImm ALU_AND 11 21 4063, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705ac : bv 32 := 0x00b42023.
Lemma F_2705ac : fetch_word Plain.M.loaded_segments (0x2705f0 : word) = Some W_2705ac.
Proof. vm_refl. Qed.
Lemma D_2705ac : decode_any W_2705ac = Some (Store SZ4 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705b0 : bv 32 := 0x00050a63.
Lemma F_2705b0 : fetch_word Plain.M.loaded_segments (0x2705f4 : word) = Some W_2705b0.
Proof. vm_refl. Qed.
Lemma D_2705b0 : decode_any W_2705b0 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705b4 : bv 32 := 0x02043503.
Lemma F_2705b4 : fetch_word Plain.M.loaded_segments (0x2705f8 : word) = Some W_2705b4.
Proof. vm_refl. Qed.
Lemma D_2705b4 : decode_any W_2705b4 = Some (Load SZ8 true 10 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705b8 : bv 32 := 0x00000a13.
Lemma F_2705b8 : fetch_word Plain.M.loaded_segments (0x2705fc : word) = Some W_2705b8.
Proof. vm_refl. Qed.
Lemma D_2705b8 : decode_any W_2705b8 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705bc : bv 32 := 0x04051263.
Lemma F_2705bc : fetch_word Plain.M.loaded_segments (0x270600 : word) = Some W_2705bc.
Proof. vm_refl. Qed.
Lemma D_2705bc : decode_any W_2705bc = Some (Branch BC_NE 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705c0 : bv 32 := 0x0240006f.
Lemma F_2705c0 : fetch_word Plain.M.loaded_segments (0x270604 : word) = Some W_2705c0.
Proof. vm_refl. Qed.
Lemma D_2705c0 : decode_any W_2705c0 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705c4 : bv 32 := 0x05843a03.
Lemma F_2705c4 : fetch_word Plain.M.loaded_segments (0x270608 : word) = Some W_2705c4.
Proof. vm_refl. Qed.
Lemma D_2705c4 : decode_any W_2705c4 = Some (Load SZ8 true 20 8 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705c8 : bv 32 := 0x01010513.
Lemma F_2705c8 : fetch_word Plain.M.loaded_segments (0x27060c : word) = Some W_2705c8.
Proof. vm_refl. Qed.
Lemma D_2705c8 : decode_any W_2705c8 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705cc : bv 32 := 0x02043023.
Lemma F_2705cc : fetch_word Plain.M.loaded_segments (0x270610 : word) = Some W_2705cc.
Proof. vm_refl. Qed.
Lemma D_2705cc : decode_any W_2705cc = Some (Store SZ8 8 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705d0 : bv 32 := 0x02043423.
Lemma F_2705d0 : fetch_word Plain.M.loaded_segments (0x270614 : word) = Some W_2705d0.
Proof. vm_refl. Qed.
Lemma D_2705d0 : decode_any W_2705d0 = Some (Store SZ8 8 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705d4 : bv 32 := 0x02043c23.
Lemma F_2705d4 : fetch_word Plain.M.loaded_segments (0x270618 : word) = Some W_2705d4.
Proof. vm_refl. Qed.
Lemma D_2705d4 : decode_any W_2705d4 = Some (Store SZ8 8 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705d8 : bv 32 := 0x04a43c23.
Lemma F_2705d8 : fetch_word Plain.M.loaded_segments (0x27061c : word) = Some W_2705d8.
Proof. vm_refl. Qed.
Lemma D_2705d8 : decode_any W_2705d8 = Some (Store SZ8 8 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705dc : bv 32 := 0x05000513.
Lemma F_2705dc : fetch_word Plain.M.loaded_segments (0x270620 : word) = Some W_2705dc.
Proof. vm_refl. Qed.
Lemma D_2705dc : decode_any W_2705dc = Some (OpImm ALU_ADD 10 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705e0 : bv 32 := 0x06a43023.
Lemma F_2705e0 : fetch_word Plain.M.loaded_segments (0x270624 : word) = Some W_2705e0.
Proof. vm_refl. Qed.
Lemma D_2705e0 : decode_any W_2705e0 = Some (Store SZ8 8 10 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705e4 : bv 32 := 0x00040513.
Lemma F_2705e4 : fetch_word Plain.M.loaded_segments (0x270628 : word) = Some W_2705e4.
Proof. vm_refl. Qed.
Lemma D_2705e4 : decode_any W_2705e4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705e8 : bv 32 := 0xfecff0ef.
Lemma F_2705e8 : fetch_word Plain.M.loaded_segments (0x27062c : word) = Some W_2705e8.
Proof. vm_refl. Qed.
Lemma D_2705e8 : decode_any W_2705e8 = Some (Jal 1 2095084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705ec : bv 32 := 0x00050a63.
Lemma F_2705ec : fetch_word Plain.M.loaded_segments (0x270630 : word) = Some W_2705ec.
Proof. vm_refl. Qed.
Lemma D_2705ec : decode_any W_2705ec = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705f0 : bv 32 := 0xfff00493.
Lemma F_2705f0 : fetch_word Plain.M.loaded_segments (0x270634 : word) = Some W_2705f0.
Proof. vm_refl. Qed.
Lemma D_2705f0 : decode_any W_2705f0 = Some (OpImm ALU_ADD 9 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705f4 : bv 32 := 0x020afa93.
Lemma F_2705f4 : fetch_word Plain.M.loaded_segments (0x270638 : word) = Some W_2705f4.
Proof. vm_refl. Qed.
Lemma D_2705f4 : decode_any W_2705f4 = Some (OpImm ALU_AND 21 21 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705f8 : bv 32 := 0x020a1663.
Lemma F_2705f8 : fetch_word Plain.M.loaded_segments (0x27063c : word) = Some W_2705f8.
Proof. vm_refl. Qed.
Lemma D_2705f8 : decode_any W_2705f8 = Some (Branch BC_NE 20 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2705fc : bv 32 := 0x0600006f.
Lemma F_2705fc : fetch_word Plain.M.loaded_segments (0x270640 : word) = Some W_2705fc.
Proof. vm_refl. Qed.
Lemma D_2705fc : decode_any W_2705fc = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270600 : bv 32 := 0x00010613.
Lemma F_270600 : fetch_word Plain.M.loaded_segments (0x270644 : word) = Some W_270600.
Proof. vm_refl. Qed.
Lemma D_270600 : decode_any W_270600 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270604 : bv 32 := 0x06010693.
Lemma F_270604 : fetch_word Plain.M.loaded_segments (0x270648 : word) = Some W_270604.
Proof. vm_refl. Qed.
Lemma D_270604 : decode_any W_270604 = Some (OpImm ALU_ADD 13 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270608 : bv 32 := 0x10810713.
Lemma F_270608 : fetch_word Plain.M.loaded_segments (0x27064c : word) = Some W_270608.
Proof. vm_refl. Qed.
Lemma D_270608 : decode_any W_270608 = Some (OpImm ALU_ADD 14 2 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27060c : bv 32 := 0x00040513.
Lemma F_27060c : fetch_word Plain.M.loaded_segments (0x270650 : word) = Some W_27060c.
Proof. vm_refl. Qed.
Lemma D_27060c : decode_any W_27060c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270610 : bv 32 := 0x00048593.
Lemma F_270610 : fetch_word Plain.M.loaded_segments (0x270654 : word) = Some W_270610.
Proof. vm_refl. Qed.
Lemma D_270610 : decode_any W_270610 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270614 : bv 32 := 0x0ac000ef.
Lemma F_270614 : fetch_word Plain.M.loaded_segments (0x270658 : word) = Some W_270614.
Proof. vm_refl. Qed.
Lemma D_270614 : decode_any W_270614 = Some (Jal 1 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270618 : bv 32 := 0x00050493.
Lemma F_270618 : fetch_word Plain.M.loaded_segments (0x27065c : word) = Some W_270618.
Proof. vm_refl. Qed.
Lemma D_270618 : decode_any W_270618 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27061c : bv 32 := 0x020afa93.
Lemma F_27061c : fetch_word Plain.M.loaded_segments (0x270660 : word) = Some W_27061c.
Proof. vm_refl. Qed.
Lemma D_27061c : decode_any W_27061c = Some (OpImm ALU_AND 21 21 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270620 : bv 32 := 0x020a0e63.
Lemma F_270620 : fetch_word Plain.M.loaded_segments (0x270664 : word) = Some W_270620.
Proof. vm_refl. Qed.
Lemma D_270620 : decode_any W_270620 = Some (Branch BC_EQ 20 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270624 : bv 32 := 0x04843683.
Lemma F_270624 : fetch_word Plain.M.loaded_segments (0x270668 : word) = Some W_270624.
Proof. vm_refl. Qed.
Lemma D_270624 : decode_any W_270624 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270628 : bv 32 := 0x00040513.
Lemma F_270628 : fetch_word Plain.M.loaded_segments (0x27066c : word) = Some W_270628.
Proof. vm_refl. Qed.
Lemma D_270628 : decode_any W_270628 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27062c : bv 32 := 0x00000593.
Lemma F_27062c : fetch_word Plain.M.loaded_segments (0x270670 : word) = Some W_27062c.
Proof. vm_refl. Qed.
Lemma D_27062c : decode_any W_27062c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270630 : bv 32 := 0x00000613.
Lemma F_270630 : fetch_word Plain.M.loaded_segments (0x270674 : word) = Some W_270630.
Proof. vm_refl. Qed.
Lemma D_270630 : decode_any W_270630 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270634 : bv 32 := 0x000680e7.
Lemma F_270634 : fetch_word Plain.M.loaded_segments (0x270678 : word) = Some W_270634.
Proof. vm_refl. Qed.
Lemma D_270634 : decode_any W_270634 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270638 : bv 32 := 0x02843503.
Lemma F_270638 : fetch_word Plain.M.loaded_segments (0x27067c : word) = Some W_270638.
Proof. vm_refl. Qed.
Lemma D_270638 : decode_any W_270638 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27063c : bv 32 := 0x02043023.
Lemma F_27063c : fetch_word Plain.M.loaded_segments (0x270680 : word) = Some W_27063c.
Proof. vm_refl. Qed.
Lemma D_27063c : decode_any W_27063c = Some (Store SZ8 8 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270640 : bv 32 := 0x02043423.
Lemma F_270640 : fetch_word Plain.M.loaded_segments (0x270684 : word) = Some W_270640.
Proof. vm_refl. Qed.
Lemma D_270640 : decode_any W_270640 = Some (Store SZ8 8 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270644 : bv 32 := 0x02043c23.
Lemma F_270644 : fetch_word Plain.M.loaded_segments (0x270688 : word) = Some W_270644.
Proof. vm_refl. Qed.
Lemma D_270644 : decode_any W_270644 = Some (Store SZ8 8 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270648 : bv 32 := 0x05443c23.
Lemma F_270648 : fetch_word Plain.M.loaded_segments (0x27068c : word) = Some W_270648.
Proof. vm_refl. Qed.
Lemma D_270648 : decode_any W_270648 = Some (Store SZ8 8 20 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27064c : bv 32 := 0x00a03533.
Lemma F_27064c : fetch_word Plain.M.loaded_segments (0x270690 : word) = Some W_27064c.
Proof. vm_refl. Qed.
Lemma D_27064c : decode_any W_27064c = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270650 : bv 32 := 0xfff5051b.
Lemma F_270650 : fetch_word Plain.M.loaded_segments (0x270694 : word) = Some W_270650.
Proof. vm_refl. Qed.
Lemma D_270650 : decode_any W_270650 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270654 : bv 32 := 0x009564b3.
Lemma F_270654 : fetch_word Plain.M.loaded_segments (0x270698 : word) = Some W_270654.
Proof. vm_refl. Qed.
Lemma D_270654 : decode_any W_270654 = Some (Op ALU_OR 9 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270658 : bv 32 := 0x06043023.
Lemma F_270658 : fetch_word Plain.M.loaded_segments (0x27069c : word) = Some W_270658.
Proof. vm_refl. Qed.
Lemma D_270658 : decode_any W_270658 = Some (Store SZ8 8 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27065c : bv 32 := 0x00042503.
Lemma F_27065c : fetch_word Plain.M.loaded_segments (0x2706a0 : word) = Some W_27065c.
Proof. vm_refl. Qed.
Lemma D_27065c : decode_any W_27065c = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270660 : bv 32 := 0x02057593.
Lemma F_270660 : fetch_word Plain.M.loaded_segments (0x2706a4 : word) = Some W_270660.
Proof. vm_refl. Qed.
Lemma D_270660 : decode_any W_270660 = Some (OpImm ALU_AND 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270664 : bv 32 := 0x01556633.
Lemma F_270664 : fetch_word Plain.M.loaded_segments (0x2706a8 : word) = Some W_270664.
Proof. vm_refl. Qed.
Lemma D_270664 : decode_any W_270664 = Some (Op ALU_OR 12 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270668 : bv 32 := 0x0015b513.
Lemma F_270668 : fetch_word Plain.M.loaded_segments (0x2706ac : word) = Some W_270668.
Proof. vm_refl. Qed.
Lemma D_270668 : decode_any W_270668 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27066c : bv 32 := 0xfff5051b.
Lemma F_27066c : fetch_word Plain.M.loaded_segments (0x2706b0 : word) = Some W_27066c.
Proof. vm_refl. Qed.
Lemma D_27066c : decode_any W_27066c = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270670 : bv 32 := 0x00956533.
Lemma F_270670 : fetch_word Plain.M.loaded_segments (0x2706b4 : word) = Some W_270670.
Proof. vm_refl. Qed.
Lemma D_270670 : decode_any W_270670 = Some (Op ALU_OR 10 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270674 : bv 32 := 0x00c42023.
Lemma F_270674 : fetch_word Plain.M.loaded_segments (0x2706b8 : word) = Some W_270674.
Proof. vm_refl. Qed.
Lemma D_270674 : decode_any W_270674 = Some (Store SZ4 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270678 : bv 32 := 0x00099a63.
Lemma F_270678 : fetch_word Plain.M.loaded_segments (0x2706bc : word) = Some W_270678.
Proof. vm_refl. Qed.
Lemma D_270678 : decode_any W_270678 = Some (Branch BC_NE 19 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27067c : bv 32 := 0x00050493.
Lemma F_27067c : fetch_word Plain.M.loaded_segments (0x2706c0 : word) = Some W_27067c.
Proof. vm_refl. Qed.
Lemma D_27067c : decode_any W_27067c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270680 : bv 32 := 0x00040513.
Lemma F_270680 : fetch_word Plain.M.loaded_segments (0x2706c4 : word) = Some W_270680.
Proof. vm_refl. Qed.
Lemma D_270680 : decode_any W_270680 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270684 : bv 32 := 0x8c1fe0ef.
Lemma F_270684 : fetch_word Plain.M.loaded_segments (0x2706c8 : word) = Some W_270684.
Proof. vm_refl. Qed.
Lemma D_270684 : decode_any W_270684 = Some (Jal 1 2091200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270688 : bv 32 := 0x00048513.
Lemma F_270688 : fetch_word Plain.M.loaded_segments (0x2706cc : word) = Some W_270688.
Proof. vm_refl. Qed.
Lemma D_270688 : decode_any W_270688 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27068c : bv 32 := 0x00093583.
Lemma F_27068c : fetch_word Plain.M.loaded_segments (0x2706d0 : word) = Some W_27068c.
Proof. vm_refl. Qed.
Lemma D_27068c : decode_any W_27068c = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270690 : bv 32 := 0x13013603.
Lemma F_270690 : fetch_word Plain.M.loaded_segments (0x2706d4 : word) = Some W_270690.
Proof. vm_refl. Qed.
Lemma D_270690 : decode_any W_270690 = Some (Load SZ8 true 12 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270694 : bv 32 := 0x02c59463.
Lemma F_270694 : fetch_word Plain.M.loaded_segments (0x2706d8 : word) = Some W_270694.
Proof. vm_refl. Qed.
Lemma D_270694 : decode_any W_270694 = Some (Branch BC_NE 11 12 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270698 : bv 32 := 0x16813083.
Lemma F_270698 : fetch_word Plain.M.loaded_segments (0x2706dc : word) = Some W_270698.
Proof. vm_refl. Qed.
Lemma D_270698 : decode_any W_270698 = Some (Load SZ8 true 1 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27069c : bv 32 := 0x16013403.
Lemma F_27069c : fetch_word Plain.M.loaded_segments (0x2706e0 : word) = Some W_27069c.
Proof. vm_refl. Qed.
Lemma D_27069c : decode_any W_27069c = Some (Load SZ8 true 8 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706a0 : bv 32 := 0x15813483.
Lemma F_2706a0 : fetch_word Plain.M.loaded_segments (0x2706e4 : word) = Some W_2706a0.
Proof. vm_refl. Qed.
Lemma D_2706a0 : decode_any W_2706a0 = Some (Load SZ8 true 9 2 344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706a4 : bv 32 := 0x15013903.
Lemma F_2706a4 : fetch_word Plain.M.loaded_segments (0x2706e8 : word) = Some W_2706a4.
Proof. vm_refl. Qed.
Lemma D_2706a4 : decode_any W_2706a4 = Some (Load SZ8 true 18 2 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706a8 : bv 32 := 0x14813983.
Lemma F_2706a8 : fetch_word Plain.M.loaded_segments (0x2706ec : word) = Some W_2706a8.
Proof. vm_refl. Qed.
Lemma D_2706a8 : decode_any W_2706a8 = Some (Load SZ8 true 19 2 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706ac : bv 32 := 0x14013a03.
Lemma F_2706ac : fetch_word Plain.M.loaded_segments (0x2706f0 : word) = Some W_2706ac.
Proof. vm_refl. Qed.
Lemma D_2706ac : decode_any W_2706ac = Some (Load SZ8 true 20 2 320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706b0 : bv 32 := 0x13813a83.
Lemma F_2706b0 : fetch_word Plain.M.loaded_segments (0x2706f4 : word) = Some W_2706b0.
Proof. vm_refl. Qed.
Lemma D_2706b0 : decode_any W_2706b0 = Some (Load SZ8 true 21 2 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706b4 : bv 32 := 0x17010113.
Lemma F_2706b4 : fetch_word Plain.M.loaded_segments (0x2706f8 : word) = Some W_2706b4.
Proof. vm_refl. Qed.
Lemma D_2706b4 : decode_any W_2706b4 = Some (OpImm ALU_ADD 2 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706b8 : bv 32 := 0x00008067.
Lemma F_2706b8 : fetch_word Plain.M.loaded_segments (0x2706fc : word) = Some W_2706b8.
Proof. vm_refl. Qed.
Lemma D_2706b8 : decode_any W_2706b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706bc : bv 32 := 0xa9cfb0ef.
Lemma F_2706bc : fetch_word Plain.M.loaded_segments (0x270700 : word) = Some W_2706bc.
Proof. vm_refl. Qed.
Lemma D_2706bc : decode_any W_2706bc = Some (Jal 1 2077340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706c0 : bv 32 := 0xde010113.
Lemma F_2706c0 : fetch_word Plain.M.loaded_segments (0x270704 : word) = Some W_2706c0.
Proof. vm_refl. Qed.
Lemma D_2706c0 : decode_any W_2706c0 = Some (OpImm ALU_ADD 2 2 3552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706c4 : bv 32 := 0x20113c23.
Lemma F_2706c4 : fetch_word Plain.M.loaded_segments (0x270708 : word) = Some W_2706c4.
Proof. vm_refl. Qed.
Lemma D_2706c4 : decode_any W_2706c4 = Some (Store SZ8 2 1 536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706c8 : bv 32 := 0x20813823.
Lemma F_2706c8 : fetch_word Plain.M.loaded_segments (0x27070c : word) = Some W_2706c8.
Proof. vm_refl. Qed.
Lemma D_2706c8 : decode_any W_2706c8 = Some (Store SZ8 2 8 528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706cc : bv 32 := 0x20913423.
Lemma F_2706cc : fetch_word Plain.M.loaded_segments (0x270710 : word) = Some W_2706cc.
Proof. vm_refl. Qed.
Lemma D_2706cc : decode_any W_2706cc = Some (Store SZ8 2 9 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706d0 : bv 32 := 0x21213023.
Lemma F_2706d0 : fetch_word Plain.M.loaded_segments (0x270714 : word) = Some W_2706d0.
Proof. vm_refl. Qed.
Lemma D_2706d0 : decode_any W_2706d0 = Some (Store SZ8 2 18 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706d4 : bv 32 := 0x1f313c23.
Lemma F_2706d4 : fetch_word Plain.M.loaded_segments (0x270718 : word) = Some W_2706d4.
Proof. vm_refl. Qed.
Lemma D_2706d4 : decode_any W_2706d4 = Some (Store SZ8 2 19 504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706d8 : bv 32 := 0x1f413823.
Lemma F_2706d8 : fetch_word Plain.M.loaded_segments (0x27071c : word) = Some W_2706d8.
Proof. vm_refl. Qed.
Lemma D_2706d8 : decode_any W_2706d8 = Some (Store SZ8 2 20 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706dc : bv 32 := 0x1f513423.
Lemma F_2706dc : fetch_word Plain.M.loaded_segments (0x270720 : word) = Some W_2706dc.
Proof. vm_refl. Qed.
Lemma D_2706dc : decode_any W_2706dc = Some (Store SZ8 2 21 488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706e0 : bv 32 := 0x1f613023.
Lemma F_2706e0 : fetch_word Plain.M.loaded_segments (0x270724 : word) = Some W_2706e0.
Proof. vm_refl. Qed.
Lemma D_2706e0 : decode_any W_2706e0 = Some (Store SZ8 2 22 480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706e4 : bv 32 := 0x1d713c23.
Lemma F_2706e4 : fetch_word Plain.M.loaded_segments (0x270728 : word) = Some W_2706e4.
Proof. vm_refl. Qed.
Lemma D_2706e4 : decode_any W_2706e4 = Some (Store SZ8 2 23 472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706e8 : bv 32 := 0x1d813823.
Lemma F_2706e8 : fetch_word Plain.M.loaded_segments (0x27072c : word) = Some W_2706e8.
Proof. vm_refl. Qed.
Lemma D_2706e8 : decode_any W_2706e8 = Some (Store SZ8 2 24 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706ec : bv 32 := 0x1d913423.
Lemma F_2706ec : fetch_word Plain.M.loaded_segments (0x270730 : word) = Some W_2706ec.
Proof. vm_refl. Qed.
Lemma D_2706ec : decode_any W_2706ec = Some (Store SZ8 2 25 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706f0 : bv 32 := 0x1da13023.
Lemma F_2706f0 : fetch_word Plain.M.loaded_segments (0x270734 : word) = Some W_2706f0.
Proof. vm_refl. Qed.
Lemma D_2706f0 : decode_any W_2706f0 = Some (Store SZ8 2 26 448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706f4 : bv 32 := 0x1bb13c23.
Lemma F_2706f4 : fetch_word Plain.M.loaded_segments (0x270738 : word) = Some W_2706f4.
Proof. vm_refl. Qed.
Lemma D_2706f4 : decode_any W_2706f4 = Some (Store SZ8 2 27 440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706f8 : bv 32 := 0x04e13023.
Lemma F_2706f8 : fetch_word Plain.M.loaded_segments (0x27073c : word) = Some W_2706f8.
Proof. vm_refl. Qed.
Lemma D_2706f8 : decode_any W_2706f8 = Some (Store SZ8 2 14 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2706fc : bv 32 := 0x02d13c23.
Lemma F_2706fc : fetch_word Plain.M.loaded_segments (0x270740 : word) = Some W_2706fc.
Proof. vm_refl. Qed.
Lemma D_2706fc : decode_any W_2706fc = Some (Store SZ8 2 13 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270700 : bv 32 := 0x04c13423.
Lemma F_270700 : fetch_word Plain.M.loaded_segments (0x270744 : word) = Some W_270700.
Proof. vm_refl. Qed.
Lemma D_270700 : decode_any W_270700 = Some (Store SZ8 2 12 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270704 : bv 32 := 0x00058a93.
Lemma F_270704 : fetch_word Plain.M.loaded_segments (0x270748 : word) = Some W_270704.
Proof. vm_refl. Qed.
Lemma D_270704 : decode_any W_270704 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270708 : bv 32 := 0x00050a13.
Lemma F_270708 : fetch_word Plain.M.loaded_segments (0x27074c : word) = Some W_270708.
Proof. vm_refl. Qed.
Lemma D_270708 : decode_any W_270708 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27070c : bv 32 := 0x04013c23.
Lemma F_27070c : fetch_word Plain.M.loaded_segments (0x270750 : word) = Some W_27070c.
Proof. vm_refl. Qed.
Lemma D_27070c : decode_any W_27070c = Some (Store SZ8 2 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270710 : bv 32 := 0x00000993.
Lemma F_270710 : fetch_word Plain.M.loaded_segments (0x270754 : word) = Some W_270710.
Proof. vm_refl. Qed.
Lemma D_270710 : decode_any W_270710 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270714 : bv 32 := 0x00000d13.
Lemma F_270714 : fetch_word Plain.M.loaded_segments (0x270758 : word) = Some W_270714.
Proof. vm_refl. Qed.
Lemma D_270714 : decode_any W_270714 = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270718 : bv 32 := 0x00067517.
Lemma F_270718 : fetch_word Plain.M.loaded_segments (0x27075c : word) = Some W_270718.
Proof. vm_refl. Qed.
Lemma D_270718 : decode_any W_270718 = Some (Auipc 10 103, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27071c : bv 32 := 0x800004b7.
Lemma F_27071c : fetch_word Plain.M.loaded_segments (0x270760 : word) = Some W_27071c.
Proof. vm_refl. Qed.
Lemma D_27071c : decode_any W_27071c = Some (Lui 9 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270720 : bv 32 := 0x000135b7.
Lemma F_270720 : fetch_word Plain.M.loaded_segments (0x270764 : word) = Some W_270720.
Proof. vm_refl. Qed.
Lemma D_270720 : decode_any W_270720 = Some (Lui 11 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270724 : bv 32 := 0x44453603.
Lemma F_270724 : fetch_word Plain.M.loaded_segments (0x270768 : word) = Some W_270724.
Proof. vm_refl. Qed.
Lemma D_270724 : decode_any W_270724 = Some (Load SZ8 true 12 10 1092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270728 : bv 32 := 0x0cccd537.
Lemma F_270728 : fetch_word Plain.M.loaded_segments (0x27076c : word) = Some W_270728.
Proof. vm_refl. Qed.
Lemma D_270728 : decode_any W_270728 = Some (Lui 10 52429, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27072c : bv 32 := 0x06c13023.
Lemma F_27072c : fetch_word Plain.M.loaded_segments (0x270770 : word) = Some W_27072c.
Proof. vm_refl. Qed.
Lemma D_27072c : decode_any W_27072c = Some (Store SZ8 2 12 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270730 : bv 32 := 0x00063603.
Lemma F_270730 : fetch_word Plain.M.loaded_segments (0x270774 : word) = Some W_270730.
Proof. vm_refl. Qed.
Lemma D_270730 : decode_any W_270730 = Some (Load SZ8 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270734 : bv 32 := 0xffff06b7.
Lemma F_270734 : fetch_word Plain.M.loaded_segments (0x270778 : word) = Some W_270734.
Proof. vm_refl. Qed.
Lemma D_270734 : decode_any W_270734 = Some (Lui 13 1048560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270738 : bv 32 := 0x1ac13823.
Lemma F_270738 : fetch_word Plain.M.loaded_segments (0x27077c : word) = Some W_270738.
Proof. vm_refl. Qed.
Lemma D_270738 : decode_any W_270738 = Some (Store SZ8 2 12 432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27073c : bv 32 := 0xccccd637.
Lemma F_27073c : fetch_word Plain.M.loaded_segments (0x270780 : word) = Some W_27073c.
Proof. vm_refl. Qed.
Lemma D_27073c : decode_any W_27073c = Some (Lui 12 838861, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270740 : bv 32 := 0xfff4849b.
Lemma F_270740 : fetch_word Plain.M.loaded_segments (0x270784 : word) = Some W_270740.
Proof. vm_refl. Qed.
Lemma D_270740 : decode_any W_270740 = Some (OpImm32 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270744 : bv 32 := 0x8895859b.
Lemma F_270744 : fetch_word Plain.M.loaded_segments (0x270788 : word) = Some W_270744.
Proof. vm_refl. Qed.
Lemma D_270744 : decode_any W_270744 = Some (OpImm32 11 11 2185, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270748 : bv 32 := 0x04b13823.
Lemma F_270748 : fetch_word Plain.M.loaded_segments (0x27078c : word) = Some W_270748.
Proof. vm_refl. Qed.
Lemma D_270748 : decode_any W_270748 = Some (Store SZ8 2 11 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27074c : bv 32 := 0xccc5051b.
Lemma F_27074c : fetch_word Plain.M.loaded_segments (0x270790 : word) = Some W_27074c.
Proof. vm_refl. Qed.
Lemma D_27074c : decode_any W_27074c = Some (OpImm32 10 10 3276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270750 : bv 32 := 0x06a13423.
Lemma F_270750 : fetch_word Plain.M.loaded_segments (0x270794 : word) = Some W_270750.
Proof. vm_refl. Qed.
Lemma D_270750 : decode_any W_270750 = Some (Store SZ8 2 10 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270754 : bv 32 := 0xfff6869b.
Lemma F_270754 : fetch_word Plain.M.loaded_segments (0x270798 : word) = Some W_270754.
Proof. vm_refl. Qed.
Lemma D_270754 : decode_any W_270754 = Some (OpImm32 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270758 : bv 32 := 0x02d13823.
Lemma F_270758 : fetch_word Plain.M.loaded_segments (0x27079c : word) = Some W_270758.
Proof. vm_refl. Qed.
Lemma D_270758 : decode_any W_270758 = Some (Store SZ8 2 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27075c : bv 32 := 0xccd6051b.
Lemma F_27075c : fetch_word Plain.M.loaded_segments (0x2707a0 : word) = Some W_27075c.
Proof. vm_refl. Qed.
Lemma D_27075c : decode_any W_27075c = Some (OpImm32 10 12 3277, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270760 : bv 32 := 0x02a13423.
Lemma F_270760 : fetch_word Plain.M.loaded_segments (0x2707a4 : word) = Some W_270760.
Proof. vm_refl. Qed.
Lemma D_270760 : decode_any W_270760 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270764 : bv 32 := 0x02500413.
Lemma F_270764 : fetch_word Plain.M.loaded_segments (0x2707a8 : word) = Some W_270764.
Proof. vm_refl. Qed.
Lemma D_270764 : decode_any W_270764 = Some (OpImm ALU_ADD 8 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270768 : bv 32 := 0x0080006f.
Lemma F_270768 : fetch_word Plain.M.loaded_segments (0x2707ac : word) = Some W_270768.
Proof. vm_refl. Qed.
Lemma D_270768 : decode_any W_270768 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27076c : bv 32 := 0x0a0b0063.
Lemma F_27076c : fetch_word Plain.M.loaded_segments (0x2707b0 : word) = Some W_27076c.
Proof. vm_refl. Qed.
Lemma D_27076c : decode_any W_27076c = Some (Branch BC_EQ 22 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270770 : bv 32 := 0x4134853b.
Lemma F_270770 : fetch_word Plain.M.loaded_segments (0x2707b4 : word) = Some W_270770.
Proof. vm_refl. Qed.
Lemma D_270770 : decode_any W_270770 = Some (Op32 ALU_SUB 10 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270774 : bv 32 := 0x000d059b.
Lemma F_270774 : fetch_word Plain.M.loaded_segments (0x2707b8 : word) = Some W_270774.
Proof. vm_refl. Qed.
Lemma D_270774 : decode_any W_270774 = Some (OpImm32 11 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270778 : bv 32 := 0x3cb540e3.
Lemma F_270778 : fetch_word Plain.M.loaded_segments (0x2707bc : word) = Some W_270778.
Proof. vm_refl. Qed.
Lemma D_270778 : decode_any W_270778 = Some (Branch BC_LT 10 11 3008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27077c : bv 32 := 0x000a8b93.
Lemma F_27077c : fetch_word Plain.M.loaded_segments (0x2707c0 : word) = Some W_27077c.
Proof. vm_refl. Qed.
Lemma D_27077c : decode_any W_27077c = Some (OpImm ALU_ADD 23 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270780 : bv 32 := 0x000ac503.
Lemma F_270780 : fetch_word Plain.M.loaded_segments (0x2707c4 : word) = Some W_270780.
Proof. vm_refl. Qed.
Lemma D_270780 : decode_any W_270780 = Some (Load SZ1 false 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270784 : bv 32 := 0x013d09bb.
Lemma F_270784 : fetch_word Plain.M.loaded_segments (0x2707c8 : word) = Some W_270784.
Proof. vm_refl. Qed.
Lemma D_270784 : decode_any W_270784 = Some (Op32 ALU_ADD 19 26 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270788 : bv 32 := 0x3a050ee3.
Lemma F_270788 : fetch_word Plain.M.loaded_segments (0x2707cc : word) = Some W_270788.
Proof. vm_refl. Qed.
Lemma D_270788 : decode_any W_270788 = Some (Branch BC_EQ 10 0 3004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27078c : bv 32 := 0x000b8a93.
Lemma F_27078c : fetch_word Plain.M.loaded_segments (0x2707d0 : word) = Some W_27078c.
Proof. vm_refl. Qed.
Lemma D_27078c : decode_any W_27078c = Some (OpImm ALU_ADD 21 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270790 : bv 32 := 0x00050a63.
Lemma F_270790 : fetch_word Plain.M.loaded_segments (0x2707d4 : word) = Some W_270790.
Proof. vm_refl. Qed.
Lemma D_270790 : decode_any W_270790 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270794 : bv 32 := 0x00850c63.
Lemma F_270794 : fetch_word Plain.M.loaded_segments (0x2707d8 : word) = Some W_270794.
Proof. vm_refl. Qed.
Lemma D_270794 : decode_any W_270794 = Some (Branch BC_EQ 10 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270798 : bv 32 := 0x001ac503.
Lemma F_270798 : fetch_word Plain.M.loaded_segments (0x2707dc : word) = Some W_270798.
Proof. vm_refl. Qed.
Lemma D_270798 : decode_any W_270798 = Some (Load SZ1 false 10 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27079c : bv 32 := 0x001a8a93.
Lemma F_27079c : fetch_word Plain.M.loaded_segments (0x2707e0 : word) = Some W_27079c.
Proof. vm_refl. Qed.
Lemma D_27079c : decode_any W_27079c = Some (OpImm ALU_ADD 21 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707a0 : bv 32 := 0xfe051ae3.
Lemma F_2707a0 : fetch_word Plain.M.loaded_segments (0x2707e4 : word) = Some W_2707a0.
Proof. vm_refl. Qed.
Lemma D_2707a0 : decode_any W_2707a0 = Some (Branch BC_NE 10 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707a4 : bv 32 := 0x000a8513.
Lemma F_2707a4 : fetch_word Plain.M.loaded_segments (0x2707e8 : word) = Some W_2707a4.
Proof. vm_refl. Qed.
Lemma D_2707a4 : decode_any W_2707a4 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707a8 : bv 32 := 0x0300006f.
Lemma F_2707a8 : fetch_word Plain.M.loaded_segments (0x2707ec : word) = Some W_2707a8.
Proof. vm_refl. Qed.
Lemma D_2707a8 : decode_any W_2707a8 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707ac : bv 32 := 0x000a8513.
Lemma F_2707ac : fetch_word Plain.M.loaded_segments (0x2707f0 : word) = Some W_2707ac.
Proof. vm_refl. Qed.
Lemma D_2707ac : decode_any W_2707ac = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707b0 : bv 32 := 0x000a8593.
Lemma F_2707b0 : fetch_word Plain.M.loaded_segments (0x2707f4 : word) = Some W_2707b0.
Proof. vm_refl. Qed.
Lemma D_2707b0 : decode_any W_2707b0 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707b4 : bv 32 := 0x0015c603.
Lemma F_2707b4 : fetch_word Plain.M.loaded_segments (0x2707f8 : word) = Some W_2707b4.
Proof. vm_refl. Qed.
Lemma D_2707b4 : decode_any W_2707b4 = Some (Load SZ1 false 12 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707b8 : bv 32 := 0x00861e63.
Lemma F_2707b8 : fetch_word Plain.M.loaded_segments (0x2707fc : word) = Some W_2707b8.
Proof. vm_refl. Qed.
Lemma D_2707b8 : decode_any W_2707b8 = Some (Branch BC_NE 12 8 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707bc : bv 32 := 0x0025c603.
Lemma F_2707bc : fetch_word Plain.M.loaded_segments (0x270800 : word) = Some W_2707bc.
Proof. vm_refl. Qed.
Lemma D_2707bc : decode_any W_2707bc = Some (Load SZ1 false 12 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707c0 : bv 32 := 0x00258a93.
Lemma F_2707c0 : fetch_word Plain.M.loaded_segments (0x270804 : word) = Some W_2707c0.
Proof. vm_refl. Qed.
Lemma D_2707c0 : decode_any W_2707c0 = Some (OpImm ALU_ADD 21 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707c4 : bv 32 := 0x00150513.
Lemma F_2707c4 : fetch_word Plain.M.loaded_segments (0x270808 : word) = Some W_2707c4.
Proof. vm_refl. Qed.
Lemma D_2707c4 : decode_any W_2707c4 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707c8 : bv 32 := 0x000a8593.
Lemma F_2707c8 : fetch_word Plain.M.loaded_segments (0x27080c : word) = Some W_2707c8.
Proof. vm_refl. Qed.
Lemma D_2707c8 : decode_any W_2707c8 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707cc : bv 32 := 0xfe8604e3.
Lemma F_2707cc : fetch_word Plain.M.loaded_segments (0x270810 : word) = Some W_2707cc.
Proof. vm_refl. Qed.
Lemma D_2707cc : decode_any W_2707cc = Some (Branch BC_EQ 12 8 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707d0 : bv 32 := 0x0080006f.
Lemma F_2707d0 : fetch_word Plain.M.loaded_segments (0x270814 : word) = Some W_2707d0.
Proof. vm_refl. Qed.
Lemma D_2707d0 : decode_any W_2707d0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707d4 : bv 32 := 0x00058a93.
Lemma F_2707d4 : fetch_word Plain.M.loaded_segments (0x270818 : word) = Some W_2707d4.
Proof. vm_refl. Qed.
Lemma D_2707d4 : decode_any W_2707d4 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707d8 : bv 32 := 0x41750d33.
Lemma F_2707d8 : fetch_word Plain.M.loaded_segments (0x27081c : word) = Some W_2707d8.
Proof. vm_refl. Qed.
Lemma D_2707d8 : decode_any W_2707d8 = Some (Op ALU_SUB 26 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707dc : bv 32 := 0x4134893b.
Lemma F_2707dc : fetch_word Plain.M.loaded_segments (0x270820 : word) = Some W_2707dc.
Proof. vm_refl. Qed.
Lemma D_2707dc : decode_any W_2707dc = Some (Op32 ALU_SUB 18 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707e0 : bv 32 := 0x35a94ce3.
Lemma F_2707e0 : fetch_word Plain.M.loaded_segments (0x270824 : word) = Some W_2707e0.
Proof. vm_refl. Qed.
Lemma D_2707e0 : decode_any W_2707e0 = Some (Branch BC_LT 18 26 2904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707e4 : bv 32 := 0x000d0b1b.
Lemma F_2707e4 : fetch_word Plain.M.loaded_segments (0x270828 : word) = Some W_2707e4.
Proof. vm_refl. Qed.
Lemma D_2707e4 : decode_any W_2707e4 = Some (OpImm32 22 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707e8 : bv 32 := 0xf80a02e3.
Lemma F_2707e8 : fetch_word Plain.M.loaded_segments (0x27082c : word) = Some W_2707e8.
Proof. vm_refl. Qed.
Lemma D_2707e8 : decode_any W_2707e8 = Some (Branch BC_EQ 20 0 8068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707ec : bv 32 := 0x000a4503.
Lemma F_2707ec : fetch_word Plain.M.loaded_segments (0x270830 : word) = Some W_2707ec.
Proof. vm_refl. Qed.
Lemma D_2707ec : decode_any W_2707ec = Some (Load SZ1 false 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707f0 : bv 32 := 0x02057513.
Lemma F_2707f0 : fetch_word Plain.M.loaded_segments (0x270834 : word) = Some W_2707f0.
Proof. vm_refl. Qed.
Lemma D_2707f0 : decode_any W_2707f0 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707f4 : bv 32 := 0xf6051ce3.
Lemma F_2707f4 : fetch_word Plain.M.loaded_segments (0x270838 : word) = Some W_2707f4.
Proof. vm_refl. Qed.
Lemma D_2707f4 : decode_any W_2707f4 = Some (Branch BC_NE 10 0 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707f8 : bv 32 := 0x000b8513.
Lemma F_2707f8 : fetch_word Plain.M.loaded_segments (0x27083c : word) = Some W_2707f8.
Proof. vm_refl. Qed.
Lemma D_2707f8 : decode_any W_2707f8 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2707fc : bv 32 := 0x000b0593.
Lemma F_2707fc : fetch_word Plain.M.loaded_segments (0x270840 : word) = Some W_2707fc.
Proof. vm_refl. Qed.
Lemma D_2707fc : decode_any W_2707fc = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270800 : bv 32 := 0x000a0613.
Lemma F_270800 : fetch_word Plain.M.loaded_segments (0x270844 : word) = Some W_270800.
Proof. vm_refl. Qed.
Lemma D_270800 : decode_any W_270800 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270804 : bv 32 := 0x9a1ff0ef.
Lemma F_270804 : fetch_word Plain.M.loaded_segments (0x270848 : word) = Some W_270804.
Proof. vm_refl. Qed.
Lemma D_270804 : decode_any W_270804 = Some (Jal 1 2095520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270808 : bv 32 := 0xf65ff06f.
Lemma F_270808 : fetch_word Plain.M.loaded_segments (0x27084c : word) = Some W_270808.
Proof. vm_refl. Qed.
Lemma D_270808 : decode_any W_270808 = Some (Jal 0 2096996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27080c : bv 32 := 0x001ac583.
Lemma F_27080c : fetch_word Plain.M.loaded_segments (0x270850 : word) = Some W_27080c.
Proof. vm_refl. Qed.
Lemma D_27080c : decode_any W_27080c = Some (Load SZ1 false 11 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270810 : bv 32 := 0x001a8613.
Lemma F_270810 : fetch_word Plain.M.loaded_segments (0x270854 : word) = Some W_270810.
Proof. vm_refl. Qed.
Lemma D_270810 : decode_any W_270810 = Some (OpImm ALU_ADD 12 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270814 : bv 32 := 0xfd058693.
Lemma F_270814 : fetch_word Plain.M.loaded_segments (0x270858 : word) = Some W_270814.
Proof. vm_refl. Qed.
Lemma D_270814 : decode_any W_270814 = Some (OpImm ALU_ADD 13 11 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270818 : bv 32 := 0xfff00513.
Lemma F_270818 : fetch_word Plain.M.loaded_segments (0x27085c : word) = Some W_270818.
Proof. vm_refl. Qed.
Lemma D_270818 : decode_any W_270818 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27081c : bv 32 := 0x00900713.
Lemma F_27081c : fetch_word Plain.M.loaded_segments (0x270860 : word) = Some W_27081c.
Proof. vm_refl. Qed.
Lemma D_27081c : decode_any W_27081c = Some (OpImm ALU_ADD 14 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270820 : bv 32 := 0x02d76863.
Lemma F_270820 : fetch_word Plain.M.loaded_segments (0x270864 : word) = Some W_270820.
Proof. vm_refl. Qed.
Lemma D_270820 : decode_any W_270820 = Some (Branch BC_LTU 14 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270824 : bv 32 := 0x002ac703.
Lemma F_270824 : fetch_word Plain.M.loaded_segments (0x270868 : word) = Some W_270824.
Proof. vm_refl. Qed.
Lemma D_270824 : decode_any W_270824 = Some (Load SZ1 false 14 21 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270828 : bv 32 := 0x02400793.
Lemma F_270828 : fetch_word Plain.M.loaded_segments (0x27086c : word) = Some W_270828.
Proof. vm_refl. Qed.
Lemma D_270828 : decode_any W_270828 = Some (OpImm ALU_ADD 15 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27082c : bv 32 := 0x00100813.
Lemma F_27082c : fetch_word Plain.M.loaded_segments (0x270870 : word) = Some W_27082c.
Proof. vm_refl. Qed.
Lemma D_27082c : decode_any W_27082c = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270830 : bv 32 := 0x05013283.
Lemma F_270830 : fetch_word Plain.M.loaded_segments (0x270874 : word) = Some W_270830.
Proof. vm_refl. Qed.
Lemma D_270830 : decode_any W_270830 = Some (Load SZ8 true 5 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270834 : bv 32 := 0x02f71263.
Lemma F_270834 : fetch_word Plain.M.loaded_segments (0x270878 : word) = Some W_270834.
Proof. vm_refl. Qed.
Lemma D_270834 : decode_any W_270834 = Some (Branch BC_NE 14 15 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270838 : bv 32 := 0x003ac583.
Lemma F_270838 : fetch_word Plain.M.loaded_segments (0x27087c : word) = Some W_270838.
Proof. vm_refl. Qed.
Lemma D_270838 : decode_any W_270838 = Some (Load SZ1 false 11 21 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27083c : bv 32 := 0x003a8613.
Lemma F_27083c : fetch_word Plain.M.loaded_segments (0x270880 : word) = Some W_27083c.
Proof. vm_refl. Qed.
Lemma D_27083c : decode_any W_27083c = Some (OpImm ALU_ADD 12 21 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270840 : bv 32 := 0x00100513.
Lemma F_270840 : fetch_word Plain.M.loaded_segments (0x270884 : word) = Some W_270840.
Proof. vm_refl. Qed.
Lemma D_270840 : decode_any W_270840 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270844 : bv 32 := 0x04a13c23.
Lemma F_270844 : fetch_word Plain.M.loaded_segments (0x270888 : word) = Some W_270844.
Proof. vm_refl. Qed.
Lemma D_270844 : decode_any W_270844 = Some (Store SZ8 2 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270848 : bv 32 := 0x00068513.
Lemma F_270848 : fetch_word Plain.M.loaded_segments (0x27088c : word) = Some W_270848.
Proof. vm_refl. Qed.
Lemma D_270848 : decode_any W_270848 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27084c : bv 32 := 0x00c0006f.
Lemma F_27084c : fetch_word Plain.M.loaded_segments (0x270890 : word) = Some W_27084c.
Proof. vm_refl. Qed.
Lemma D_27084c : decode_any W_27084c = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270850 : bv 32 := 0x00100813.
Lemma F_270850 : fetch_word Plain.M.loaded_segments (0x270894 : word) = Some W_270850.
Proof. vm_refl. Qed.
Lemma D_270850 : decode_any W_270850 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270854 : bv 32 := 0x05013283.
Lemma F_270854 : fetch_word Plain.M.loaded_segments (0x270898 : word) = Some W_270854.
Proof. vm_refl. Qed.
Lemma D_270854 : decode_any W_270854 = Some (Load SZ8 true 5 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270858 : bv 32 := 0xfe058693.
Lemma F_270858 : fetch_word Plain.M.loaded_segments (0x27089c : word) = Some W_270858.
Proof. vm_refl. Qed.
Lemma D_270858 : decode_any W_270858 = Some (OpImm ALU_ADD 13 11 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27085c : bv 32 := 0x01f00713.
Lemma F_27085c : fetch_word Plain.M.loaded_segments (0x2708a0 : word) = Some W_27085c.
Proof. vm_refl. Qed.
Lemma D_27085c : decode_any W_27085c = Some (OpImm ALU_ADD 14 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270860 : bv 32 := 0x06d76e63.
Lemma F_270860 : fetch_word Plain.M.loaded_segments (0x2708a4 : word) = Some W_270860.
Proof. vm_refl. Qed.
Lemma D_270860 : decode_any W_270860 = Some (Branch BC_LTU 14 13 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270864 : bv 32 := 0x00d816bb.
Lemma F_270864 : fetch_word Plain.M.loaded_segments (0x2708a8 : word) = Some W_270864.
Proof. vm_refl. Qed.
Lemma D_270864 : decode_any W_270864 = Some (Op32 ALU_SLL 13 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270868 : bv 32 := 0x0056f733.
Lemma F_270868 : fetch_word Plain.M.loaded_segments (0x2708ac : word) = Some W_270868.
Proof. vm_refl. Qed.
Lemma D_270868 : decode_any W_270868 = Some (Op ALU_AND 14 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27086c : bv 32 := 0x02000893.
Lemma F_27086c : fetch_word Plain.M.loaded_segments (0x2708b0 : word) = Some W_27086c.
Proof. vm_refl. Qed.
Lemma D_27086c : decode_any W_27086c = Some (OpImm ALU_ADD 17 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270870 : bv 32 := 0x00000c13.
Lemma F_270870 : fetch_word Plain.M.loaded_segments (0x2708b4 : word) = Some W_270870.
Proof. vm_refl. Qed.
Lemma D_270870 : decode_any W_270870 = Some (OpImm ALU_ADD 24 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270874 : bv 32 := 0x02070663.
Lemma F_270874 : fetch_word Plain.M.loaded_segments (0x2708b8 : word) = Some W_270874.
Proof. vm_refl. Qed.
Lemma D_270874 : decode_any W_270874 = Some (Branch BC_EQ 14 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270878 : bv 32 := 0x00160713.
Lemma F_270878 : fetch_word Plain.M.loaded_segments (0x2708bc : word) = Some W_270878.
Proof. vm_refl. Qed.
Lemma D_270878 : decode_any W_270878 = Some (OpImm ALU_ADD 14 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27087c : bv 32 := 0x00070613.
Lemma F_27087c : fetch_word Plain.M.loaded_segments (0x2708c0 : word) = Some W_27087c.
Proof. vm_refl. Qed.
Lemma D_27087c : decode_any W_27087c = Some (OpImm ALU_ADD 12 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270880 : bv 32 := 0x00074583.
Lemma F_270880 : fetch_word Plain.M.loaded_segments (0x2708c4 : word) = Some W_270880.
Proof. vm_refl. Qed.
Lemma D_270880 : decode_any W_270880 = Some (Load SZ1 false 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270884 : bv 32 := 0xfe058713.
Lemma F_270884 : fetch_word Plain.M.loaded_segments (0x2708c8 : word) = Some W_270884.
Proof. vm_refl. Qed.
Lemma D_270884 : decode_any W_270884 = Some (OpImm ALU_ADD 14 11 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270888 : bv 32 := 0x0186ec33.
Lemma F_270888 : fetch_word Plain.M.loaded_segments (0x2708cc : word) = Some W_270888.
Proof. vm_refl. Qed.
Lemma D_270888 : decode_any W_270888 = Some (Op ALU_OR 24 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27088c : bv 32 := 0x01177a63.
Lemma F_27088c : fetch_word Plain.M.loaded_segments (0x2708d0 : word) = Some W_27088c.
Proof. vm_refl. Qed.
Lemma D_27088c : decode_any W_27088c = Some (Branch BC_GEU 14 17 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270890 : bv 32 := 0x00e816bb.
Lemma F_270890 : fetch_word Plain.M.loaded_segments (0x2708d4 : word) = Some W_270890.
Proof. vm_refl. Qed.
Lemma D_270890 : decode_any W_270890 = Some (Op32 ALU_SLL 13 16 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270894 : bv 32 := 0x0056f7b3.
Lemma F_270894 : fetch_word Plain.M.loaded_segments (0x2708d8 : word) = Some W_270894.
Proof. vm_refl. Qed.
Lemma D_270894 : decode_any W_270894 = Some (Op ALU_AND 15 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270898 : bv 32 := 0x00160713.
Lemma F_270898 : fetch_word Plain.M.loaded_segments (0x2708dc : word) = Some W_270898.
Proof. vm_refl. Qed.
Lemma D_270898 : decode_any W_270898 = Some (OpImm ALU_ADD 14 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27089c : bv 32 := 0xfe0790e3.
Lemma F_27089c : fetch_word Plain.M.loaded_segments (0x2708e0 : word) = Some W_27089c.
Proof. vm_refl. Qed.
Lemma D_27089c : decode_any W_27089c = Some (Branch BC_NE 15 0 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708a0 : bv 32 := 0x02a00693.
Lemma F_2708a0 : fetch_word Plain.M.loaded_segments (0x2708e4 : word) = Some W_2708a0.
Proof. vm_refl. Qed.
Lemma D_2708a0 : decode_any W_2708a0 = Some (OpImm ALU_ADD 13 0 42, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708a4 : bv 32 := 0x04d59263.
Lemma F_2708a4 : fetch_word Plain.M.loaded_segments (0x2708e8 : word) = Some W_2708a4.
Proof. vm_refl. Qed.
Lemma D_2708a4 : decode_any W_2708a4 = Some (Branch BC_NE 11 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708a8 : bv 32 := 0x00164583.
Lemma F_2708a8 : fetch_word Plain.M.loaded_segments (0x2708ec : word) = Some W_2708a8.
Proof. vm_refl. Qed.
Lemma D_2708a8 : decode_any W_2708a8 = Some (Load SZ1 false 11 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708ac : bv 32 := 0xfd058593.
Lemma F_2708ac : fetch_word Plain.M.loaded_segments (0x2708f0 : word) = Some W_2708ac.
Proof. vm_refl. Qed.
Lemma D_2708ac : decode_any W_2708ac = Some (OpImm ALU_ADD 11 11 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708b0 : bv 32 := 0x00900693.
Lemma F_2708b0 : fetch_word Plain.M.loaded_segments (0x2708f4 : word) = Some W_2708b0.
Proof. vm_refl. Qed.
Lemma D_2708b0 : decode_any W_2708b0 = Some (OpImm ALU_ADD 13 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708b4 : bv 32 := 0x0ab6e263.
Lemma F_2708b4 : fetch_word Plain.M.loaded_segments (0x2708f8 : word) = Some W_2708b4.
Proof. vm_refl. Qed.
Lemma D_2708b4 : decode_any W_2708b4 = Some (Branch BC_LTU 13 11 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708b8 : bv 32 := 0x00264683.
Lemma F_2708b8 : fetch_word Plain.M.loaded_segments (0x2708fc : word) = Some W_2708b8.
Proof. vm_refl. Qed.
Lemma D_2708b8 : decode_any W_2708b8 = Some (Load SZ1 false 13 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708bc : bv 32 := 0x02400713.
Lemma F_2708bc : fetch_word Plain.M.loaded_segments (0x270900 : word) = Some W_2708bc.
Proof. vm_refl. Qed.
Lemma D_2708bc : decode_any W_2708bc = Some (OpImm ALU_ADD 14 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708c0 : bv 32 := 0x08e69c63.
Lemma F_2708c0 : fetch_word Plain.M.loaded_segments (0x270904 : word) = Some W_2708c0.
Proof. vm_refl. Qed.
Lemma D_2708c0 : decode_any W_2708c0 = Some (Branch BC_NE 13 14 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708c4 : bv 32 := 0x0c0a0c63.
Lemma F_2708c4 : fetch_word Plain.M.loaded_segments (0x270908 : word) = Some W_2708c4.
Proof. vm_refl. Qed.
Lemma D_2708c4 : decode_any W_2708c4 = Some (Branch BC_EQ 20 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708c8 : bv 32 := 0x00459593.
Lemma F_2708c8 : fetch_word Plain.M.loaded_segments (0x27090c : word) = Some W_2708c8.
Proof. vm_refl. Qed.
Lemma D_2708c8 : decode_any W_2708c8 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708cc : bv 32 := 0x03813683.
Lemma F_2708cc : fetch_word Plain.M.loaded_segments (0x270910 : word) = Some W_2708cc.
Proof. vm_refl. Qed.
Lemma D_2708cc : decode_any W_2708cc = Some (Load SZ8 true 13 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708d0 : bv 32 := 0x00b685b3.
Lemma F_2708d0 : fetch_word Plain.M.loaded_segments (0x270914 : word) = Some W_2708d0.
Proof. vm_refl. Qed.
Lemma D_2708d0 : decode_any W_2708d0 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708d4 : bv 32 := 0x0005ab03.
Lemma F_2708d4 : fetch_word Plain.M.loaded_segments (0x270918 : word) = Some W_2708d4.
Proof. vm_refl. Qed.
Lemma D_2708d4 : decode_any W_2708d4 = Some (Load SZ4 true 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708d8 : bv 32 := 0x0dc0006f.
Lemma F_2708d8 : fetch_word Plain.M.loaded_segments (0x27091c : word) = Some W_2708d8.
Proof. vm_refl. Qed.
Lemma D_2708d8 : decode_any W_2708d8 = Some (Jal 0 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708dc : bv 32 := 0x00000c13.
Lemma F_2708dc : fetch_word Plain.M.loaded_segments (0x270920 : word) = Some W_2708dc.
Proof. vm_refl. Qed.
Lemma D_2708dc : decode_any W_2708dc = Some (OpImm ALU_ADD 24 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708e0 : bv 32 := 0x02a00693.
Lemma F_2708e0 : fetch_word Plain.M.loaded_segments (0x270924 : word) = Some W_2708e0.
Proof. vm_refl. Qed.
Lemma D_2708e0 : decode_any W_2708e0 = Some (OpImm ALU_ADD 13 0 42, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708e4 : bv 32 := 0xfcd582e3.
Lemma F_2708e4 : fetch_word Plain.M.loaded_segments (0x270928 : word) = Some W_2708e4.
Proof. vm_refl. Qed.
Lemma D_2708e4 : decode_any W_2708e4 = Some (Branch BC_EQ 11 13 8132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708e8 : bv 32 := 0xfd058593.
Lemma F_2708e8 : fetch_word Plain.M.loaded_segments (0x27092c : word) = Some W_2708e8.
Proof. vm_refl. Qed.
Lemma D_2708e8 : decode_any W_2708e8 = Some (OpImm ALU_ADD 11 11 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708ec : bv 32 := 0x00000b13.
Lemma F_2708ec : fetch_word Plain.M.loaded_segments (0x270930 : word) = Some W_2708ec.
Proof. vm_refl. Qed.
Lemma D_2708ec : decode_any W_2708ec = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708f0 : bv 32 := 0x00900693.
Lemma F_2708f0 : fetch_word Plain.M.loaded_segments (0x270934 : word) = Some W_2708f0.
Proof. vm_refl. Qed.
Lemma D_2708f0 : decode_any W_2708f0 = Some (OpImm ALU_ADD 13 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708f4 : bv 32 := 0x0cb6ee63.
Lemma F_2708f4 : fetch_word Plain.M.loaded_segments (0x270938 : word) = Some W_2708f4.
Proof. vm_refl. Qed.
Lemma D_2708f4 : decode_any W_2708f4 = Some (Branch BC_LTU 13 11 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708f8 : bv 32 := 0x00060693.
Lemma F_2708f8 : fetch_word Plain.M.loaded_segments (0x27093c : word) = Some W_2708f8.
Proof. vm_refl. Qed.
Lemma D_2708f8 : decode_any W_2708f8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2708fc : bv 32 := 0x0380006f.
Lemma F_2708fc : fetch_word Plain.M.loaded_segments (0x270940 : word) = Some W_2708fc.
Proof. vm_refl. Qed.
Lemma D_2708fc : decode_any W_2708fc = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270900 : bv 32 := 0x00a00313.
Lemma F_270900 : fetch_word Plain.M.loaded_segments (0x270944 : word) = Some W_270900.
Proof. vm_refl. Qed.
Lemma D_270900 : decode_any W_270900 = Some (OpImm ALU_ADD 6 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270904 : bv 32 := 0x026b063b.
Lemma F_270904 : fetch_word Plain.M.loaded_segments (0x270948 : word) = Some W_270904.
Proof. vm_refl. Qed.
Lemma D_270904 : decode_any W_270904 = Some (Mul32 M_MUL 12 22 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270908 : bv 32 := 0x0005871b.
Lemma F_270908 : fetch_word Plain.M.loaded_segments (0x27094c : word) = Some W_270908.
Proof. vm_refl. Qed.
Lemma D_270908 : decode_any W_270908 = Some (OpImm32 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27090c : bv 32 := 0x0016c803.
Lemma F_27090c : fetch_word Plain.M.loaded_segments (0x270950 : word) = Some W_27090c.
Proof. vm_refl. Qed.
Lemma D_27090c : decode_any W_27090c = Some (Load SZ1 false 16 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270910 : bv 32 := 0x009647b3.
Lemma F_270910 : fetch_word Plain.M.loaded_segments (0x270954 : word) = Some W_270910.
Proof. vm_refl. Qed.
Lemma D_270910 : decode_any W_270910 = Some (Op ALU_XOR 15 12 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270914 : bv 32 := 0x00b608bb.
Lemma F_270914 : fetch_word Plain.M.loaded_segments (0x270958 : word) = Some W_270914.
Proof. vm_refl. Qed.
Lemma D_270914 : decode_any W_270914 = Some (Op32 ALU_ADD 17 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270918 : bv 32 := 0x00e7b5b3.
Lemma F_270918 : fetch_word Plain.M.loaded_segments (0x27095c : word) = Some W_270918.
Proof. vm_refl. Qed.
Lemma D_270918 : decode_any W_270918 = Some (Op ALU_SLTU 11 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27091c : bv 32 := 0x40b002bb.
Lemma F_27091c : fetch_word Plain.M.loaded_segments (0x270960 : word) = Some W_27091c.
Proof. vm_refl. Qed.
Lemma D_27091c : decode_any W_27091c = Some (Op32 ALU_SUB 5 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270920 : bv 32 := 0x00168613.
Lemma F_270920 : fetch_word Plain.M.loaded_segments (0x270964 : word) = Some W_270920.
Proof. vm_refl. Qed.
Lemma D_270920 : decode_any W_270920 = Some (OpImm ALU_ADD 12 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270924 : bv 32 := 0xfd080593.
Lemma F_270924 : fetch_word Plain.M.loaded_segments (0x270968 : word) = Some W_270924.
Proof. vm_refl. Qed.
Lemma D_270924 : decode_any W_270924 = Some (OpImm ALU_ADD 11 16 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270928 : bv 32 := 0x0112eb33.
Lemma F_270928 : fetch_word Plain.M.loaded_segments (0x27096c : word) = Some W_270928.
Proof. vm_refl. Qed.
Lemma D_270928 : decode_any W_270928 = Some (Op ALU_OR 22 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27092c : bv 32 := 0x00060693.
Lemma F_27092c : fetch_word Plain.M.loaded_segments (0x270970 : word) = Some W_27092c.
Proof. vm_refl. Qed.
Lemma D_27092c : decode_any W_27092c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270930 : bv 32 := 0x0665f263.
Lemma F_270930 : fetch_word Plain.M.loaded_segments (0x270974 : word) = Some W_270930.
Proof. vm_refl. Qed.
Lemma D_270930 : decode_any W_270930 = Some (Branch BC_GEU 11 6 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270934 : bv 32 := 0x06813603.
Lemma F_270934 : fetch_word Plain.M.loaded_segments (0x270978 : word) = Some W_270934.
Proof. vm_refl. Qed.
Lemma D_270934 : decode_any W_270934 = Some (Load SZ8 true 12 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270938 : bv 32 := 0xfd6674e3.
Lemma F_270938 : fetch_word Plain.M.loaded_segments (0x27097c : word) = Some W_270938.
Proof. vm_refl. Qed.
Lemma D_270938 : decode_any W_270938 = Some (Branch BC_GEU 12 22 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27093c : bv 32 := 0x0016c583.
Lemma F_27093c : fetch_word Plain.M.loaded_segments (0x270980 : word) = Some W_27093c.
Proof. vm_refl. Qed.
Lemma D_27093c : decode_any W_27093c = Some (Load SZ1 false 11 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270940 : bv 32 := 0x00168693.
Lemma F_270940 : fetch_word Plain.M.loaded_segments (0x270984 : word) = Some W_270940.
Proof. vm_refl. Qed.
Lemma D_270940 : decode_any W_270940 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270944 : bv 32 := 0xfd058593.
Lemma F_270944 : fetch_word Plain.M.loaded_segments (0x270988 : word) = Some W_270944.
Proof. vm_refl. Qed.
Lemma D_270944 : decode_any W_270944 = Some (OpImm ALU_ADD 11 11 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270948 : bv 32 := 0xfff00b13.
Lemma F_270948 : fetch_word Plain.M.loaded_segments (0x27098c : word) = Some W_270948.
Proof. vm_refl. Qed.
Lemma D_270948 : decode_any W_270948 = Some (OpImm ALU_ADD 22 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27094c : bv 32 := 0x00a00613.
Lemma F_27094c : fetch_word Plain.M.loaded_segments (0x270990 : word) = Some W_27094c.
Proof. vm_refl. Qed.
Lemma D_27094c : decode_any W_27094c = Some (OpImm ALU_ADD 12 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270950 : bv 32 := 0xfec5e2e3.
Lemma F_270950 : fetch_word Plain.M.loaded_segments (0x270994 : word) = Some W_270950.
Proof. vm_refl. Qed.
Lemma D_270950 : decode_any W_270950 = Some (Branch BC_LTU 11 12 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270954 : bv 32 := 0x1e50006f.
Lemma F_270954 : fetch_word Plain.M.loaded_segments (0x270998 : word) = Some W_270954.
Proof. vm_refl. Qed.
Lemma D_270954 : decode_any W_270954 = Some (Jal 0 2532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270958 : bv 32 := 0x05813583.
Lemma F_270958 : fetch_word Plain.M.loaded_segments (0x27099c : word) = Some W_270958.
Proof. vm_refl. Qed.
Lemma D_270958 : decode_any W_270958 = Some (Load SZ8 true 11 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27095c : bv 32 := 0x320598e3.
Lemma F_27095c : fetch_word Plain.M.loaded_segments (0x2709a0 : word) = Some W_27095c.
Proof. vm_refl. Qed.
Lemma D_27095c : decode_any W_27095c = Some (Branch BC_NE 11 0 2864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270960 : bv 32 := 0x00160613.
Lemma F_270960 : fetch_word Plain.M.loaded_segments (0x2709a4 : word) = Some W_270960.
Proof. vm_refl. Qed.
Lemma D_270960 : decode_any W_270960 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270964 : bv 32 := 0x020a0263.
Lemma F_270964 : fetch_word Plain.M.loaded_segments (0x2709a8 : word) = Some W_270964.
Proof. vm_refl. Qed.
Lemma D_270964 : decode_any W_270964 = Some (Branch BC_EQ 20 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270968 : bv 32 := 0x04813703.
Lemma F_270968 : fetch_word Plain.M.loaded_segments (0x2709ac : word) = Some W_270968.
Proof. vm_refl. Qed.
Lemma D_270968 : decode_any W_270968 = Some (Load SZ8 true 14 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27096c : bv 32 := 0x00073583.
Lemma F_27096c : fetch_word Plain.M.loaded_segments (0x2709b0 : word) = Some W_27096c.
Proof. vm_refl. Qed.
Lemma D_27096c : decode_any W_27096c = Some (Load SZ8 true 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270970 : bv 32 := 0x00858693.
Lemma F_270970 : fetch_word Plain.M.loaded_segments (0x2709b4 : word) = Some W_270970.
Proof. vm_refl. Qed.
Lemma D_270970 : decode_any W_270970 = Some (OpImm ALU_ADD 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270974 : bv 32 := 0x00d73023.
Lemma F_270974 : fetch_word Plain.M.loaded_segments (0x2709b8 : word) = Some W_270974.
Proof. vm_refl. Qed.
Lemma D_270974 : decode_any W_270974 = Some (Store SZ8 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270978 : bv 32 := 0x0005ab03.
Lemma F_270978 : fetch_word Plain.M.loaded_segments (0x2709bc : word) = Some W_270978.
Proof. vm_refl. Qed.
Lemma D_270978 : decode_any W_270978 = Some (Load SZ4 true 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27097c : bv 32 := 0x04013c23.
Lemma F_27097c : fetch_word Plain.M.loaded_segments (0x2709c0 : word) = Some W_27097c.
Proof. vm_refl. Qed.
Lemma D_27097c : decode_any W_27097c = Some (Store SZ8 2 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270980 : bv 32 := 0x040b5863.
Lemma F_270980 : fetch_word Plain.M.loaded_segments (0x2709c4 : word) = Some W_270980.
Proof. vm_refl. Qed.
Lemma D_270980 : decode_any W_270980 = Some (Branch BC_GE 22 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270984 : bv 32 := 0x0400006f.
Lemma F_270984 : fetch_word Plain.M.loaded_segments (0x2709c8 : word) = Some W_270984.
Proof. vm_refl. Qed.
Lemma D_270984 : decode_any W_270984 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270988 : bv 32 := 0x04013c23.
Lemma F_270988 : fetch_word Plain.M.loaded_segments (0x2709cc : word) = Some W_270988.
Proof. vm_refl. Qed.
Lemma D_270988 : decode_any W_270988 = Some (Store SZ8 2 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27098c : bv 32 := 0x00000b13.
Lemma F_27098c : fetch_word Plain.M.loaded_segments (0x2709d0 : word) = Some W_27098c.
Proof. vm_refl. Qed.
Lemma D_27098c : decode_any W_27098c = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270990 : bv 32 := 0x0400006f.
Lemma F_270990 : fetch_word Plain.M.loaded_segments (0x2709d4 : word) = Some W_270990.
Proof. vm_refl. Qed.
Lemma D_270990 : decode_any W_270990 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270994 : bv 32 := 0x02e7fe63.
Lemma F_270994 : fetch_word Plain.M.loaded_segments (0x2709d8 : word) = Some W_270994.
Proof. vm_refl. Qed.
Lemma D_270994 : decode_any W_270994 = Some (Branch BC_GEU 15 14 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270998 : bv 32 := 0x1a10006f.
Lemma F_270998 : fetch_word Plain.M.loaded_segments (0x2709dc : word) = Some W_270998.
Proof. vm_refl. Qed.
Lemma D_270998 : decode_any W_270998 = Some (Jal 0 2464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27099c : bv 32 := 0x00000b13.
Lemma F_27099c : fetch_word Plain.M.loaded_segments (0x2709e0 : word) = Some W_27099c.
Proof. vm_refl. Qed.
Lemma D_27099c : decode_any W_27099c = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709a0 : bv 32 := 0x00259593.
Lemma F_2709a0 : fetch_word Plain.M.loaded_segments (0x2709e4 : word) = Some W_2709a0.
Proof. vm_refl. Qed.
Lemma D_2709a0 : decode_any W_2709a0 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709a4 : bv 32 := 0x04013683.
Lemma F_2709a4 : fetch_word Plain.M.loaded_segments (0x2709e8 : word) = Some W_2709a4.
Proof. vm_refl. Qed.
Lemma D_2709a4 : decode_any W_2709a4 = Some (Load SZ8 true 13 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709a8 : bv 32 := 0x00b685b3.
Lemma F_2709a8 : fetch_word Plain.M.loaded_segments (0x2709ec : word) = Some W_2709a8.
Proof. vm_refl. Qed.
Lemma D_2709a8 : decode_any W_2709a8 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709ac : bv 32 := 0x00a00693.
Lemma F_2709ac : fetch_word Plain.M.loaded_segments (0x2709f0 : word) = Some W_2709ac.
Proof. vm_refl. Qed.
Lemma D_2709ac : decode_any W_2709ac = Some (OpImm ALU_ADD 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709b0 : bv 32 := 0x00d5a023.
Lemma F_2709b0 : fetch_word Plain.M.loaded_segments (0x2709f4 : word) = Some W_2709b0.
Proof. vm_refl. Qed.
Lemma D_2709b0 : decode_any W_2709b0 = Some (Store SZ4 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709b4 : bv 32 := 0x00360613.
Lemma F_2709b4 : fetch_word Plain.M.loaded_segments (0x2709f8 : word) = Some W_2709b4.
Proof. vm_refl. Qed.
Lemma D_2709b4 : decode_any W_2709b4 = Some (OpImm ALU_ADD 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709b8 : bv 32 := 0x00100593.
Lemma F_2709b8 : fetch_word Plain.M.loaded_segments (0x2709fc : word) = Some W_2709b8.
Proof. vm_refl. Qed.
Lemma D_2709b8 : decode_any W_2709b8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709bc : bv 32 := 0x04b13c23.
Lemma F_2709bc : fetch_word Plain.M.loaded_segments (0x270a00 : word) = Some W_2709bc.
Proof. vm_refl. Qed.
Lemma D_2709bc : decode_any W_2709bc = Some (Store SZ8 2 11 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709c0 : bv 32 := 0x000b5863.
Lemma F_2709c0 : fetch_word Plain.M.loaded_segments (0x270a04 : word) = Some W_2709c0.
Proof. vm_refl. Qed.
Lemma D_2709c0 : decode_any W_2709c0 = Some (Branch BC_GE 22 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709c4 : bv 32 := 0x000025b7.
Lemma F_2709c4 : fetch_word Plain.M.loaded_segments (0x270a08 : word) = Some W_2709c4.
Proof. vm_refl. Qed.
Lemma D_2709c4 : decode_any W_2709c4 = Some (Lui 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709c8 : bv 32 := 0x00bc6c33.
Lemma F_2709c8 : fetch_word Plain.M.loaded_segments (0x270a0c : word) = Some W_2709c8.
Proof. vm_refl. Qed.
Lemma D_2709c8 : decode_any W_2709c8 = Some (Op ALU_OR 24 24 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709cc : bv 32 := 0x41600b3b.
Lemma F_2709cc : fetch_word Plain.M.loaded_segments (0x270a10 : word) = Some W_2709cc.
Proof. vm_refl. Qed.
Lemma D_2709cc : decode_any W_2709cc = Some (Op32 ALU_SUB 22 0 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709d0 : bv 32 := 0x00064583.
Lemma F_2709d0 : fetch_word Plain.M.loaded_segments (0x270a14 : word) = Some W_2709d0.
Proof. vm_refl. Qed.
Lemma D_2709d0 : decode_any W_2709d0 = Some (Load SZ1 false 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709d4 : bv 32 := 0x02e00693.
Lemma F_2709d4 : fetch_word Plain.M.loaded_segments (0x270a18 : word) = Some W_2709d4.
Proof. vm_refl. Qed.
Lemma D_2709d4 : decode_any W_2709d4 = Some (OpImm ALU_ADD 13 0 46, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709d8 : bv 32 := 0x04d59863.
Lemma F_2709d8 : fetch_word Plain.M.loaded_segments (0x270a1c : word) = Some W_2709d8.
Proof. vm_refl. Qed.
Lemma D_2709d8 : decode_any W_2709d8 = Some (Branch BC_NE 11 13 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709dc : bv 32 := 0x00164583.
Lemma F_2709dc : fetch_word Plain.M.loaded_segments (0x270a20 : word) = Some W_2709dc.
Proof. vm_refl. Qed.
Lemma D_2709dc : decode_any W_2709dc = Some (Load SZ1 false 11 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709e0 : bv 32 := 0x02a00693.
Lemma F_2709e0 : fetch_word Plain.M.loaded_segments (0x270a24 : word) = Some W_2709e0.
Proof. vm_refl. Qed.
Lemma D_2709e0 : decode_any W_2709e0 = Some (OpImm ALU_ADD 13 0 42, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709e4 : bv 32 := 0x04d59e63.
Lemma F_2709e4 : fetch_word Plain.M.loaded_segments (0x270a28 : word) = Some W_2709e4.
Proof. vm_refl. Qed.
Lemma D_2709e4 : decode_any W_2709e4 = Some (Branch BC_NE 11 13 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709e8 : bv 32 := 0x00264583.
Lemma F_2709e8 : fetch_word Plain.M.loaded_segments (0x270a2c : word) = Some W_2709e8.
Proof. vm_refl. Qed.
Lemma D_2709e8 : decode_any W_2709e8 = Some (Load SZ1 false 11 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709ec : bv 32 := 0xfd058593.
Lemma F_2709ec : fetch_word Plain.M.loaded_segments (0x270a30 : word) = Some W_2709ec.
Proof. vm_refl. Qed.
Lemma D_2709ec : decode_any W_2709ec = Some (OpImm ALU_ADD 11 11 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709f0 : bv 32 := 0x00900693.
Lemma F_2709f0 : fetch_word Plain.M.loaded_segments (0x270a34 : word) = Some W_2709f0.
Proof. vm_refl. Qed.
Lemma D_2709f0 : decode_any W_2709f0 = Some (OpImm ALU_ADD 13 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709f4 : bv 32 := 0xfc600793.
Lemma F_2709f4 : fetch_word Plain.M.loaded_segments (0x270a38 : word) = Some W_2709f4.
Proof. vm_refl. Qed.
Lemma D_2709f4 : decode_any W_2709f4 = Some (OpImm ALU_ADD 15 0 4038, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709f8 : bv 32 := 0x03a00813.
Lemma F_2709f8 : fetch_word Plain.M.loaded_segments (0x270a3c : word) = Some W_2709f8.
Proof. vm_refl. Qed.
Lemma D_2709f8 : decode_any W_2709f8 = Some (OpImm ALU_ADD 16 0 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2709fc : bv 32 := 0x00800893.
Lemma F_2709fc : fetch_word Plain.M.loaded_segments (0x270a40 : word) = Some W_2709fc.
Proof. vm_refl. Qed.
Lemma D_2709fc : decode_any W_2709fc = Some (OpImm ALU_ADD 17 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a00 : bv 32 := 0x0ab6e263.
Lemma F_270a00 : fetch_word Plain.M.loaded_segments (0x270a44 : word) = Some W_270a00.
Proof. vm_refl. Qed.
Lemma D_270a00 : decode_any W_270a00 = Some (Branch BC_LTU 13 11 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a04 : bv 32 := 0x00364683.
Lemma F_270a04 : fetch_word Plain.M.loaded_segments (0x270a48 : word) = Some W_270a04.
Proof. vm_refl. Qed.
Lemma D_270a04 : decode_any W_270a04 = Some (Load SZ1 false 13 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a08 : bv 32 := 0x02400713.
Lemma F_270a08 : fetch_word Plain.M.loaded_segments (0x270a4c : word) = Some W_270a08.
Proof. vm_refl. Qed.
Lemma D_270a08 : decode_any W_270a08 = Some (OpImm ALU_ADD 14 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a0c : bv 32 := 0x08e69c63.
Lemma F_270a0c : fetch_word Plain.M.loaded_segments (0x270a50 : word) = Some W_270a0c.
Proof. vm_refl. Qed.
Lemma D_270a0c : decode_any W_270a0c = Some (Branch BC_NE 13 14 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a10 : bv 32 := 0x0c0a0a63.
Lemma F_270a10 : fetch_word Plain.M.loaded_segments (0x270a54 : word) = Some W_270a10.
Proof. vm_refl. Qed.
Lemma D_270a10 : decode_any W_270a10 = Some (Branch BC_EQ 20 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a14 : bv 32 := 0x00459593.
Lemma F_270a14 : fetch_word Plain.M.loaded_segments (0x270a58 : word) = Some W_270a14.
Proof. vm_refl. Qed.
Lemma D_270a14 : decode_any W_270a14 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a18 : bv 32 := 0x03813683.
Lemma F_270a18 : fetch_word Plain.M.loaded_segments (0x270a5c : word) = Some W_270a18.
Proof. vm_refl. Qed.
Lemma D_270a18 : decode_any W_270a18 = Some (Load SZ8 true 13 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a1c : bv 32 := 0x00b685b3.
Lemma F_270a1c : fetch_word Plain.M.loaded_segments (0x270a60 : word) = Some W_270a1c.
Proof. vm_refl. Qed.
Lemma D_270a1c : decode_any W_270a1c = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a20 : bv 32 := 0x0005ac83.
Lemma F_270a20 : fetch_word Plain.M.loaded_segments (0x270a64 : word) = Some W_270a20.
Proof. vm_refl. Qed.
Lemma D_270a20 : decode_any W_270a20 = Some (Load SZ4 true 25 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a24 : bv 32 := 0x0d80006f.
Lemma F_270a24 : fetch_word Plain.M.loaded_segments (0x270a68 : word) = Some W_270a24.
Proof. vm_refl. Qed.
Lemma D_270a24 : decode_any W_270a24 = Some (Jal 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a28 : bv 32 := 0x00000293.
Lemma F_270a28 : fetch_word Plain.M.loaded_segments (0x270a6c : word) = Some W_270a28.
Proof. vm_refl. Qed.
Lemma D_270a28 : decode_any W_270a28 = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a2c : bv 32 := 0xfff00c93.
Lemma F_270a2c : fetch_word Plain.M.loaded_segments (0x270a70 : word) = Some W_270a2c.
Proof. vm_refl. Qed.
Lemma D_270a2c : decode_any W_270a2c = Some (OpImm ALU_ADD 25 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a30 : bv 32 := 0xfc600793.
Lemma F_270a30 : fetch_word Plain.M.loaded_segments (0x270a74 : word) = Some W_270a30.
Proof. vm_refl. Qed.
Lemma D_270a30 : decode_any W_270a30 = Some (OpImm ALU_ADD 15 0 4038, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a34 : bv 32 := 0x03a00813.
Lemma F_270a34 : fetch_word Plain.M.loaded_segments (0x270a78 : word) = Some W_270a34.
Proof. vm_refl. Qed.
Lemma D_270a34 : decode_any W_270a34 = Some (OpImm ALU_ADD 16 0 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a38 : bv 32 := 0x00800893.
Lemma F_270a38 : fetch_word Plain.M.loaded_segments (0x270a7c : word) = Some W_270a38.
Proof. vm_refl. Qed.
Lemma D_270a38 : decode_any W_270a38 = Some (OpImm ALU_ADD 17 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a3c : bv 32 := 0x0cc0006f.
Lemma F_270a3c : fetch_word Plain.M.loaded_segments (0x270a80 : word) = Some W_270a3c.
Proof. vm_refl. Qed.
Lemma D_270a3c : decode_any W_270a3c = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a40 : bv 32 := 0x00160613.
Lemma F_270a40 : fetch_word Plain.M.loaded_segments (0x270a84 : word) = Some W_270a40.
Proof. vm_refl. Qed.
Lemma D_270a40 : decode_any W_270a40 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a44 : bv 32 := 0xfd058593.
Lemma F_270a44 : fetch_word Plain.M.loaded_segments (0x270a88 : word) = Some W_270a44.
Proof. vm_refl. Qed.
Lemma D_270a44 : decode_any W_270a44 = Some (OpImm ALU_ADD 11 11 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a48 : bv 32 := 0x00100293.
Lemma F_270a48 : fetch_word Plain.M.loaded_segments (0x270a8c : word) = Some W_270a48.
Proof. vm_refl. Qed.
Lemma D_270a48 : decode_any W_270a48 = Some (OpImm ALU_ADD 5 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a4c : bv 32 := 0x00900693.
Lemma F_270a4c : fetch_word Plain.M.loaded_segments (0x270a90 : word) = Some W_270a4c.
Proof. vm_refl. Qed.
Lemma D_270a4c : decode_any W_270a4c = Some (OpImm ALU_ADD 13 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a50 : bv 32 := 0x00800893.
Lemma F_270a50 : fetch_word Plain.M.loaded_segments (0x270a94 : word) = Some W_270a50.
Proof. vm_refl. Qed.
Lemma D_270a50 : decode_any W_270a50 = Some (OpImm ALU_ADD 17 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a54 : bv 32 := 0x00000c93.
Lemma F_270a54 : fetch_word Plain.M.loaded_segments (0x270a98 : word) = Some W_270a54.
Proof. vm_refl. Qed.
Lemma D_270a54 : decode_any W_270a54 = Some (OpImm ALU_ADD 25 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a58 : bv 32 := 0x06b6ec63.
Lemma F_270a58 : fetch_word Plain.M.loaded_segments (0x270a9c : word) = Some W_270a58.
Proof. vm_refl. Qed.
Lemma D_270a58 : decode_any W_270a58 = Some (Branch BC_LTU 13 11 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a5c : bv 32 := 0x00a00813.
Lemma F_270a5c : fetch_word Plain.M.loaded_segments (0x270aa0 : word) = Some W_270a5c.
Proof. vm_refl. Qed.
Lemma D_270a5c : decode_any W_270a5c = Some (OpImm ALU_ADD 16 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a60 : bv 32 := 0x0340006f.
Lemma F_270a60 : fetch_word Plain.M.loaded_segments (0x270aa4 : word) = Some W_270a60.
Proof. vm_refl. Qed.
Lemma D_270a60 : decode_any W_270a60 = Some (Jal 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a64 : bv 32 := 0x030c86bb.
Lemma F_270a64 : fetch_word Plain.M.loaded_segments (0x270aa8 : word) = Some W_270a64.
Proof. vm_refl. Qed.
Lemma D_270a64 : decode_any W_270a64 = Some (Mul32 M_MUL 13 25 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a68 : bv 32 := 0x0005871b.
Lemma F_270a68 : fetch_word Plain.M.loaded_segments (0x270aac : word) = Some W_270a68.
Proof. vm_refl. Qed.
Lemma D_270a68 : decode_any W_270a68 = Some (OpImm32 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a6c : bv 32 := 0x0096c7b3.
Lemma F_270a6c : fetch_word Plain.M.loaded_segments (0x270ab0 : word) = Some W_270a6c.
Proof. vm_refl. Qed.
Lemma D_270a6c : decode_any W_270a6c = Some (Op ALU_XOR 15 13 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a70 : bv 32 := 0x00e7b733.
Lemma F_270a70 : fetch_word Plain.M.loaded_segments (0x270ab4 : word) = Some W_270a70.
Proof. vm_refl. Qed.
Lemma D_270a70 : decode_any W_270a70 = Some (Op ALU_SLTU 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a74 : bv 32 := 0x00b685bb.
Lemma F_270a74 : fetch_word Plain.M.loaded_segments (0x270ab8 : word) = Some W_270a74.
Proof. vm_refl. Qed.
Lemma D_270a74 : decode_any W_270a74 = Some (Op32 ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a78 : bv 32 := 0x40e006bb.
Lemma F_270a78 : fetch_word Plain.M.loaded_segments (0x270abc : word) = Some W_270a78.
Proof. vm_refl. Qed.
Lemma D_270a78 : decode_any W_270a78 = Some (Op32 ALU_SUB 13 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a7c : bv 32 := 0x00b6ecb3.
Lemma F_270a7c : fetch_word Plain.M.loaded_segments (0x270ac0 : word) = Some W_270a7c.
Proof. vm_refl. Qed.
Lemma D_270a7c : decode_any W_270a7c = Some (Op ALU_OR 25 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a80 : bv 32 := 0x00164583.
Lemma F_270a80 : fetch_word Plain.M.loaded_segments (0x270ac4 : word) = Some W_270a80.
Proof. vm_refl. Qed.
Lemma D_270a80 : decode_any W_270a80 = Some (Load SZ1 false 11 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a84 : bv 32 := 0x00160693.
Lemma F_270a84 : fetch_word Plain.M.loaded_segments (0x270ac8 : word) = Some W_270a84.
Proof. vm_refl. Qed.
Lemma D_270a84 : decode_any W_270a84 = Some (OpImm ALU_ADD 13 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a88 : bv 32 := 0xfd058593.
Lemma F_270a88 : fetch_word Plain.M.loaded_segments (0x270acc : word) = Some W_270a88.
Proof. vm_refl. Qed.
Lemma D_270a88 : decode_any W_270a88 = Some (OpImm ALU_ADD 11 11 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a8c : bv 32 := 0x00068613.
Lemma F_270a8c : fetch_word Plain.M.loaded_segments (0x270ad0 : word) = Some W_270a8c.
Proof. vm_refl. Qed.
Lemma D_270a8c : decode_any W_270a8c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a90 : bv 32 := 0x0305fe63.
Lemma F_270a90 : fetch_word Plain.M.loaded_segments (0x270ad4 : word) = Some W_270a90.
Proof. vm_refl. Qed.
Lemma D_270a90 : decode_any W_270a90 = Some (Branch BC_GEU 11 16 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a94 : bv 32 := 0x06813683.
Lemma F_270a94 : fetch_word Plain.M.loaded_segments (0x270ad8 : word) = Some W_270a94.
Proof. vm_refl. Qed.
Lemma D_270a94 : decode_any W_270a94 = Some (Load SZ8 true 13 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a98 : bv 32 := 0xfd96f6e3.
Lemma F_270a98 : fetch_word Plain.M.loaded_segments (0x270adc : word) = Some W_270a98.
Proof. vm_refl. Qed.
Lemma D_270a98 : decode_any W_270a98 = Some (Branch BC_GEU 13 25 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270a9c : bv 32 := 0xfff00c93.
Lemma F_270a9c : fetch_word Plain.M.loaded_segments (0x270ae0 : word) = Some W_270a9c.
Proof. vm_refl. Qed.
Lemma D_270a9c : decode_any W_270a9c = Some (OpImm ALU_ADD 25 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270aa0 : bv 32 := 0xfe1ff06f.
Lemma F_270aa0 : fetch_word Plain.M.loaded_segments (0x270ae4 : word) = Some W_270aa0.
Proof. vm_refl. Qed.
Lemma D_270aa0 : decode_any W_270aa0 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270aa4 : bv 32 := 0x05813583.
Lemma F_270aa4 : fetch_word Plain.M.loaded_segments (0x270ae8 : word) = Some W_270aa4.
Proof. vm_refl. Qed.
Lemma D_270aa4 : decode_any W_270aa4 = Some (Load SZ8 true 11 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270aa8 : bv 32 := 0x1e0592e3.
Lemma F_270aa8 : fetch_word Plain.M.loaded_segments (0x270aec : word) = Some W_270aa8.
Proof. vm_refl. Qed.
Lemma D_270aa8 : decode_any W_270aa8 = Some (Branch BC_NE 11 0 2532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270aac : bv 32 := 0x00260613.
Lemma F_270aac : fetch_word Plain.M.loaded_segments (0x270af0 : word) = Some W_270aac.
Proof. vm_refl. Qed.
Lemma D_270aac : decode_any W_270aac = Some (OpImm ALU_ADD 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ab0 : bv 32 := 0x020a0663.
Lemma F_270ab0 : fetch_word Plain.M.loaded_segments (0x270af4 : word) = Some W_270ab0.
Proof. vm_refl. Qed.
Lemma D_270ab0 : decode_any W_270ab0 = Some (Branch BC_EQ 20 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ab4 : bv 32 := 0x04813703.
Lemma F_270ab4 : fetch_word Plain.M.loaded_segments (0x270af8 : word) = Some W_270ab4.
Proof. vm_refl. Qed.
Lemma D_270ab4 : decode_any W_270ab4 = Some (Load SZ8 true 14 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ab8 : bv 32 := 0x00073583.
Lemma F_270ab8 : fetch_word Plain.M.loaded_segments (0x270afc : word) = Some W_270ab8.
Proof. vm_refl. Qed.
Lemma D_270ab8 : decode_any W_270ab8 = Some (Load SZ8 true 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270abc : bv 32 := 0x00858693.
Lemma F_270abc : fetch_word Plain.M.loaded_segments (0x270b00 : word) = Some W_270abc.
Proof. vm_refl. Qed.
Lemma D_270abc : decode_any W_270abc = Some (OpImm ALU_ADD 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ac0 : bv 32 := 0x00d73023.
Lemma F_270ac0 : fetch_word Plain.M.loaded_segments (0x270b04 : word) = Some W_270ac0.
Proof. vm_refl. Qed.
Lemma D_270ac0 : decode_any W_270ac0 = Some (Store SZ8 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ac4 : bv 32 := 0x0005ac83.
Lemma F_270ac4 : fetch_word Plain.M.loaded_segments (0x270b08 : word) = Some W_270ac4.
Proof. vm_refl. Qed.
Lemma D_270ac4 : decode_any W_270ac4 = Some (Load SZ4 true 25 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ac8 : bv 32 := 0x0380006f.
Lemma F_270ac8 : fetch_word Plain.M.loaded_segments (0x270b0c : word) = Some W_270ac8.
Proof. vm_refl. Qed.
Lemma D_270ac8 : decode_any W_270ac8 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270acc : bv 32 := 0x00068613.
Lemma F_270acc : fetch_word Plain.M.loaded_segments (0x270b10 : word) = Some W_270acc.
Proof. vm_refl. Qed.
Lemma D_270acc : decode_any W_270acc = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ad0 : bv 32 := 0xfc600793.
Lemma F_270ad0 : fetch_word Plain.M.loaded_segments (0x270b14 : word) = Some W_270ad0.
Proof. vm_refl. Qed.
Lemma D_270ad0 : decode_any W_270ad0 = Some (OpImm ALU_ADD 15 0 4038, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ad4 : bv 32 := 0x03a00813.
Lemma F_270ad4 : fetch_word Plain.M.loaded_segments (0x270b18 : word) = Some W_270ad4.
Proof. vm_refl. Qed.
Lemma D_270ad4 : decode_any W_270ad4 = Some (OpImm ALU_ADD 16 0 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ad8 : bv 32 := 0x0300006f.
Lemma F_270ad8 : fetch_word Plain.M.loaded_segments (0x270b1c : word) = Some W_270ad8.
Proof. vm_refl. Qed.
Lemma D_270ad8 : decode_any W_270ad8 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270adc : bv 32 := 0x00000c93.
Lemma F_270adc : fetch_word Plain.M.loaded_segments (0x270b20 : word) = Some W_270adc.
Proof. vm_refl. Qed.
Lemma D_270adc : decode_any W_270adc = Some (OpImm ALU_ADD 25 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ae0 : bv 32 := 0x0200006f.
Lemma F_270ae0 : fetch_word Plain.M.loaded_segments (0x270b24 : word) = Some W_270ae0.
Proof. vm_refl. Qed.
Lemma D_270ae0 : decode_any W_270ae0 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ae4 : bv 32 := 0x00000c93.
Lemma F_270ae4 : fetch_word Plain.M.loaded_segments (0x270b28 : word) = Some W_270ae4.
Proof. vm_refl. Qed.
Lemma D_270ae4 : decode_any W_270ae4 = Some (OpImm ALU_ADD 25 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ae8 : bv 32 := 0x00259593.
Lemma F_270ae8 : fetch_word Plain.M.loaded_segments (0x270b2c : word) = Some W_270ae8.
Proof. vm_refl. Qed.
Lemma D_270ae8 : decode_any W_270ae8 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270aec : bv 32 := 0x04013683.
Lemma F_270aec : fetch_word Plain.M.loaded_segments (0x270b30 : word) = Some W_270aec.
Proof. vm_refl. Qed.
Lemma D_270aec : decode_any W_270aec = Some (Load SZ8 true 13 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270af0 : bv 32 := 0x00b685b3.
Lemma F_270af0 : fetch_word Plain.M.loaded_segments (0x270b34 : word) = Some W_270af0.
Proof. vm_refl. Qed.
Lemma D_270af0 : decode_any W_270af0 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270af4 : bv 32 := 0x00a00693.
Lemma F_270af4 : fetch_word Plain.M.loaded_segments (0x270b38 : word) = Some W_270af4.
Proof. vm_refl. Qed.
Lemma D_270af4 : decode_any W_270af4 = Some (OpImm ALU_ADD 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270af8 : bv 32 := 0x00d5a023.
Lemma F_270af8 : fetch_word Plain.M.loaded_segments (0x270b3c : word) = Some W_270af8.
Proof. vm_refl. Qed.
Lemma D_270af8 : decode_any W_270af8 = Some (Store SZ4 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270afc : bv 32 := 0x00460613.
Lemma F_270afc : fetch_word Plain.M.loaded_segments (0x270b40 : word) = Some W_270afc.
Proof. vm_refl. Qed.
Lemma D_270afc : decode_any W_270afc = Some (OpImm ALU_ADD 12 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b00 : bv 32 := 0x000ca593.
Lemma F_270b00 : fetch_word Plain.M.loaded_segments (0x270b44 : word) = Some W_270b00.
Proof. vm_refl. Qed.
Lemma D_270b00 : decode_any W_270b00 = Some (OpImm ALU_SLT 11 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b04 : bv 32 := 0x0015c293.
Lemma F_270b04 : fetch_word Plain.M.loaded_segments (0x270b48 : word) = Some W_270b04.
Proof. vm_refl. Qed.
Lemma D_270b04 : decode_any W_270b04 = Some (OpImm ALU_XOR 5 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b08 : bv 32 := 0x00000593.
Lemma F_270b08 : fetch_word Plain.M.loaded_segments (0x270b4c : word) = Some W_270b08.
Proof. vm_refl. Qed.
Lemma D_270b08 : decode_any W_270b08 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b0c : bv 32 := 0x00060a93.
Lemma F_270b0c : fetch_word Plain.M.loaded_segments (0x270b50 : word) = Some W_270b0c.
Proof. vm_refl. Qed.
Lemma D_270b0c : decode_any W_270b0c = Some (OpImm ALU_ADD 21 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b10 : bv 32 := 0x000ac603.
Lemma F_270b10 : fetch_word Plain.M.loaded_segments (0x270b54 : word) = Some W_270b10.
Proof. vm_refl. Qed.
Lemma D_270b10 : decode_any W_270b10 = Some (Load SZ1 false 12 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b14 : bv 32 := 0xf8560693.
Lemma F_270b14 : fetch_word Plain.M.loaded_segments (0x270b58 : word) = Some W_270b14.
Proof. vm_refl. Qed.
Lemma D_270b14 : decode_any W_270b14 = Some (OpImm ALU_ADD 13 12 3973, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b18 : bv 32 := 0x16f6eae3.
Lemma F_270b18 : fetch_word Plain.M.loaded_segments (0x270b5c : word) = Some W_270b18.
Proof. vm_refl. Qed.
Lemma D_270b18 : decode_any W_270b18 = Some (Branch BC_LTU 13 15 2420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b1c : bv 32 := 0x00058d93.
Lemma F_270b1c : fetch_word Plain.M.loaded_segments (0x270b60 : word) = Some W_270b1c.
Proof. vm_refl. Qed.
Lemma D_270b1c : decode_any W_270b1c = Some (OpImm ALU_ADD 27 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b20 : bv 32 := 0x030585b3.
Lemma F_270b20 : fetch_word Plain.M.loaded_segments (0x270b64 : word) = Some W_270b20.
Proof. vm_refl. Qed.
Lemma D_270b20 : decode_any W_270b20 = Some (Mul M_MUL 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b24 : bv 32 := 0xffe01697.
Lemma F_270b24 : fetch_word Plain.M.loaded_segments (0x270b68 : word) = Some W_270b24.
Proof. vm_refl. Qed.
Lemma D_270b24 : decode_any W_270b24 = Some (Auipc 13 1048065, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b28 : bv 32 := 0x4b868693.
Lemma F_270b28 : fetch_word Plain.M.loaded_segments (0x270b6c : word) = Some W_270b28.
Proof. vm_refl. Qed.
Lemma D_270b28 : decode_any W_270b28 = Some (OpImm ALU_ADD 13 13 1208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b2c : bv 32 := 0x00b685b3.
Lemma F_270b2c : fetch_word Plain.M.loaded_segments (0x270b70 : word) = Some W_270b2c.
Proof. vm_refl. Qed.
Lemma D_270b2c : decode_any W_270b2c = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b30 : bv 32 := 0x00b605b3.
Lemma F_270b30 : fetch_word Plain.M.loaded_segments (0x270b74 : word) = Some W_270b30.
Proof. vm_refl. Qed.
Lemma D_270b30 : decode_any W_270b30 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b34 : bv 32 := 0xfbf5c583.
Lemma F_270b34 : fetch_word Plain.M.loaded_segments (0x270b78 : word) = Some W_270b34.
Proof. vm_refl. Qed.
Lemma D_270b34 : decode_any W_270b34 = Some (Load SZ1 false 11 11 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b38 : bv 32 := 0xfff58613.
Lemma F_270b38 : fetch_word Plain.M.loaded_segments (0x270b7c : word) = Some W_270b38.
Proof. vm_refl. Qed.
Lemma D_270b38 : decode_any W_270b38 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b3c : bv 32 := 0x001a8a93.
Lemma F_270b3c : fetch_word Plain.M.loaded_segments (0x270b80 : word) = Some W_270b3c.
Proof. vm_refl. Qed.
Lemma D_270b3c : decode_any W_270b3c = Some (OpImm ALU_ADD 21 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b40 : bv 32 := 0xfd1668e3.
Lemma F_270b40 : fetch_word Plain.M.loaded_segments (0x270b84 : word) = Some W_270b40.
Proof. vm_refl. Qed.
Lemma D_270b40 : decode_any W_270b40 = Some (Branch BC_LTU 12 17 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b44 : bv 32 := 0x01b00613.
Lemma F_270b44 : fetch_word Plain.M.loaded_segments (0x270b88 : word) = Some W_270b44.
Proof. vm_refl. Qed.
Lemma D_270b44 : decode_any W_270b44 = Some (OpImm ALU_ADD 12 0 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b48 : bv 32 := 0x02c58863.
Lemma F_270b48 : fetch_word Plain.M.loaded_segments (0x270b8c : word) = Some W_270b48.
Proof. vm_refl. Qed.
Lemma D_270b48 : decode_any W_270b48 = Some (Branch BC_EQ 11 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b4c : bv 32 := 0x140580e3.
Lemma F_270b4c : fetch_word Plain.M.loaded_segments (0x270b90 : word) = Some W_270b4c.
Proof. vm_refl. Qed.
Lemma D_270b4c : decode_any W_270b4c = Some (Branch BC_EQ 11 0 2368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b50 : bv 32 := 0x02054c63.
Lemma F_270b50 : fetch_word Plain.M.loaded_segments (0x270b94 : word) = Some W_270b50.
Proof. vm_refl. Qed.
Lemma D_270b50 : decode_any W_270b50 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b54 : bv 32 := 0x0e0a0663.
Lemma F_270b54 : fetch_word Plain.M.loaded_segments (0x270b98 : word) = Some W_270b54.
Proof. vm_refl. Qed.
Lemma D_270b54 : decode_any W_270b54 = Some (Branch BC_EQ 20 0 236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b58 : bv 32 := 0x00451513.
Lemma F_270b58 : fetch_word Plain.M.loaded_segments (0x270b9c : word) = Some W_270b58.
Proof. vm_refl. Qed.
Lemma D_270b58 : decode_any W_270b58 = Some (ShiftImm ALU_SLL 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b5c : bv 32 := 0x03813583.
Lemma F_270b5c : fetch_word Plain.M.loaded_segments (0x270ba0 : word) = Some W_270b5c.
Proof. vm_refl. Qed.
Lemma D_270b5c : decode_any W_270b5c = Some (Load SZ8 true 11 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b60 : bv 32 := 0x00a58533.
Lemma F_270b60 : fetch_word Plain.M.loaded_segments (0x270ba4 : word) = Some W_270b60.
Proof. vm_refl. Qed.
Lemma D_270b60 : decode_any W_270b60 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b64 : bv 32 := 0x00053583.
Lemma F_270b64 : fetch_word Plain.M.loaded_segments (0x270ba8 : word) = Some W_270b64.
Proof. vm_refl. Qed.
Lemma D_270b64 : decode_any W_270b64 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b68 : bv 32 := 0x00853503.
Lemma F_270b68 : fetch_word Plain.M.loaded_segments (0x270bac : word) = Some W_270b68.
Proof. vm_refl. Qed.
Lemma D_270b68 : decode_any W_270b68 = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b6c : bv 32 := 0x06b13823.
Lemma F_270b6c : fetch_word Plain.M.loaded_segments (0x270bb0 : word) = Some W_270b6c.
Proof. vm_refl. Qed.
Lemma D_270b6c : decode_any W_270b6c = Some (Store SZ8 2 11 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b70 : bv 32 := 0x06a13c23.
Lemma F_270b70 : fetch_word Plain.M.loaded_segments (0x270bb4 : word) = Some W_270b70.
Proof. vm_refl. Qed.
Lemma D_270b70 : decode_any W_270b70 = Some (Store SZ8 2 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b74 : bv 32 := 0x02c0006f.
Lemma F_270b74 : fetch_word Plain.M.loaded_segments (0x270bb8 : word) = Some W_270b74.
Proof. vm_refl. Qed.
Lemma D_270b74 : decode_any W_270b74 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b78 : bv 32 := 0x10055ae3.
Lemma F_270b78 : fetch_word Plain.M.loaded_segments (0x270bbc : word) = Some W_270b78.
Proof. vm_refl. Qed.
Lemma D_270b78 : decode_any W_270b78 = Some (Branch BC_GE 10 0 2324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b7c : bv 32 := 0x00000d13.
Lemma F_270b7c : fetch_word Plain.M.loaded_segments (0x270bc0 : word) = Some W_270b7c.
Proof. vm_refl. Qed.
Lemma D_270b7c : decode_any W_270b7c = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b80 : bv 32 := 0x020a1063.
Lemma F_270b80 : fetch_word Plain.M.loaded_segments (0x270bc4 : word) = Some W_270b80.
Proof. vm_refl. Qed.
Lemma D_270b80 : decode_any W_270b80 = Some (Branch BC_NE 20 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b84 : bv 32 := 0xbedff06f.
Lemma F_270b84 : fetch_word Plain.M.loaded_segments (0x270bc8 : word) = Some W_270b84.
Proof. vm_refl. Qed.
Lemma D_270b84 : decode_any W_270b84 = Some (Jal 0 2096108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b88 : bv 32 := 0x080a08e3.
Lemma F_270b88 : fetch_word Plain.M.loaded_segments (0x270bcc : word) = Some W_270b88.
Proof. vm_refl. Qed.
Lemma D_270b88 : decode_any W_270b88 = Some (Branch BC_EQ 20 0 2192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b8c : bv 32 := 0x07010513.
Lemma F_270b8c : fetch_word Plain.M.loaded_segments (0x270bd0 : word) = Some W_270b8c.
Proof. vm_refl. Qed.
Lemma D_270b8c : decode_any W_270b8c = Some (OpImm ALU_ADD 10 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b90 : bv 32 := 0x04813603.
Lemma F_270b90 : fetch_word Plain.M.loaded_segments (0x270bd4 : word) = Some W_270b90.
Proof. vm_refl. Qed.
Lemma D_270b90 : decode_any W_270b90 = Some (Load SZ8 true 12 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b94 : bv 32 := 0x00028d13.
Lemma F_270b94 : fetch_word Plain.M.loaded_segments (0x270bd8 : word) = Some W_270b94.
Proof. vm_refl. Qed.
Lemma D_270b94 : decode_any W_270b94 = Some (OpImm ALU_ADD 26 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b98 : bv 32 := 0x159000ef.
Lemma F_270b98 : fetch_word Plain.M.loaded_segments (0x270bdc : word) = Some W_270b98.
Proof. vm_refl. Qed.
Lemma D_270b98 : decode_any W_270b98 = Some (Jal 1 2392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270b9c : bv 32 := 0x000d0293.
Lemma F_270b9c : fetch_word Plain.M.loaded_segments (0x270be0 : word) = Some W_270b9c.
Proof. vm_refl. Qed.
Lemma D_270b9c : decode_any W_270b9c = Some (OpImm ALU_ADD 5 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ba0 : bv 32 := 0x000a4503.
Lemma F_270ba0 : fetch_word Plain.M.loaded_segments (0x270be4 : word) = Some W_270ba0.
Proof. vm_refl. Qed.
Lemma D_270ba0 : decode_any W_270ba0 = Some (Load SZ1 false 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ba4 : bv 32 := 0x02057513.
Lemma F_270ba4 : fetch_word Plain.M.loaded_segments (0x270be8 : word) = Some W_270ba4.
Proof. vm_refl. Qed.
Lemma D_270ba4 : decode_any W_270ba4 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ba8 : bv 32 := 0x0e0518e3.
Lemma F_270ba8 : fetch_word Plain.M.loaded_segments (0x270bec : word) = Some W_270ba8.
Proof. vm_refl. Qed.
Lemma D_270ba8 : decode_any W_270ba8 = Some (Branch BC_NE 10 0 2288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bac : bv 32 := 0xfffac803.
Lemma F_270bac : fetch_word Plain.M.loaded_segments (0x270bf0 : word) = Some W_270bac.
Proof. vm_refl. Qed.
Lemma D_270bac : decode_any W_270bac = Some (Load SZ1 false 16 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bb0 : bv 32 := 0x01b03533.
Lemma F_270bb0 : fetch_word Plain.M.loaded_segments (0x270bf4 : word) = Some W_270bb0.
Proof. vm_refl. Qed.
Lemma D_270bb0 : decode_any W_270bb0 = Some (Op ALU_SLTU 10 0 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bb4 : bv 32 := 0x00f87593.
Lemma F_270bb4 : fetch_word Plain.M.loaded_segments (0x270bf8 : word) = Some W_270bb4.
Proof. vm_refl. Qed.
Lemma D_270bb4 : decode_any W_270bb4 = Some (OpImm ALU_AND 11 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bb8 : bv 32 := 0xffd58593.
Lemma F_270bb8 : fetch_word Plain.M.loaded_segments (0x270bfc : word) = Some W_270bb8.
Proof. vm_refl. Qed.
Lemma D_270bb8 : decode_any W_270bb8 = Some (OpImm ALU_ADD 11 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bbc : bv 32 := 0x0015b593.
Lemma F_270bbc : fetch_word Plain.M.loaded_segments (0x270c00 : word) = Some W_270bbc.
Proof. vm_refl. Qed.
Lemma D_270bbc : decode_any W_270bbc = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bc0 : bv 32 := 0x00b57533.
Lemma F_270bc0 : fetch_word Plain.M.loaded_segments (0x270c04 : word) = Some W_270bc0.
Proof. vm_refl. Qed.
Lemma D_270bc0 : decode_any W_270bc0 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bc4 : bv 32 := 0x00050463.
Lemma F_270bc4 : fetch_word Plain.M.loaded_segments (0x270c08 : word) = Some W_270bc4.
Proof. vm_refl. Qed.
Lemma D_270bc4 : decode_any W_270bc4 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bc8 : bv 32 := 0x0d387813.
Lemma F_270bc8 : fetch_word Plain.M.loaded_segments (0x270c0c : word) = Some W_270bc8.
Proof. vm_refl. Qed.
Lemma D_270bc8 : decode_any W_270bc8 = Some (OpImm ALU_AND 16 16 211, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bcc : bv 32 := 0x032c1513.
Lemma F_270bcc : fetch_word Plain.M.loaded_segments (0x270c10 : word) = Some W_270bcc.
Proof. vm_refl. Qed.
Lemma D_270bcc : decode_any W_270bcc = Some (ShiftImm ALU_SLL 10 24 50, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bd0 : bv 32 := 0x03013583.
Lemma F_270bd0 : fetch_word Plain.M.loaded_segments (0x270c14 : word) = Some W_270bd0.
Proof. vm_refl. Qed.
Lemma D_270bd0 : decode_any W_270bd0 = Some (Load SZ8 true 11 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bd4 : bv 32 := 0x00bc7d33.
Lemma F_270bd4 : fetch_word Plain.M.loaded_segments (0x270c18 : word) = Some W_270bd4.
Proof. vm_refl. Qed.
Lemma D_270bd4 : decode_any W_270bd4 = Some (Op ALU_AND 26 24 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bd8 : bv 32 := 0x00055463.
Lemma F_270bd8 : fetch_word Plain.M.loaded_segments (0x270c1c : word) = Some W_270bd8.
Proof. vm_refl. Qed.
Lemma D_270bd8 : decode_any W_270bd8 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bdc : bv 32 := 0x000d0c13.
Lemma F_270bdc : fetch_word Plain.M.loaded_segments (0x270c20 : word) = Some W_270bdc.
Proof. vm_refl. Qed.
Lemma D_270bdc : decode_any W_270bdc = Some (OpImm ALU_ADD 24 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270be0 : bv 32 := 0xfbf80513.
Lemma F_270be0 : fetch_word Plain.M.loaded_segments (0x270c24 : word) = Some W_270be0.
Proof. vm_refl. Qed.
Lemma D_270be0 : decode_any W_270be0 = Some (OpImm ALU_ADD 10 16 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270be4 : bv 32 := 0x03700593.
Lemma F_270be4 : fetch_word Plain.M.loaded_segments (0x270c28 : word) = Some W_270be4.
Proof. vm_refl. Qed.
Lemma D_270be4 : decode_any W_270be4 = Some (OpImm ALU_ADD 11 0 55, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270be8 : bv 32 := 0x0aa5e063.
Lemma F_270be8 : fetch_word Plain.M.loaded_segments (0x270c2c : word) = Some W_270be8.
Proof. vm_refl. Qed.
Lemma D_270be8 : decode_any W_270be8 = Some (Branch BC_LTU 11 10 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bec : bv 32 := 0x00251513.
Lemma F_270bec : fetch_word Plain.M.loaded_segments (0x270c30 : word) = Some W_270bec.
Proof. vm_refl. Qed.
Lemma D_270bec : decode_any W_270bec = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bf0 : bv 32 := 0xffe01597.
Lemma F_270bf0 : fetch_word Plain.M.loaded_segments (0x270c34 : word) = Some W_270bf0.
Proof. vm_refl. Qed.
Lemma D_270bf0 : decode_any W_270bf0 = Some (Auipc 11 1048065, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bf4 : bv 32 := 0x2a458593.
Lemma F_270bf4 : fetch_word Plain.M.loaded_segments (0x270c38 : word) = Some W_270bf4.
Proof. vm_refl. Qed.
Lemma D_270bf4 : decode_any W_270bf4 = Some (OpImm ALU_ADD 11 11 676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bf8 : bv 32 := 0x00b50533.
Lemma F_270bf8 : fetch_word Plain.M.loaded_segments (0x270c3c : word) = Some W_270bf8.
Proof. vm_refl. Qed.
Lemma D_270bf8 : decode_any W_270bf8 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270bfc : bv 32 := 0x00052503.
Lemma F_270bfc : fetch_word Plain.M.loaded_segments (0x270c40 : word) = Some W_270bfc.
Proof. vm_refl. Qed.
Lemma D_270bfc : decode_any W_270bfc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c00 : bv 32 := 0x00b50533.
Lemma F_270c00 : fetch_word Plain.M.loaded_segments (0x270c44 : word) = Some W_270c00.
Proof. vm_refl. Qed.
Lemma D_270c00 : decode_any W_270c00 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c04 : bv 32 := 0x00050067.
Lemma F_270c04 : fetch_word Plain.M.loaded_segments (0x270c48 : word) = Some W_270c04.
Proof. vm_refl. Qed.
Lemma D_270c04 : decode_any W_270c04 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c08 : bv 32 := 0x000ca513.
Lemma F_270c08 : fetch_word Plain.M.loaded_segments (0x270c4c : word) = Some W_270c08.
Proof. vm_refl. Qed.
Lemma D_270c08 : decode_any W_270c08 = Some (OpImm ALU_SLT 10 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c0c : bv 32 := 0x00a2f533.
Lemma F_270c0c : fetch_word Plain.M.loaded_segments (0x270c50 : word) = Some W_270c0c.
Proof. vm_refl. Qed.
Lemma D_270c0c : decode_any W_270c0c = Some (Op ALU_AND 10 5 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c10 : bv 32 := 0x72051463.
Lemma F_270c10 : fetch_word Plain.M.loaded_segments (0x270c54 : word) = Some W_270c10.
Proof. vm_refl. Qed.
Lemma D_270c10 : decode_any W_270c10 = Some (Branch BC_NE 10 0 1832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c14 : bv 32 := 0x07013583.
Lemma F_270c14 : fetch_word Plain.M.loaded_segments (0x270c58 : word) = Some W_270c14.
Proof. vm_refl. Qed.
Lemma D_270c14 : decode_any W_270c14 = Some (Load SZ8 true 11 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c18 : bv 32 := 0x07813603.
Lemma F_270c18 : fetch_word Plain.M.loaded_segments (0x270c5c : word) = Some W_270c18.
Proof. vm_refl. Qed.
Lemma D_270c18 : decode_any W_270c18 = Some (Load SZ8 true 12 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c1c : bv 32 := 0x000a0513.
Lemma F_270c1c : fetch_word Plain.M.loaded_segments (0x270c60 : word) = Some W_270c1c.
Proof. vm_refl. Qed.
Lemma D_270c1c : decode_any W_270c1c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c20 : bv 32 := 0x000b0693.
Lemma F_270c20 : fetch_word Plain.M.loaded_segments (0x270c64 : word) = Some W_270c20.
Proof. vm_refl. Qed.
Lemma D_270c20 : decode_any W_270c20 = Some (OpImm ALU_ADD 13 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c24 : bv 32 := 0x000c8713.
Lemma F_270c24 : fetch_word Plain.M.loaded_segments (0x270c68 : word) = Some W_270c24.
Proof. vm_refl. Qed.
Lemma D_270c24 : decode_any W_270c24 = Some (OpImm ALU_ADD 14 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c28 : bv 32 := 0x000c0793.
Lemma F_270c28 : fetch_word Plain.M.loaded_segments (0x270c6c : word) = Some W_270c28.
Proof. vm_refl. Qed.
Lemma D_270c28 : decode_any W_270c28 = Some (OpImm ALU_ADD 15 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c2c : bv 32 := 0x000d8893.
Lemma F_270c2c : fetch_word Plain.M.loaded_segments (0x270c70 : word) = Some W_270c2c.
Proof. vm_refl. Qed.
Lemma D_270c2c : decode_any W_270c2c = Some (OpImm ALU_ADD 17 27 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c30 : bv 32 := 0x2c9000ef.
Lemma F_270c30 : fetch_word Plain.M.loaded_segments (0x270c74 : word) = Some W_270c30.
Proof. vm_refl. Qed.
Lemma D_270c30 : decode_any W_270c30 = Some (Jal 1 2760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c34 : bv 32 := 0x00050d13.
Lemma F_270c34 : fetch_word Plain.M.loaded_segments (0x270c78 : word) = Some W_270c34.
Proof. vm_refl. Qed.
Lemma D_270c34 : decode_any W_270c34 = Some (OpImm ALU_ADD 26 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c38 : bv 32 := 0xb2055ce3.
Lemma F_270c38 : fetch_word Plain.M.loaded_segments (0x270c7c : word) = Some W_270c38.
Proof. vm_refl. Qed.
Lemma D_270c38 : decode_any W_270c38 = Some (Branch BC_GE 10 0 6968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c3c : bv 32 := 0x6fc0006f.
Lemma F_270c3c : fetch_word Plain.M.loaded_segments (0x270c80 : word) = Some W_270c3c.
Proof. vm_refl. Qed.
Lemma D_270c3c : decode_any W_270c3c = Some (Jal 0 1788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c40 : bv 32 := 0x00000d13.
Lemma F_270c40 : fetch_word Plain.M.loaded_segments (0x270c84 : word) = Some W_270c40.
Proof. vm_refl. Qed.
Lemma D_270c40 : decode_any W_270c40 = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c44 : bv 32 := 0x00251513.
Lemma F_270c44 : fetch_word Plain.M.loaded_segments (0x270c88 : word) = Some W_270c44.
Proof. vm_refl. Qed.
Lemma D_270c44 : decode_any W_270c44 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c48 : bv 32 := 0x04013603.
Lemma F_270c48 : fetch_word Plain.M.loaded_segments (0x270c8c : word) = Some W_270c48.
Proof. vm_refl. Qed.
Lemma D_270c48 : decode_any W_270c48 = Some (Load SZ8 true 12 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c4c : bv 32 := 0x00a60533.
Lemma F_270c4c : fetch_word Plain.M.loaded_segments (0x270c90 : word) = Some W_270c4c.
Proof. vm_refl. Qed.
Lemma D_270c4c : decode_any W_270c4c = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c50 : bv 32 := 0x00b52023.
Lemma F_270c50 : fetch_word Plain.M.loaded_segments (0x270c94 : word) = Some W_270c50.
Proof. vm_refl. Qed.
Lemma D_270c50 : decode_any W_270c50 = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c54 : bv 32 := 0xb1dff06f.
Lemma F_270c54 : fetch_word Plain.M.loaded_segments (0x270c98 : word) = Some W_270c54.
Proof. vm_refl. Qed.
Lemma D_270c54 : decode_any W_270c54 = Some (Jal 0 2095900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c58 : bv 32 := 0x07013503.
Lemma F_270c58 : fetch_word Plain.M.loaded_segments (0x270c9c : word) = Some W_270c58.
Proof. vm_refl. Qed.
Lemma D_270c58 : decode_any W_270c58 = Some (Load SZ8 true 10 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c5c : bv 32 := 0x2c054a63.
Lemma F_270c5c : fetch_word Plain.M.loaded_segments (0x270ca0 : word) = Some W_270c5c.
Proof. vm_refl. Qed.
Lemma D_270c5c : decode_any W_270c5c = Some (Branch BC_LT 10 0 724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c60 : bv 32 := 0xffda1597.
Lemma F_270c60 : fetch_word Plain.M.loaded_segments (0x270ca4 : word) = Some W_270c60.
Proof. vm_refl. Qed.
Lemma D_270c60 : decode_any W_270c60 = Some (Auipc 11 1047969, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c64 : bv 32 := 0x034c1613.
Lemma F_270c64 : fetch_word Plain.M.loaded_segments (0x270ca8 : word) = Some W_270c64.
Proof. vm_refl. Qed.
Lemma D_270c64 : decode_any W_270c64 = Some (ShiftImm ALU_SLL 12 24 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c68 : bv 32 := 0x9f658593.
Lemma F_270c68 : fetch_word Plain.M.loaded_segments (0x270cac : word) = Some W_270c68.
Proof. vm_refl. Qed.
Lemma D_270c68 : decode_any W_270c68 = Some (OpImm ALU_ADD 11 11 2550, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c6c : bv 32 := 0x00a00713.
Lemma F_270c6c : fetch_word Plain.M.loaded_segments (0x270cb0 : word) = Some W_270c6c.
Proof. vm_refl. Qed.
Lemma D_270c6c : decode_any W_270c6c = Some (OpImm ALU_ADD 14 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c70 : bv 32 := 0x2e064063.
Lemma F_270c70 : fetch_word Plain.M.loaded_segments (0x270cb4 : word) = Some W_270c70.
Proof. vm_refl. Qed.
Lemma D_270c70 : decode_any W_270c70 = Some (Branch BC_LT 12 0 736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c74 : bv 32 := 0x001c7613.
Lemma F_270c74 : fetch_word Plain.M.loaded_segments (0x270cb8 : word) = Some W_270c74.
Proof. vm_refl. Qed.
Lemma D_270c74 : decode_any W_270c74 = Some (OpImm ALU_AND 12 24 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c78 : bv 32 := 0x00c13c23.
Lemma F_270c78 : fetch_word Plain.M.loaded_segments (0x270cbc : word) = Some W_270c78.
Proof. vm_refl. Qed.
Lemma D_270c78 : decode_any W_270c78 = Some (Store SZ8 2 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c7c : bv 32 := 0x00161613.
Lemma F_270c7c : fetch_word Plain.M.loaded_segments (0x270cc0 : word) = Some W_270c7c.
Proof. vm_refl. Qed.
Lemma D_270c7c : decode_any W_270c7c = Some (ShiftImm ALU_SLL 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c80 : bv 32 := 0x00c588b3.
Lemma F_270c80 : fetch_word Plain.M.loaded_segments (0x270cc4 : word) = Some W_270c80.
Proof. vm_refl. Qed.
Lemma D_270c80 : decode_any W_270c80 = Some (Op ALU_ADD 17 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c84 : bv 32 := 0x2d80006f.
Lemma F_270c84 : fetch_word Plain.M.loaded_segments (0x270cc8 : word) = Some W_270c84.
Proof. vm_refl. Qed.
Lemma D_270c84 : decode_any W_270c84 = Some (Jal 0 728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c88 : bv 32 := 0x00013c23.
Lemma F_270c88 : fetch_word Plain.M.loaded_segments (0x270ccc : word) = Some W_270c88.
Proof. vm_refl. Qed.
Lemma D_270c88 : decode_any W_270c88 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c8c : bv 32 := 0xffda1517.
Lemma F_270c8c : fetch_word Plain.M.loaded_segments (0x270cd0 : word) = Some W_270c8c.
Proof. vm_refl. Qed.
Lemma D_270c8c : decode_any W_270c8c = Some (Auipc 10 1047969, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c90 : bv 32 := 0x9ca50513.
Lemma F_270c90 : fetch_word Plain.M.loaded_segments (0x270cd4 : word) = Some W_270c90.
Proof. vm_refl. Qed.
Lemma D_270c90 : decode_any W_270c90 = Some (OpImm ALU_ADD 10 10 2506, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c94 : bv 32 := 0x00a13023.
Lemma F_270c94 : fetch_word Plain.M.loaded_segments (0x270cd8 : word) = Some W_270c94.
Proof. vm_refl. Qed.
Lemma D_270c94 : decode_any W_270c94 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c98 : bv 32 := 0x0b010593.
Lemma F_270c98 : fetch_word Plain.M.loaded_segments (0x270cdc : word) = Some W_270c98.
Proof. vm_refl. Qed.
Lemma D_270c98 : decode_any W_270c98 = Some (OpImm ALU_ADD 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270c9c : bv 32 := 0x3700006f.
Lemma F_270c9c : fetch_word Plain.M.loaded_segments (0x270ce0 : word) = Some W_270c9c.
Proof. vm_refl. Qed.
Lemma D_270c9c : decode_any W_270c9c = Some (Jal 0 880, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ca0 : bv 32 := 0x07013b83.
Lemma F_270ca0 : fetch_word Plain.M.loaded_segments (0x270ce4 : word) = Some W_270ca0.
Proof. vm_refl. Qed.
Lemma D_270ca0 : decode_any W_270ca0 = Some (Load SZ8 true 23 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ca4 : bv 32 := 0x020b9063.
Lemma F_270ca4 : fetch_word Plain.M.loaded_segments (0x270ce8 : word) = Some W_270ca4.
Proof. vm_refl. Qed.
Lemma D_270ca4 : decode_any W_270ca4 = Some (Branch BC_NE 23 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ca8 : bv 32 := 0xffdca517.
Lemma F_270ca8 : fetch_word Plain.M.loaded_segments (0x270cec : word) = Some W_270ca8.
Proof. vm_refl. Qed.
Lemma D_270ca8 : decode_any W_270ca8 = Some (Auipc 10 1048010, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270cac : bv 32 := 0x94150b93.
Lemma F_270cac : fetch_word Plain.M.loaded_segments (0x270cf0 : word) = Some W_270cac.
Proof. vm_refl. Qed.
Lemma D_270cac : decode_any W_270cac = Some (OpImm ALU_ADD 23 10 2369, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270cb0 : bv 32 := 0x0140006f.
Lemma F_270cb0 : fetch_word Plain.M.loaded_segments (0x270cf4 : word) = Some W_270cb0.
Proof. vm_refl. Qed.
Lemma D_270cb0 : decode_any W_270cb0 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270cb4 : bv 32 := 0xcadfa0ef.
Lemma F_270cb4 : fetch_word Plain.M.loaded_segments (0x270cf8 : word) = Some W_270cb4.
Proof. vm_refl. Qed.
Lemma D_270cb4 : decode_any W_270cb4 = Some (Jal 1 2075820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270cb8 : bv 32 := 0x00052503.
Lemma F_270cb8 : fetch_word Plain.M.loaded_segments (0x270cfc : word) = Some W_270cb8.
Proof. vm_refl. Qed.
Lemma D_270cb8 : decode_any W_270cb8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270cbc : bv 32 := 0x104020ef.
Lemma F_270cbc : fetch_word Plain.M.loaded_segments (0x270d00 : word) = Some W_270cbc.
Proof. vm_refl. Qed.
Lemma D_270cbc : decode_any W_270cbc = Some (Jal 1 8452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270cc0 : bv 32 := 0x00050b93.
Lemma F_270cc0 : fetch_word Plain.M.loaded_segments (0x270d04 : word) = Some W_270cc0.
Proof. vm_refl. Qed.
Lemma D_270cc0 : decode_any W_270cc0 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270cc4 : bv 32 := 0x000c8593.
Lemma F_270cc4 : fetch_word Plain.M.loaded_segments (0x270d08 : word) = Some W_270cc4.
Proof. vm_refl. Qed.
Lemma D_270cc4 : decode_any W_270cc4 = Some (OpImm ALU_ADD 11 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270cc8 : bv 32 := 0x009ce463.
Lemma F_270cc8 : fetch_word Plain.M.loaded_segments (0x270d0c : word) = Some W_270cc8.
Proof. vm_refl. Qed.
Lemma D_270cc8 : decode_any W_270cc8 = Some (Branch BC_LTU 25 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ccc : bv 32 := 0x00048593.
Lemma F_270ccc : fetch_word Plain.M.loaded_segments (0x270d10 : word) = Some W_270ccc.
Proof. vm_refl. Qed.
Lemma D_270ccc : decode_any W_270ccc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270cd0 : bv 32 := 0x000b8513.
Lemma F_270cd0 : fetch_word Plain.M.loaded_segments (0x270d14 : word) = Some W_270cd0.
Proof. vm_refl. Qed.
Lemma D_270cd0 : decode_any W_270cd0 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270cd4 : bv 32 := 0x3f0060ef.
Lemma F_270cd4 : fetch_word Plain.M.loaded_segments (0x270d18 : word) = Some W_270cd4.
Proof. vm_refl. Qed.
Lemma D_270cd4 : decode_any W_270cd4 = Some (Jal 1 25584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270cd8 : bv 32 := 0x00ab85b3.
Lemma F_270cd8 : fetch_word Plain.M.loaded_segments (0x270d1c : word) = Some W_270cd8.
Proof. vm_refl. Qed.
Lemma D_270cd8 : decode_any W_270cd8 = Some (Op ALU_ADD 11 23 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270cdc : bv 32 := 0x000cd663.
Lemma F_270cdc : fetch_word Plain.M.loaded_segments (0x270d20 : word) = Some W_270cdc.
Proof. vm_refl. Qed.
Lemma D_270cdc : decode_any W_270cdc = Some (Branch BC_GE 25 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ce0 : bv 32 := 0x0005c603.
Lemma F_270ce0 : fetch_word Plain.M.loaded_segments (0x270d24 : word) = Some W_270ce0.
Proof. vm_refl. Qed.
Lemma D_270ce0 : decode_any W_270ce0 = Some (Load SZ1 false 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ce4 : bv 32 := 0x64061a63.
Lemma F_270ce4 : fetch_word Plain.M.loaded_segments (0x270d28 : word) = Some W_270ce4.
Proof. vm_refl. Qed.
Lemma D_270ce4 : decode_any W_270ce4 = Some (Branch BC_NE 12 0 1620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ce8 : bv 32 := 0x00013c23.
Lemma F_270ce8 : fetch_word Plain.M.loaded_segments (0x270d2c : word) = Some W_270ce8.
Proof. vm_refl. Qed.
Lemma D_270ce8 : decode_any W_270ce8 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270cec : bv 32 := 0xffda1617.
Lemma F_270cec : fetch_word Plain.M.loaded_segments (0x270d30 : word) = Some W_270cec.
Proof. vm_refl. Qed.
Lemma D_270cec : decode_any W_270cec = Some (Auipc 12 1047969, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270cf0 : bv 32 := 0x96a60613.
Lemma F_270cf0 : fetch_word Plain.M.loaded_segments (0x270d34 : word) = Some W_270cf0.
Proof. vm_refl. Qed.
Lemma D_270cf0 : decode_any W_270cf0 = Some (OpImm ALU_ADD 12 12 2410, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270cf4 : bv 32 := 0x00c13023.
Lemma F_270cf4 : fetch_word Plain.M.loaded_segments (0x270d38 : word) = Some W_270cf4.
Proof. vm_refl. Qed.
Lemma D_270cf4 : decode_any W_270cf4 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270cf8 : bv 32 := 0x000d0c13.
Lemma F_270cf8 : fetch_word Plain.M.loaded_segments (0x270d3c : word) = Some W_270cf8.
Proof. vm_refl. Qed.
Lemma D_270cf8 : decode_any W_270cf8 = Some (OpImm ALU_ADD 24 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270cfc : bv 32 := 0x30c0006f.
Lemma F_270cfc : fetch_word Plain.M.loaded_segments (0x270d40 : word) = Some W_270cfc.
Proof. vm_refl. Qed.
Lemma D_270cfc : decode_any W_270cfc = Some (Jal 0 780, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d00 : bv 32 := 0x07013503.
Lemma F_270d00 : fetch_word Plain.M.loaded_segments (0x270d44 : word) = Some W_270d00.
Proof. vm_refl. Qed.
Lemma D_270d00 : decode_any W_270d00 = Some (Load SZ8 true 10 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d04 : bv 32 := 0x0b010b93.
Lemma F_270d04 : fetch_word Plain.M.loaded_segments (0x270d48 : word) = Some W_270d04.
Proof. vm_refl. Qed.
Lemma D_270d04 : decode_any W_270d04 = Some (OpImm ALU_ADD 23 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d08 : bv 32 := 0x02050263.
Lemma F_270d08 : fetch_word Plain.M.loaded_segments (0x270d4c : word) = Some W_270d08.
Proof. vm_refl. Qed.
Lemma D_270d08 : decode_any W_270d08 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d0c : bv 32 := 0x0b010593.
Lemma F_270d0c : fetch_word Plain.M.loaded_segments (0x270d50 : word) = Some W_270d0c.
Proof. vm_refl. Qed.
Lemma D_270d0c : decode_any W_270d0c = Some (OpImm ALU_ADD 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d10 : bv 32 := 0x00757613.
Lemma F_270d10 : fetch_word Plain.M.loaded_segments (0x270d54 : word) = Some W_270d10.
Proof. vm_refl. Qed.
Lemma D_270d10 : decode_any W_270d10 = Some (OpImm ALU_AND 12 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d14 : bv 32 := 0xfff58b93.
Lemma F_270d14 : fetch_word Plain.M.loaded_segments (0x270d58 : word) = Some W_270d14.
Proof. vm_refl. Qed.
Lemma D_270d14 : decode_any W_270d14 = Some (OpImm ALU_ADD 23 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d18 : bv 32 := 0x03060613.
Lemma F_270d18 : fetch_word Plain.M.loaded_segments (0x270d5c : word) = Some W_270d18.
Proof. vm_refl. Qed.
Lemma D_270d18 : decode_any W_270d18 = Some (OpImm ALU_ADD 12 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d1c : bv 32 := 0x00355513.
Lemma F_270d1c : fetch_word Plain.M.loaded_segments (0x270d60 : word) = Some W_270d1c.
Proof. vm_refl. Qed.
Lemma D_270d1c : decode_any W_270d1c = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d20 : bv 32 := 0xfec58fa3.
Lemma F_270d20 : fetch_word Plain.M.loaded_segments (0x270d64 : word) = Some W_270d20.
Proof. vm_refl. Qed.
Lemma D_270d20 : decode_any W_270d20 = Some (Store SZ1 11 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d24 : bv 32 := 0x000b8593.
Lemma F_270d24 : fetch_word Plain.M.loaded_segments (0x270d68 : word) = Some W_270d24.
Proof. vm_refl. Qed.
Lemma D_270d24 : decode_any W_270d24 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d28 : bv 32 := 0xfe0514e3.
Lemma F_270d28 : fetch_word Plain.M.loaded_segments (0x270d6c : word) = Some W_270d28.
Proof. vm_refl. Qed.
Lemma D_270d28 : decode_any W_270d28 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d2c : bv 32 := 0x008c7513.
Lemma F_270d2c : fetch_word Plain.M.loaded_segments (0x270d70 : word) = Some W_270d2c.
Proof. vm_refl. Qed.
Lemma D_270d2c : decode_any W_270d2c = Some (OpImm ALU_AND 10 24 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d30 : bv 32 := 0xffda1597.
Lemma F_270d30 : fetch_word Plain.M.loaded_segments (0x270d74 : word) = Some W_270d30.
Proof. vm_refl. Qed.
Lemma D_270d30 : decode_any W_270d30 = Some (Auipc 11 1047969, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d34 : bv 32 := 0x92658593.
Lemma F_270d34 : fetch_word Plain.M.loaded_segments (0x270d78 : word) = Some W_270d34.
Proof. vm_refl. Qed.
Lemma D_270d34 : decode_any W_270d34 = Some (OpImm ALU_ADD 11 11 2342, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d38 : bv 32 := 0x00b13023.
Lemma F_270d38 : fetch_word Plain.M.loaded_segments (0x270d7c : word) = Some W_270d38.
Proof. vm_refl. Qed.
Lemma D_270d38 : decode_any W_270d38 = Some (Store SZ8 2 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d3c : bv 32 := 0x00050863.
Lemma F_270d3c : fetch_word Plain.M.loaded_segments (0x270d80 : word) = Some W_270d3c.
Proof. vm_refl. Qed.
Lemma D_270d3c : decode_any W_270d3c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d40 : bv 32 := 0x0b010513.
Lemma F_270d40 : fetch_word Plain.M.loaded_segments (0x270d84 : word) = Some W_270d40.
Proof. vm_refl. Qed.
Lemma D_270d40 : decode_any W_270d40 = Some (OpImm ALU_ADD 10 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d44 : bv 32 := 0x41750533.
Lemma F_270d44 : fetch_word Plain.M.loaded_segments (0x270d88 : word) = Some W_270d44.
Proof. vm_refl. Qed.
Lemma D_270d44 : decode_any W_270d44 = Some (Op ALU_SUB 10 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d48 : bv 32 := 0x5b955a63.
Lemma F_270d48 : fetch_word Plain.M.loaded_segments (0x270d8c : word) = Some W_270d48.
Proof. vm_refl. Qed.
Lemma D_270d48 : decode_any W_270d48 = Some (Branch BC_GE 10 25 1460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d4c : bv 32 := 0x00013c23.
Lemma F_270d4c : fetch_word Plain.M.loaded_segments (0x270d90 : word) = Some W_270d4c.
Proof. vm_refl. Qed.
Lemma D_270d4c : decode_any W_270d4c = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d50 : bv 32 := 0x26c0006f.
Lemma F_270d50 : fetch_word Plain.M.loaded_segments (0x270d94 : word) = Some W_270d50.
Proof. vm_refl. Qed.
Lemma D_270d50 : decode_any W_270d50 = Some (Jal 0 620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d54 : bv 32 := 0x0ffdf513.
Lemma F_270d54 : fetch_word Plain.M.loaded_segments (0x270d98 : word) = Some W_270d54.
Proof. vm_refl. Qed.
Lemma D_270d54 : decode_any W_270d54 = Some (OpImm ALU_AND 10 27 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d58 : bv 32 := 0x00000d13.
Lemma F_270d58 : fetch_word Plain.M.loaded_segments (0x270d9c : word) = Some W_270d58.
Proof. vm_refl. Qed.
Lemma D_270d58 : decode_any W_270d58 = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d5c : bv 32 := 0x00700593.
Lemma F_270d5c : fetch_word Plain.M.loaded_segments (0x270da0 : word) = Some W_270d5c.
Proof. vm_refl. Qed.
Lemma D_270d5c : decode_any W_270d5c = Some (OpImm ALU_ADD 11 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d60 : bv 32 := 0xa0a5e8e3.
Lemma F_270d60 : fetch_word Plain.M.loaded_segments (0x270da4 : word) = Some W_270d60.
Proof. vm_refl. Qed.
Lemma D_270d60 : decode_any W_270d60 = Some (Branch BC_LTU 11 10 6672, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d64 : bv 32 := 0x00251513.
Lemma F_270d64 : fetch_word Plain.M.loaded_segments (0x270da8 : word) = Some W_270d64.
Proof. vm_refl. Qed.
Lemma D_270d64 : decode_any W_270d64 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d68 : bv 32 := 0xffe01597.
Lemma F_270d68 : fetch_word Plain.M.loaded_segments (0x270dac : word) = Some W_270d68.
Proof. vm_refl. Qed.
Lemma D_270d68 : decode_any W_270d68 = Some (Auipc 11 1048065, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d6c : bv 32 := 0x20c58593.
Lemma F_270d6c : fetch_word Plain.M.loaded_segments (0x270db0 : word) = Some W_270d6c.
Proof. vm_refl. Qed.
Lemma D_270d6c : decode_any W_270d6c = Some (OpImm ALU_ADD 11 11 524, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d70 : bv 32 := 0x00b50533.
Lemma F_270d70 : fetch_word Plain.M.loaded_segments (0x270db4 : word) = Some W_270d70.
Proof. vm_refl. Qed.
Lemma D_270d70 : decode_any W_270d70 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d74 : bv 32 := 0x00052503.
Lemma F_270d74 : fetch_word Plain.M.loaded_segments (0x270db8 : word) = Some W_270d74.
Proof. vm_refl. Qed.
Lemma D_270d74 : decode_any W_270d74 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d78 : bv 32 := 0x00b50533.
Lemma F_270d78 : fetch_word Plain.M.loaded_segments (0x270dbc : word) = Some W_270d78.
Proof. vm_refl. Qed.
Lemma D_270d78 : decode_any W_270d78 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d7c : bv 32 := 0x00050067.
Lemma F_270d7c : fetch_word Plain.M.loaded_segments (0x270dc0 : word) = Some W_270d7c.
Proof. vm_refl. Qed.
Lemma D_270d7c : decode_any W_270d7c = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d80 : bv 32 := 0x00000d13.
Lemma F_270d80 : fetch_word Plain.M.loaded_segments (0x270dc4 : word) = Some W_270d80.
Proof. vm_refl. Qed.
Lemma D_270d80 : decode_any W_270d80 = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d84 : bv 32 := 0x07013503.
Lemma F_270d84 : fetch_word Plain.M.loaded_segments (0x270dc8 : word) = Some W_270d84.
Proof. vm_refl. Qed.
Lemma D_270d84 : decode_any W_270d84 = Some (Load SZ8 true 10 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d88 : bv 32 := 0x01353023.
Lemma F_270d88 : fetch_word Plain.M.loaded_segments (0x270dcc : word) = Some W_270d88.
Proof. vm_refl. Qed.
Lemma D_270d88 : decode_any W_270d88 = Some (Store SZ8 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d8c : bv 32 := 0x9e5ff06f.
Lemma F_270d8c : fetch_word Plain.M.loaded_segments (0x270dd0 : word) = Some W_270d8c.
Proof. vm_refl. Qed.
Lemma D_270d8c : decode_any W_270d8c = Some (Jal 0 2095588, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d90 : bv 32 := 0x00013c23.
Lemma F_270d90 : fetch_word Plain.M.loaded_segments (0x270dd4 : word) = Some W_270d90.
Proof. vm_refl. Qed.
Lemma D_270d90 : decode_any W_270d90 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d94 : bv 32 := 0x07013503.
Lemma F_270d94 : fetch_word Plain.M.loaded_segments (0x270dd8 : word) = Some W_270d94.
Proof. vm_refl. Qed.
Lemma D_270d94 : decode_any W_270d94 = Some (Load SZ8 true 10 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d98 : bv 32 := 0xffda1597.
Lemma F_270d98 : fetch_word Plain.M.loaded_segments (0x270ddc : word) = Some W_270d98.
Proof. vm_refl. Qed.
Lemma D_270d98 : decode_any W_270d98 = Some (Auipc 11 1047969, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270d9c : bv 32 := 0x8be58893.
Lemma F_270d9c : fetch_word Plain.M.loaded_segments (0x270de0 : word) = Some W_270d9c.
Proof. vm_refl. Qed.
Lemma D_270d9c : decode_any W_270d9c = Some (OpImm ALU_ADD 17 11 2238, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270da0 : bv 32 := 0x00a00713.
Lemma F_270da0 : fetch_word Plain.M.loaded_segments (0x270de4 : word) = Some W_270da0.
Proof. vm_refl. Qed.
Lemma D_270da0 : decode_any W_270da0 = Some (OpImm ALU_ADD 14 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270da4 : bv 32 := 0x1b80006f.
Lemma F_270da4 : fetch_word Plain.M.loaded_segments (0x270de8 : word) = Some W_270da4.
Proof. vm_refl. Qed.
Lemma D_270da4 : decode_any W_270da4 = Some (Jal 0 440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270da8 : bv 32 := 0x07013503.
Lemma F_270da8 : fetch_word Plain.M.loaded_segments (0x270dec : word) = Some W_270da8.
Proof. vm_refl. Qed.
Lemma D_270da8 : decode_any W_270da8 = Some (Load SZ8 true 10 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270dac : bv 32 := 0x02050063.
Lemma F_270dac : fetch_word Plain.M.loaded_segments (0x270df0 : word) = Some W_270dac.
Proof. vm_refl. Qed.
Lemma D_270dac : decode_any W_270dac = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270db0 : bv 32 := 0x08a12823.
Lemma F_270db0 : fetch_word Plain.M.loaded_segments (0x270df4 : word) = Some W_270db0.
Proof. vm_refl. Qed.
Lemma D_270db0 : decode_any W_270db0 = Some (Store SZ4 2 10 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270db4 : bv 32 := 0x08012a23.
Lemma F_270db4 : fetch_word Plain.M.loaded_segments (0x270df8 : word) = Some W_270db4.
Proof. vm_refl. Qed.
Lemma D_270db4 : decode_any W_270db4 = Some (Store SZ4 2 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270db8 : bv 32 := 0x09010913.
Lemma F_270db8 : fetch_word Plain.M.loaded_segments (0x270dfc : word) = Some W_270db8.
Proof. vm_refl. Qed.
Lemma D_270db8 : decode_any W_270db8 = Some (OpImm ALU_ADD 18 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270dbc : bv 32 := 0x07213823.
Lemma F_270dbc : fetch_word Plain.M.loaded_segments (0x270e00 : word) = Some W_270dbc.
Proof. vm_refl. Qed.
Lemma D_270dbc : decode_any W_270dbc = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270dc0 : bv 32 := 0xfff00c93.
Lemma F_270dc0 : fetch_word Plain.M.loaded_segments (0x270e04 : word) = Some W_270dc0.
Proof. vm_refl. Qed.
Lemma D_270dc0 : decode_any W_270dc0 = Some (OpImm ALU_ADD 25 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270dc4 : bv 32 := 0x0b00006f.
Lemma F_270dc4 : fetch_word Plain.M.loaded_segments (0x270e08 : word) = Some W_270dc4.
Proof. vm_refl. Qed.
Lemma D_270dc4 : decode_any W_270dc4 = Some (Jal 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270dc8 : bv 32 := 0x07013503.
Lemma F_270dc8 : fetch_word Plain.M.loaded_segments (0x270e0c : word) = Some W_270dc8.
Proof. vm_refl. Qed.
Lemma D_270dc8 : decode_any W_270dc8 = Some (Load SZ8 true 10 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270dcc : bv 32 := 0x00013c23.
Lemma F_270dcc : fetch_word Plain.M.loaded_segments (0x270e10 : word) = Some W_270dcc.
Proof. vm_refl. Qed.
Lemma D_270dcc : decode_any W_270dcc = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270dd0 : bv 32 := 0x0aa107a3.
Lemma F_270dd0 : fetch_word Plain.M.loaded_segments (0x270e14 : word) = Some W_270dd0.
Proof. vm_refl. Qed.
Lemma D_270dd0 : decode_any W_270dd0 = Some (Store SZ1 2 10 175, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270dd4 : bv 32 := 0xffda1517.
Lemma F_270dd4 : fetch_word Plain.M.loaded_segments (0x270e18 : word) = Some W_270dd4.
Proof. vm_refl. Qed.
Lemma D_270dd4 : decode_any W_270dd4 = Some (Auipc 10 1047969, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270dd8 : bv 32 := 0x88250513.
Lemma F_270dd8 : fetch_word Plain.M.loaded_segments (0x270e1c : word) = Some W_270dd8.
Proof. vm_refl. Qed.
Lemma D_270dd8 : decode_any W_270dd8 = Some (OpImm ALU_ADD 10 10 2178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ddc : bv 32 := 0x00a13023.
Lemma F_270ddc : fetch_word Plain.M.loaded_segments (0x270e20 : word) = Some W_270ddc.
Proof. vm_refl. Qed.
Lemma D_270ddc : decode_any W_270ddc = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270de0 : bv 32 := 0x00100c93.
Lemma F_270de0 : fetch_word Plain.M.loaded_segments (0x270e24 : word) = Some W_270de0.
Proof. vm_refl. Qed.
Lemma D_270de0 : decode_any W_270de0 = Some (OpImm ALU_ADD 25 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270de4 : bv 32 := 0x0b010593.
Lemma F_270de4 : fetch_word Plain.M.loaded_segments (0x270e28 : word) = Some W_270de4.
Proof. vm_refl. Qed.
Lemma D_270de4 : decode_any W_270de4 = Some (OpImm ALU_ADD 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270de8 : bv 32 := 0x0af10b93.
Lemma F_270de8 : fetch_word Plain.M.loaded_segments (0x270e2c : word) = Some W_270de8.
Proof. vm_refl. Qed.
Lemma D_270de8 : decode_any W_270de8 = Some (OpImm ALU_ADD 23 2 175, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270dec : bv 32 := 0x000d0c13.
Lemma F_270dec : fetch_word Plain.M.loaded_segments (0x270e30 : word) = Some W_270dec.
Proof. vm_refl. Qed.
Lemma D_270dec : decode_any W_270dec = Some (OpImm ALU_ADD 24 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270df0 : bv 32 := 0x21c0006f.
Lemma F_270df0 : fetch_word Plain.M.loaded_segments (0x270e34 : word) = Some W_270df0.
Proof. vm_refl. Qed.
Lemma D_270df0 : decode_any W_270df0 = Some (Jal 0 540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270df4 : bv 32 := 0x01000513.
Lemma F_270df4 : fetch_word Plain.M.loaded_segments (0x270e38 : word) = Some W_270df4.
Proof. vm_refl. Qed.
Lemma D_270df4 : decode_any W_270df4 = Some (OpImm ALU_ADD 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270df8 : bv 32 := 0x01956463.
Lemma F_270df8 : fetch_word Plain.M.loaded_segments (0x270e3c : word) = Some W_270df8.
Proof. vm_refl. Qed.
Lemma D_270df8 : decode_any W_270df8 = Some (Branch BC_LTU 10 25 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270dfc : bv 32 := 0x01000c93.
Lemma F_270dfc : fetch_word Plain.M.loaded_segments (0x270e40 : word) = Some W_270dfc.
Proof. vm_refl. Qed.
Lemma D_270dfc : decode_any W_270dfc = Some (OpImm ALU_ADD 25 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e00 : bv 32 := 0x008c6c13.
Lemma F_270e00 : fetch_word Plain.M.loaded_segments (0x270e44 : word) = Some W_270e00.
Proof. vm_refl. Qed.
Lemma D_270e00 : decode_any W_270e00 = Some (OpImm ALU_OR 24 24 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e04 : bv 32 := 0x07800813.
Lemma F_270e04 : fetch_word Plain.M.loaded_segments (0x270e48 : word) = Some W_270e04.
Proof. vm_refl. Qed.
Lemma D_270e04 : decode_any W_270e04 = Some (OpImm ALU_ADD 16 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e08 : bv 32 := 0x07013503.
Lemma F_270e08 : fetch_word Plain.M.loaded_segments (0x270e4c : word) = Some W_270e08.
Proof. vm_refl. Qed.
Lemma D_270e08 : decode_any W_270e08 = Some (Load SZ8 true 10 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e0c : bv 32 := 0xffda1597.
Lemma F_270e0c : fetch_word Plain.M.loaded_segments (0x270e50 : word) = Some W_270e0c.
Proof. vm_refl. Qed.
Lemma D_270e0c : decode_any W_270e0c = Some (Auipc 11 1047969, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e10 : bv 32 := 0x84a58713.
Lemma F_270e10 : fetch_word Plain.M.loaded_segments (0x270e54 : word) = Some W_270e10.
Proof. vm_refl. Qed.
Lemma D_270e10 : decode_any W_270e10 = Some (OpImm ALU_ADD 14 11 2122, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e14 : bv 32 := 0x04050463.
Lemma F_270e14 : fetch_word Plain.M.loaded_segments (0x270e58 : word) = Some W_270e14.
Proof. vm_refl. Qed.
Lemma D_270e14 : decode_any W_270e14 = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e18 : bv 32 := 0x02087593.
Lemma F_270e18 : fetch_word Plain.M.loaded_segments (0x270e5c : word) = Some W_270e18.
Proof. vm_refl. Qed.
Lemma D_270e18 : decode_any W_270e18 = Some (OpImm ALU_AND 11 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e1c : bv 32 := 0x0b010b93.
Lemma F_270e1c : fetch_word Plain.M.loaded_segments (0x270e60 : word) = Some W_270e1c.
Proof. vm_refl. Qed.
Lemma D_270e1c : decode_any W_270e1c = Some (OpImm ALU_ADD 23 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e20 : bv 32 := 0x00f57613.
Lemma F_270e20 : fetch_word Plain.M.loaded_segments (0x270e64 : word) = Some W_270e20.
Proof. vm_refl. Qed.
Lemma D_270e20 : decode_any W_270e20 = Some (OpImm ALU_AND 12 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e24 : bv 32 := 0xffdda697.
Lemma F_270e24 : fetch_word Plain.M.loaded_segments (0x270e68 : word) = Some W_270e24.
Proof. vm_refl. Qed.
Lemma D_270e24 : decode_any W_270e24 = Some (Auipc 13 1048026, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e28 : bv 32 := 0x65868693.
Lemma F_270e28 : fetch_word Plain.M.loaded_segments (0x270e6c : word) = Some W_270e28.
Proof. vm_refl. Qed.
Lemma D_270e28 : decode_any W_270e28 = Some (OpImm ALU_ADD 13 13 1624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e2c : bv 32 := 0x00c68633.
Lemma F_270e2c : fetch_word Plain.M.loaded_segments (0x270e70 : word) = Some W_270e2c.
Proof. vm_refl. Qed.
Lemma D_270e2c : decode_any W_270e2c = Some (Op ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e30 : bv 32 := 0x00064603.
Lemma F_270e30 : fetch_word Plain.M.loaded_segments (0x270e74 : word) = Some W_270e30.
Proof. vm_refl. Qed.
Lemma D_270e30 : decode_any W_270e30 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e34 : bv 32 := 0x00455513.
Lemma F_270e34 : fetch_word Plain.M.loaded_segments (0x270e78 : word) = Some W_270e34.
Proof. vm_refl. Qed.
Lemma D_270e34 : decode_any W_270e34 = Some (ShiftImm ALU_SRL 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e38 : bv 32 := 0x00b66633.
Lemma F_270e38 : fetch_word Plain.M.loaded_segments (0x270e7c : word) = Some W_270e38.
Proof. vm_refl. Qed.
Lemma D_270e38 : decode_any W_270e38 = Some (Op ALU_OR 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e3c : bv 32 := 0xfecb8fa3.
Lemma F_270e3c : fetch_word Plain.M.loaded_segments (0x270e80 : word) = Some W_270e3c.
Proof. vm_refl. Qed.
Lemma D_270e3c : decode_any W_270e3c = Some (Store SZ1 23 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e40 : bv 32 := 0xfffb8b93.
Lemma F_270e40 : fetch_word Plain.M.loaded_segments (0x270e84 : word) = Some W_270e40.
Proof. vm_refl. Qed.
Lemma D_270e40 : decode_any W_270e40 = Some (OpImm ALU_ADD 23 23 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e44 : bv 32 := 0xfc051ee3.
Lemma F_270e44 : fetch_word Plain.M.loaded_segments (0x270e88 : word) = Some W_270e44.
Proof. vm_refl. Qed.
Lemma D_270e44 : decode_any W_270e44 = Some (Branch BC_NE 10 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e48 : bv 32 := 0x008c7513.
Lemma F_270e48 : fetch_word Plain.M.loaded_segments (0x270e8c : word) = Some W_270e48.
Proof. vm_refl. Qed.
Lemma D_270e48 : decode_any W_270e48 = Some (OpImm ALU_AND 10 24 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e4c : bv 32 := 0x0c051263.
Lemma F_270e4c : fetch_word Plain.M.loaded_segments (0x270e90 : word) = Some W_270e4c.
Proof. vm_refl. Qed.
Lemma D_270e4c : decode_any W_270e4c = Some (Branch BC_NE 10 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e50 : bv 32 := 0x00e13023.
Lemma F_270e50 : fetch_word Plain.M.loaded_segments (0x270e94 : word) = Some W_270e50.
Proof. vm_refl. Qed.
Lemma D_270e50 : decode_any W_270e50 = Some (Store SZ8 2 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e54 : bv 32 := 0x00013c23.
Lemma F_270e54 : fetch_word Plain.M.loaded_segments (0x270e98 : word) = Some W_270e54.
Proof. vm_refl. Qed.
Lemma D_270e54 : decode_any W_270e54 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e58 : bv 32 := 0x1640006f.
Lemma F_270e58 : fetch_word Plain.M.loaded_segments (0x270e9c : word) = Some W_270e58.
Proof. vm_refl. Qed.
Lemma D_270e58 : decode_any W_270e58 = Some (Jal 0 356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e5c : bv 32 := 0x00e13023.
Lemma F_270e5c : fetch_word Plain.M.loaded_segments (0x270ea0 : word) = Some W_270e5c.
Proof. vm_refl. Qed.
Lemma D_270e5c : decode_any W_270e5c = Some (Store SZ8 2 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e60 : bv 32 := 0x00013c23.
Lemma F_270e60 : fetch_word Plain.M.loaded_segments (0x270ea4 : word) = Some W_270e60.
Proof. vm_refl. Qed.
Lemma D_270e60 : decode_any W_270e60 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e64 : bv 32 := 0x0b010b93.
Lemma F_270e64 : fetch_word Plain.M.loaded_segments (0x270ea8 : word) = Some W_270e64.
Proof. vm_refl. Qed.
Lemma D_270e64 : decode_any W_270e64 = Some (OpImm ALU_ADD 23 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e68 : bv 32 := 0x1540006f.
Lemma F_270e68 : fetch_word Plain.M.loaded_segments (0x270eac : word) = Some W_270e68.
Proof. vm_refl. Qed.
Lemma D_270e68 : decode_any W_270e68 = Some (Jal 0 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e6c : bv 32 := 0x440c8263.
Lemma F_270e6c : fetch_word Plain.M.loaded_segments (0x270eb0 : word) = Some W_270e6c.
Proof. vm_refl. Qed.
Lemma D_270e6c : decode_any W_270e6c = Some (Branch BC_EQ 25 0 1092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e70 : bv 32 := 0x07013903.
Lemma F_270e70 : fetch_word Plain.M.loaded_segments (0x270eb4 : word) = Some W_270e70.
Proof. vm_refl. Qed.
Lemma D_270e70 : decode_any W_270e70 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e74 : bv 32 := 0x00000b93.
Lemma F_270e74 : fetch_word Plain.M.loaded_segments (0x270eb8 : word) = Some W_270e74.
Proof. vm_refl. Qed.
Lemma D_270e74 : decode_any W_270e74 = Some (OpImm ALU_ADD 23 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e78 : bv 32 := 0x00090d13.
Lemma F_270e78 : fetch_word Plain.M.loaded_segments (0x270ebc : word) = Some W_270e78.
Proof. vm_refl. Qed.
Lemma D_270e78 : decode_any W_270e78 = Some (OpImm ALU_ADD 26 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e7c : bv 32 := 0x000d2583.
Lemma F_270e7c : fetch_word Plain.M.loaded_segments (0x270ec0 : word) = Some W_270e7c.
Proof. vm_refl. Qed.
Lemma D_270e7c : decode_any W_270e7c = Some (Load SZ4 true 11 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e80 : bv 32 := 0x02058263.
Lemma F_270e80 : fetch_word Plain.M.loaded_segments (0x270ec4 : word) = Some W_270e80.
Proof. vm_refl. Qed.
Lemma D_270e80 : decode_any W_270e80 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e84 : bv 32 := 0x08c10513.
Lemma F_270e84 : fetch_word Plain.M.loaded_segments (0x270ec8 : word) = Some W_270e84.
Proof. vm_refl. Qed.
Lemma D_270e84 : decode_any W_270e84 = Some (OpImm ALU_ADD 10 2 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e88 : bv 32 := 0x775010ef.
Lemma F_270e88 : fetch_word Plain.M.loaded_segments (0x270ecc : word) = Some W_270e88.
Proof. vm_refl. Qed.
Lemma D_270e88 : decode_any W_270e88 = Some (Jal 1 8052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e8c : bv 32 := 0x60054663.
Lemma F_270e8c : fetch_word Plain.M.loaded_segments (0x270ed0 : word) = Some W_270e8c.
Proof. vm_refl. Qed.
Lemma D_270e8c : decode_any W_270e8c = Some (Branch BC_LT 10 0 1548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e90 : bv 32 := 0x417c85b3.
Lemma F_270e90 : fetch_word Plain.M.loaded_segments (0x270ed4 : word) = Some W_270e90.
Proof. vm_refl. Qed.
Lemma D_270e90 : decode_any W_270e90 = Some (Op ALU_SUB 11 25 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e94 : bv 32 := 0x00a5e863.
Lemma F_270e94 : fetch_word Plain.M.loaded_segments (0x270ed8 : word) = Some W_270e94.
Proof. vm_refl. Qed.
Lemma D_270e94 : decode_any W_270e94 = Some (Branch BC_LTU 11 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e98 : bv 32 := 0x00ab8bb3.
Lemma F_270e98 : fetch_word Plain.M.loaded_segments (0x270edc : word) = Some W_270e98.
Proof. vm_refl. Qed.
Lemma D_270e98 : decode_any W_270e98 = Some (Op ALU_ADD 23 23 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270e9c : bv 32 := 0x004d0d13.
Lemma F_270e9c : fetch_word Plain.M.loaded_segments (0x270ee0 : word) = Some W_270e9c.
Proof. vm_refl. Qed.
Lemma D_270e9c : decode_any W_270e9c = Some (OpImm ALU_ADD 26 26 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ea0 : bv 32 := 0xfd9beee3.
Lemma F_270ea0 : fetch_word Plain.M.loaded_segments (0x270ee4 : word) = Some W_270ea0.
Proof. vm_refl. Qed.
Lemma D_270ea0 : decode_any W_270ea0 = Some (Branch BC_LTU 23 25 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ea4 : bv 32 := 0x01fbd513.
Lemma F_270ea4 : fetch_word Plain.M.loaded_segments (0x270ee8 : word) = Some W_270ea4.
Proof. vm_refl. Qed.
Lemma D_270ea4 : decode_any W_270ea4 = Some (ShiftImm ALU_SRL 10 23 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ea8 : bv 32 := 0x48051863.
Lemma F_270ea8 : fetch_word Plain.M.loaded_segments (0x270eec : word) = Some W_270ea8.
Proof. vm_refl. Qed.
Lemma D_270ea8 : decode_any W_270ea8 = Some (Branch BC_NE 10 0 1168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270eac : bv 32 := 0x02000593.
Lemma F_270eac : fetch_word Plain.M.loaded_segments (0x270ef0 : word) = Some W_270eac.
Proof. vm_refl. Qed.
Lemma D_270eac : decode_any W_270eac = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270eb0 : bv 32 := 0x000a0513.
Lemma F_270eb0 : fetch_word Plain.M.loaded_segments (0x270ef4 : word) = Some W_270eb0.
Proof. vm_refl. Qed.
Lemma D_270eb0 : decode_any W_270eb0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270eb4 : bv 32 := 0x000b0613.
Lemma F_270eb4 : fetch_word Plain.M.loaded_segments (0x270ef8 : word) = Some W_270eb4.
Proof. vm_refl. Qed.
Lemma D_270eb4 : decode_any W_270eb4 = Some (OpImm ALU_ADD 12 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270eb8 : bv 32 := 0x000b8693.
Lemma F_270eb8 : fetch_word Plain.M.loaded_segments (0x270efc : word) = Some W_270eb8.
Proof. vm_refl. Qed.
Lemma D_270eb8 : decode_any W_270eb8 = Some (OpImm ALU_ADD 13 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ebc : bv 32 := 0x000c0713.
Lemma F_270ebc : fetch_word Plain.M.loaded_segments (0x270f00 : word) = Some W_270ebc.
Proof. vm_refl. Qed.
Lemma D_270ebc : decode_any W_270ebc = Some (OpImm ALU_ADD 14 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ec0 : bv 32 := 0x764000ef.
Lemma F_270ec0 : fetch_word Plain.M.loaded_segments (0x270f04 : word) = Some W_270ec0.
Proof. vm_refl. Qed.
Lemma D_270ec0 : decode_any W_270ec0 = Some (Jal 1 1892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ec4 : bv 32 := 0x400b8463.
Lemma F_270ec4 : fetch_word Plain.M.loaded_segments (0x270f08 : word) = Some W_270ec4.
Proof. vm_refl. Qed.
Lemma D_270ec4 : decode_any W_270ec4 = Some (Branch BC_EQ 23 0 1032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ec8 : bv 32 := 0x00000c93.
Lemma F_270ec8 : fetch_word Plain.M.loaded_segments (0x270f0c : word) = Some W_270ec8.
Proof. vm_refl. Qed.
Lemma D_270ec8 : decode_any W_270ec8 = Some (OpImm ALU_ADD 25 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ecc : bv 32 := 0x00c0006f.
Lemma F_270ecc : fetch_word Plain.M.loaded_segments (0x270f10 : word) = Some W_270ecc.
Proof. vm_refl. Qed.
Lemma D_270ecc : decode_any W_270ecc = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ed0 : bv 32 := 0x00490913.
Lemma F_270ed0 : fetch_word Plain.M.loaded_segments (0x270f14 : word) = Some W_270ed0.
Proof. vm_refl. Qed.
Lemma D_270ed0 : decode_any W_270ed0 = Some (OpImm ALU_ADD 18 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ed4 : bv 32 := 0x3f7cfc63.
Lemma F_270ed4 : fetch_word Plain.M.loaded_segments (0x270f18 : word) = Some W_270ed4.
Proof. vm_refl. Qed.
Lemma D_270ed4 : decode_any W_270ed4 = Some (Branch BC_GEU 25 23 1016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ed8 : bv 32 := 0x00092583.
Lemma F_270ed8 : fetch_word Plain.M.loaded_segments (0x270f1c : word) = Some W_270ed8.
Proof. vm_refl. Qed.
Lemma D_270ed8 : decode_any W_270ed8 = Some (Load SZ4 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270edc : bv 32 := 0x3e058863.
Lemma F_270edc : fetch_word Plain.M.loaded_segments (0x270f20 : word) = Some W_270edc.
Proof. vm_refl. Qed.
Lemma D_270edc : decode_any W_270edc = Some (Branch BC_EQ 11 0 1008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ee0 : bv 32 := 0x08c10513.
Lemma F_270ee0 : fetch_word Plain.M.loaded_segments (0x270f24 : word) = Some W_270ee0.
Proof. vm_refl. Qed.
Lemma D_270ee0 : decode_any W_270ee0 = Some (OpImm ALU_ADD 10 2 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ee4 : bv 32 := 0x719010ef.
Lemma F_270ee4 : fetch_word Plain.M.loaded_segments (0x270f28 : word) = Some W_270ee4.
Proof. vm_refl. Qed.
Lemma D_270ee4 : decode_any W_270ee4 = Some (Jal 1 7960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ee8 : bv 32 := 0x00ac8cb3.
Lemma F_270ee8 : fetch_word Plain.M.loaded_segments (0x270f2c : word) = Some W_270ee8.
Proof. vm_refl. Qed.
Lemma D_270ee8 : decode_any W_270ee8 = Some (Op ALU_ADD 25 25 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270eec : bv 32 := 0x3f9be063.
Lemma F_270eec : fetch_word Plain.M.loaded_segments (0x270f30 : word) = Some W_270eec.
Proof. vm_refl. Qed.
Lemma D_270eec : decode_any W_270eec = Some (Branch BC_LTU 23 25 992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ef0 : bv 32 := 0x00050593.
Lemma F_270ef0 : fetch_word Plain.M.loaded_segments (0x270f34 : word) = Some W_270ef0.
Proof. vm_refl. Qed.
Lemma D_270ef0 : decode_any W_270ef0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ef4 : bv 32 := 0x000a4503.
Lemma F_270ef4 : fetch_word Plain.M.loaded_segments (0x270f38 : word) = Some W_270ef4.
Proof. vm_refl. Qed.
Lemma D_270ef4 : decode_any W_270ef4 = Some (Load SZ1 false 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ef8 : bv 32 := 0x02057513.
Lemma F_270ef8 : fetch_word Plain.M.loaded_segments (0x270f3c : word) = Some W_270ef8.
Proof. vm_refl. Qed.
Lemma D_270ef8 : decode_any W_270ef8 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270efc : bv 32 := 0xfc051ae3.
Lemma F_270efc : fetch_word Plain.M.loaded_segments (0x270f40 : word) = Some W_270efc.
Proof. vm_refl. Qed.
Lemma D_270efc : decode_any W_270efc = Some (Branch BC_NE 10 0 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f00 : bv 32 := 0x08c10513.
Lemma F_270f00 : fetch_word Plain.M.loaded_segments (0x270f44 : word) = Some W_270f00.
Proof. vm_refl. Qed.
Lemma D_270f00 : decode_any W_270f00 = Some (OpImm ALU_ADD 10 2 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f04 : bv 32 := 0x000a0613.
Lemma F_270f04 : fetch_word Plain.M.loaded_segments (0x270f48 : word) = Some W_270f04.
Proof. vm_refl. Qed.
Lemma D_270f04 : decode_any W_270f04 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f08 : bv 32 := 0xa9cff0ef.
Lemma F_270f08 : fetch_word Plain.M.loaded_segments (0x270f4c : word) = Some W_270f08.
Proof. vm_refl. Qed.
Lemma D_270f08 : decode_any W_270f08 = Some (Jal 1 2093724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f0c : bv 32 := 0xfc5ff06f.
Lemma F_270f0c : fetch_word Plain.M.loaded_segments (0x270f50 : word) = Some W_270f0c.
Proof. vm_refl. Qed.
Lemma D_270f0c : decode_any W_270f0c = Some (Jal 0 2097092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f10 : bv 32 := 0x00485513.
Lemma F_270f10 : fetch_word Plain.M.loaded_segments (0x270f54 : word) = Some W_270f10.
Proof. vm_refl. Qed.
Lemma D_270f10 : decode_any W_270f10 = Some (ShiftImm ALU_SRL 10 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f14 : bv 32 := 0xffda0597.
Lemma F_270f14 : fetch_word Plain.M.loaded_segments (0x270f58 : word) = Some W_270f14.
Proof. vm_refl. Qed.
Lemma D_270f14 : decode_any W_270f14 = Some (Auipc 11 1047968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f18 : bv 32 := 0x74258593.
Lemma F_270f18 : fetch_word Plain.M.loaded_segments (0x270f5c : word) = Some W_270f18.
Proof. vm_refl. Qed.
Lemma D_270f18 : decode_any W_270f18 = Some (OpImm ALU_ADD 11 11 1858, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f1c : bv 32 := 0x00a58533.
Lemma F_270f1c : fetch_word Plain.M.loaded_segments (0x270f60 : word) = Some W_270f1c.
Proof. vm_refl. Qed.
Lemma D_270f1c : decode_any W_270f1c = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f20 : bv 32 := 0x00a13023.
Lemma F_270f20 : fetch_word Plain.M.loaded_segments (0x270f64 : word) = Some W_270f20.
Proof. vm_refl. Qed.
Lemma D_270f20 : decode_any W_270f20 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f24 : bv 32 := 0x00200513.
Lemma F_270f24 : fetch_word Plain.M.loaded_segments (0x270f68 : word) = Some W_270f24.
Proof. vm_refl. Qed.
Lemma D_270f24 : decode_any W_270f24 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f28 : bv 32 := 0x00a13c23.
Lemma F_270f28 : fetch_word Plain.M.loaded_segments (0x270f6c : word) = Some W_270f28.
Proof. vm_refl. Qed.
Lemma D_270f28 : decode_any W_270f28 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f2c : bv 32 := 0x0900006f.
Lemma F_270f2c : fetch_word Plain.M.loaded_segments (0x270f70 : word) = Some W_270f2c.
Proof. vm_refl. Qed.
Lemma D_270f2c : decode_any W_270f2c = Some (Jal 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f30 : bv 32 := 0x40a00533.
Lemma F_270f30 : fetch_word Plain.M.loaded_segments (0x270f74 : word) = Some W_270f30.
Proof. vm_refl. Qed.
Lemma D_270f30 : decode_any W_270f30 = Some (Op ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f34 : bv 32 := 0x00100593.
Lemma F_270f34 : fetch_word Plain.M.loaded_segments (0x270f78 : word) = Some W_270f34.
Proof. vm_refl. Qed.
Lemma D_270f34 : decode_any W_270f34 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f38 : bv 32 := 0x00b13c23.
Lemma F_270f38 : fetch_word Plain.M.loaded_segments (0x270f7c : word) = Some W_270f38.
Proof. vm_refl. Qed.
Lemma D_270f38 : decode_any W_270f38 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f3c : bv 32 := 0xffda0597.
Lemma F_270f3c : fetch_word Plain.M.loaded_segments (0x270f80 : word) = Some W_270f3c.
Proof. vm_refl. Qed.
Lemma D_270f3c : decode_any W_270f3c = Some (Auipc 11 1047968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f40 : bv 32 := 0x06a13823.
Lemma F_270f40 : fetch_word Plain.M.loaded_segments (0x270f84 : word) = Some W_270f40.
Proof. vm_refl. Qed.
Lemma D_270f40 : decode_any W_270f40 = Some (Store SZ8 2 10 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f44 : bv 32 := 0x71a58893.
Lemma F_270f44 : fetch_word Plain.M.loaded_segments (0x270f88 : word) = Some W_270f44.
Proof. vm_refl. Qed.
Lemma D_270f44 : decode_any W_270f44 = Some (OpImm ALU_ADD 17 11 1818, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f48 : bv 32 := 0x00a00713.
Lemma F_270f48 : fetch_word Plain.M.loaded_segments (0x270f8c : word) = Some W_270f48.
Proof. vm_refl. Qed.
Lemma D_270f48 : decode_any W_270f48 = Some (OpImm ALU_ADD 14 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f4c : bv 32 := 0x0100006f.
Lemma F_270f4c : fetch_word Plain.M.loaded_segments (0x270f90 : word) = Some W_270f4c.
Proof. vm_refl. Qed.
Lemma D_270f4c : decode_any W_270f4c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f50 : bv 32 := 0x00158893.
Lemma F_270f50 : fetch_word Plain.M.loaded_segments (0x270f94 : word) = Some W_270f50.
Proof. vm_refl. Qed.
Lemma D_270f50 : decode_any W_270f50 = Some (OpImm ALU_ADD 17 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f54 : bv 32 := 0x00100593.
Lemma F_270f54 : fetch_word Plain.M.loaded_segments (0x270f98 : word) = Some W_270f54.
Proof. vm_refl. Qed.
Lemma D_270f54 : decode_any W_270f54 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f58 : bv 32 := 0x00b13c23.
Lemma F_270f58 : fetch_word Plain.M.loaded_segments (0x270f9c : word) = Some W_270f58.
Proof. vm_refl. Qed.
Lemma D_270f58 : decode_any W_270f58 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f5c : bv 32 := 0x02813783.
Lemma F_270f5c : fetch_word Plain.M.loaded_segments (0x270fa0 : word) = Some W_270f5c.
Proof. vm_refl. Qed.
Lemma D_270f5c : decode_any W_270f5c = Some (Load SZ8 true 15 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f60 : bv 32 := 0x06300813.
Lemma F_270f60 : fetch_word Plain.M.loaded_segments (0x270fa4 : word) = Some W_270f60.
Proof. vm_refl. Qed.
Lemma D_270f60 : decode_any W_270f60 = Some (OpImm ALU_ADD 16 0 99, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f64 : bv 32 := 0x02e56e63.
Lemma F_270f64 : fetch_word Plain.M.loaded_segments (0x270fa8 : word) = Some W_270f64.
Proof. vm_refl. Qed.
Lemma D_270f64 : decode_any W_270f64 = Some (Branch BC_LTU 10 14 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f68 : bv 32 := 0x0b010593.
Lemma F_270f68 : fetch_word Plain.M.loaded_segments (0x270fac : word) = Some W_270f68.
Proof. vm_refl. Qed.
Lemma D_270f68 : decode_any W_270f68 = Some (OpImm ALU_ADD 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f6c : bv 32 := 0x00050613.
Lemma F_270f6c : fetch_word Plain.M.loaded_segments (0x270fb0 : word) = Some W_270f6c.
Proof. vm_refl. Qed.
Lemma D_270f6c : decode_any W_270f6c = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f70 : bv 32 := 0x02079513.
Lemma F_270f70 : fetch_word Plain.M.loaded_segments (0x270fb4 : word) = Some W_270f70.
Proof. vm_refl. Qed.
Lemma D_270f70 : decode_any W_270f70 = Some (ShiftImm ALU_SLL 10 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f74 : bv 32 := 0x00a78533.
Lemma F_270f74 : fetch_word Plain.M.loaded_segments (0x270fb8 : word) = Some W_270f74.
Proof. vm_refl. Qed.
Lemma D_270f74 : decode_any W_270f74 = Some (Op ALU_ADD 10 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f78 : bv 32 := 0x02a63533.
Lemma F_270f78 : fetch_word Plain.M.loaded_segments (0x270fbc : word) = Some W_270f78.
Proof. vm_refl. Qed.
Lemma D_270f78 : decode_any W_270f78 = Some (Mul M_MULHU 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f7c : bv 32 := 0x00355513.
Lemma F_270f7c : fetch_word Plain.M.loaded_segments (0x270fc0 : word) = Some W_270f7c.
Proof. vm_refl. Qed.
Lemma D_270f7c : decode_any W_270f7c = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f80 : bv 32 := 0x02e506b3.
Lemma F_270f80 : fetch_word Plain.M.loaded_segments (0x270fc4 : word) = Some W_270f80.
Proof. vm_refl. Qed.
Lemma D_270f80 : decode_any W_270f80 = Some (Mul M_MUL 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f84 : bv 32 := 0x40d606bb.
Lemma F_270f84 : fetch_word Plain.M.loaded_segments (0x270fc8 : word) = Some W_270f84.
Proof. vm_refl. Qed.
Lemma D_270f84 : decode_any W_270f84 = Some (Op32 ALU_SUB 13 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f88 : bv 32 := 0x0306e693.
Lemma F_270f88 : fetch_word Plain.M.loaded_segments (0x270fcc : word) = Some W_270f88.
Proof. vm_refl. Qed.
Lemma D_270f88 : decode_any W_270f88 = Some (OpImm ALU_OR 13 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f8c : bv 32 := 0xfff58b93.
Lemma F_270f8c : fetch_word Plain.M.loaded_segments (0x270fd0 : word) = Some W_270f8c.
Proof. vm_refl. Qed.
Lemma D_270f8c : decode_any W_270f8c = Some (OpImm ALU_ADD 23 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f90 : bv 32 := 0xfed58fa3.
Lemma F_270f90 : fetch_word Plain.M.loaded_segments (0x270fd4 : word) = Some W_270f90.
Proof. vm_refl. Qed.
Lemma D_270f90 : decode_any W_270f90 = Some (Store SZ1 11 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f94 : bv 32 := 0x000b8593.
Lemma F_270f94 : fetch_word Plain.M.loaded_segments (0x270fd8 : word) = Some W_270f94.
Proof. vm_refl. Qed.
Lemma D_270f94 : decode_any W_270f94 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f98 : bv 32 := 0xfcc86ae3.
Lemma F_270f98 : fetch_word Plain.M.loaded_segments (0x270fdc : word) = Some W_270f98.
Proof. vm_refl. Qed.
Lemma D_270f98 : decode_any W_270f98 = Some (Branch BC_LTU 16 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270f9c : bv 32 := 0x0080006f.
Lemma F_270f9c : fetch_word Plain.M.loaded_segments (0x270fe0 : word) = Some W_270f9c.
Proof. vm_refl. Qed.
Lemma D_270f9c : decode_any W_270f9c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fa0 : bv 32 := 0x0b010b93.
Lemma F_270fa0 : fetch_word Plain.M.loaded_segments (0x270fe4 : word) = Some W_270fa0.
Proof. vm_refl. Qed.
Lemma D_270fa0 : decode_any W_270fa0 = Some (OpImm ALU_ADD 23 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fa4 : bv 32 := 0x01113023.
Lemma F_270fa4 : fetch_word Plain.M.loaded_segments (0x270fe8 : word) = Some W_270fa4.
Proof. vm_refl. Qed.
Lemma D_270fa4 : decode_any W_270fa4 = Some (Store SZ8 2 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fa8 : bv 32 := 0x00050a63.
Lemma F_270fa8 : fetch_word Plain.M.loaded_segments (0x270fec : word) = Some W_270fa8.
Proof. vm_refl. Qed.
Lemma D_270fa8 : decode_any W_270fa8 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fac : bv 32 := 0x03056513.
Lemma F_270fac : fetch_word Plain.M.loaded_segments (0x270ff0 : word) = Some W_270fac.
Proof. vm_refl. Qed.
Lemma D_270fac : decode_any W_270fac = Some (OpImm ALU_OR 10 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fb0 : bv 32 := 0xfffb8593.
Lemma F_270fb0 : fetch_word Plain.M.loaded_segments (0x270ff4 : word) = Some W_270fb0.
Proof. vm_refl. Qed.
Lemma D_270fb0 : decode_any W_270fb0 = Some (OpImm ALU_ADD 11 23 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fb4 : bv 32 := 0xfeab8fa3.
Lemma F_270fb4 : fetch_word Plain.M.loaded_segments (0x270ff8 : word) = Some W_270fb4.
Proof. vm_refl. Qed.
Lemma D_270fb4 : decode_any W_270fb4 = Some (Store SZ1 23 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fb8 : bv 32 := 0x00058b93.
Lemma F_270fb8 : fetch_word Plain.M.loaded_segments (0x270ffc : word) = Some W_270fb8.
Proof. vm_refl. Qed.
Lemma D_270fb8 : decode_any W_270fb8 = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fbc : bv 32 := 0x000ca513.
Lemma F_270fbc : fetch_word Plain.M.loaded_segments (0x271000 : word) = Some W_270fbc.
Proof. vm_refl. Qed.
Lemma D_270fbc : decode_any W_270fbc = Some (OpImm ALU_SLT 10 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fc0 : bv 32 := 0x00a2f533.
Lemma F_270fc0 : fetch_word Plain.M.loaded_segments (0x271004 : word) = Some W_270fc0.
Proof. vm_refl. Qed.
Lemma D_270fc0 : decode_any W_270fc0 = Some (Op ALU_AND 10 5 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fc4 : bv 32 := 0x36051a63.
Lemma F_270fc4 : fetch_word Plain.M.loaded_segments (0x271008 : word) = Some W_270fc4.
Proof. vm_refl. Qed.
Lemma D_270fc4 : decode_any W_270fc4 = Some (Branch BC_NE 10 0 884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fc8 : bv 32 := 0x00028663.
Lemma F_270fc8 : fetch_word Plain.M.loaded_segments (0x27100c : word) = Some W_270fc8.
Proof. vm_refl. Qed.
Lemma D_270fc8 : decode_any W_270fc8 = Some (Branch BC_EQ 5 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fcc : bv 32 := 0x03013503.
Lemma F_270fcc : fetch_word Plain.M.loaded_segments (0x271010 : word) = Some W_270fcc.
Proof. vm_refl. Qed.
Lemma D_270fcc : decode_any W_270fcc = Some (Load SZ8 true 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fd0 : bv 32 := 0x00ac7c33.
Lemma F_270fd0 : fetch_word Plain.M.loaded_segments (0x271014 : word) = Some W_270fd0.
Proof. vm_refl. Qed.
Lemma D_270fd0 : decode_any W_270fd0 = Some (Op ALU_AND 24 24 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fd4 : bv 32 := 0x07013503.
Lemma F_270fd4 : fetch_word Plain.M.loaded_segments (0x271018 : word) = Some W_270fd4.
Proof. vm_refl. Qed.
Lemma D_270fd4 : decode_any W_270fd4 = Some (Load SZ8 true 10 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fd8 : bv 32 := 0x00051a63.
Lemma F_270fd8 : fetch_word Plain.M.loaded_segments (0x27101c : word) = Some W_270fd8.
Proof. vm_refl. Qed.
Lemma D_270fd8 : decode_any W_270fd8 = Some (Branch BC_NE 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fdc : bv 32 := 0x000c9863.
Lemma F_270fdc : fetch_word Plain.M.loaded_segments (0x271020 : word) = Some W_270fdc.
Proof. vm_refl. Qed.
Lemma D_270fdc : decode_any W_270fdc = Some (Branch BC_NE 25 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fe0 : bv 32 := 0x0b010b93.
Lemma F_270fe0 : fetch_word Plain.M.loaded_segments (0x271024 : word) = Some W_270fe0.
Proof. vm_refl. Qed.
Lemma D_270fe0 : decode_any W_270fe0 = Some (OpImm ALU_ADD 23 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fe4 : bv 32 := 0x000b8593.
Lemma F_270fe4 : fetch_word Plain.M.loaded_segments (0x271028 : word) = Some W_270fe4.
Proof. vm_refl. Qed.
Lemma D_270fe4 : decode_any W_270fe4 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fe8 : bv 32 := 0x0240006f.
Lemma F_270fe8 : fetch_word Plain.M.loaded_segments (0x27102c : word) = Some W_270fe8.
Proof. vm_refl. Qed.
Lemma D_270fe8 : decode_any W_270fe8 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270fec : bv 32 := 0x00153513.
Lemma F_270fec : fetch_word Plain.M.loaded_segments (0x271030 : word) = Some W_270fec.
Proof. vm_refl. Qed.
Lemma D_270fec : decode_any W_270fec = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ff0 : bv 32 := 0x0b010593.
Lemma F_270ff0 : fetch_word Plain.M.loaded_segments (0x271034 : word) = Some W_270ff0.
Proof. vm_refl. Qed.
Lemma D_270ff0 : decode_any W_270ff0 = Some (OpImm ALU_ADD 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ff4 : bv 32 := 0x417585b3.
Lemma F_270ff4 : fetch_word Plain.M.loaded_segments (0x271038 : word) = Some W_270ff4.
Proof. vm_refl. Qed.
Lemma D_270ff4 : decode_any W_270ff4 = Some (Op ALU_SUB 11 11 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ff8 : bv 32 := 0x00a58533.
Lemma F_270ff8 : fetch_word Plain.M.loaded_segments (0x27103c : word) = Some W_270ff8.
Proof. vm_refl. Qed.
Lemma D_270ff8 : decode_any W_270ff8 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_270ffc : bv 32 := 0x00acc463.
Lemma F_270ffc : fetch_word Plain.M.loaded_segments (0x271040 : word) = Some W_270ffc.
Proof. vm_refl. Qed.
Lemma D_270ffc : decode_any W_270ffc = Some (Branch BC_LT 25 10 8, 4%Z).
Proof. vm_refl. Qed.
