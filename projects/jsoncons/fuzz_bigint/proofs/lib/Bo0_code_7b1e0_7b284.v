(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_7b1e0 : bv 32 := 0xfe010113.
Lemma F_7b1e0 : fetch_word AsanUbsan.M.loaded_segments (0x7b1e0 : word) = Some W_7b1e0.
Proof. vm_refl. Qed.
Lemma D_7b1e0 : decode_any W_7b1e0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1e4 : bv 32 := 0x00113c23.
Lemma F_7b1e4 : fetch_word AsanUbsan.M.loaded_segments (0x7b1e4 : word) = Some W_7b1e4.
Proof. vm_refl. Qed.
Lemma D_7b1e4 : decode_any W_7b1e4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1e8 : bv 32 := 0x00813823.
Lemma F_7b1e8 : fetch_word AsanUbsan.M.loaded_segments (0x7b1e8 : word) = Some W_7b1e8.
Proof. vm_refl. Qed.
Lemma D_7b1e8 : decode_any W_7b1e8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1ec : bv 32 := 0x00913423.
Lemma F_7b1ec : fetch_word AsanUbsan.M.loaded_segments (0x7b1ec : word) = Some W_7b1ec.
Proof. vm_refl. Qed.
Lemma D_7b1ec : decode_any W_7b1ec = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1f0 : bv 32 := 0x01213023.
Lemma F_7b1f0 : fetch_word AsanUbsan.M.loaded_segments (0x7b1f0 : word) = Some W_7b1f0.
Proof. vm_refl. Qed.
Lemma D_7b1f0 : decode_any W_7b1f0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1f4 : bv 32 := 0x00058413.
Lemma F_7b1f4 : fetch_word AsanUbsan.M.loaded_segments (0x7b1f4 : word) = Some W_7b1f4.
Proof. vm_refl. Qed.
Lemma D_7b1f4 : decode_any W_7b1f4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1f8 : bv 32 := 0x0005b597.
Lemma F_7b1f8 : fetch_word AsanUbsan.M.loaded_segments (0x7b1f8 : word) = Some W_7b1f8.
Proof. vm_refl. Qed.
Lemma D_7b1f8 : decode_any W_7b1f8 = Some (Auipc 11 91, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1fc : bv 32 := 0x2b05b903.
Lemma F_7b1fc : fetch_word AsanUbsan.M.loaded_segments (0x7b1fc : word) = Some W_7b1fc.
Proof. vm_refl. Qed.
Lemma D_7b1fc : decode_any W_7b1fc = Some (Load SZ8 true 18 11 688, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b200 : bv 32 := 0x00093583.
Lemma F_7b200 : fetch_word AsanUbsan.M.loaded_segments (0x7b200 : word) = Some W_7b200.
Proof. vm_refl. Qed.
Lemma D_7b200 : decode_any W_7b200 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b204 : bv 32 := 0x00050493.
Lemma F_7b204 : fetch_word AsanUbsan.M.loaded_segments (0x7b204 : word) = Some W_7b204.
Proof. vm_refl. Qed.
Lemma D_7b204 : decode_any W_7b204 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b208 : bv 32 := 0x00059863.
Lemma F_7b208 : fetch_word AsanUbsan.M.loaded_segments (0x7b208 : word) = Some W_7b208.
Proof. vm_refl. Qed.
Lemma D_7b208 : decode_any W_7b208 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b20c : bv 32 := 0xb01f70ef.
Lemma F_7b20c : fetch_word AsanUbsan.M.loaded_segments (0x7b20c : word) = Some W_7b20c.
Proof. vm_refl. Qed.
Lemma D_7b20c : decode_any W_7b20c = Some (Jal 1 2063104, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b210 : bv 32 := 0x00050593.
Lemma F_7b210 : fetch_word AsanUbsan.M.loaded_segments (0x7b210 : word) = Some W_7b210.
Proof. vm_refl. Qed.
Lemma D_7b210 : decode_any W_7b210 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b214 : bv 32 := 0x00a93023.
Lemma F_7b214 : fetch_word AsanUbsan.M.loaded_segments (0x7b214 : word) = Some W_7b214.
Proof. vm_refl. Qed.
Lemma D_7b214 : decode_any W_7b214 = Some (Store SZ8 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b218 : bv 32 := 0xfff58513.
Lemma F_7b218 : fetch_word AsanUbsan.M.loaded_segments (0x7b218 : word) = Some W_7b218.
Proof. vm_refl. Qed.
Lemma D_7b218 : decode_any W_7b218 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b21c : bv 32 := 0x00a5f533.
Lemma F_7b21c : fetch_word AsanUbsan.M.loaded_segments (0x7b21c : word) = Some W_7b21c.
Proof. vm_refl. Qed.
Lemma D_7b21c : decode_any W_7b21c = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b220 : bv 32 := 0x04051a63.
Lemma F_7b220 : fetch_word AsanUbsan.M.loaded_segments (0x7b220 : word) = Some W_7b220.
Proof. vm_refl. Qed.
Lemma D_7b220 : decode_any W_7b220 = Some (Branch BC_NE 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b224 : bv 32 := 0x00b484b3.
Lemma F_7b224 : fetch_word AsanUbsan.M.loaded_segments (0x7b224 : word) = Some W_7b224.
Proof. vm_refl. Qed.
Lemma D_7b224 : decode_any W_7b224 = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b228 : bv 32 := 0x40b005b3.
Lemma F_7b228 : fetch_word AsanUbsan.M.loaded_segments (0x7b228 : word) = Some W_7b228.
Proof. vm_refl. Qed.
Lemma D_7b228 : decode_any W_7b228 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b22c : bv 32 := 0xfff48513.
Lemma F_7b22c : fetch_word AsanUbsan.M.loaded_segments (0x7b22c : word) = Some W_7b22c.
Proof. vm_refl. Qed.
Lemma D_7b22c : decode_any W_7b22c = Some (OpImm ALU_ADD 10 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b230 : bv 32 := 0x00b57533.
Lemma F_7b230 : fetch_word AsanUbsan.M.loaded_segments (0x7b230 : word) = Some W_7b230.
Proof. vm_refl. Qed.
Lemma D_7b230 : decode_any W_7b230 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b234 : bv 32 := 0x00b475b3.
Lemma F_7b234 : fetch_word AsanUbsan.M.loaded_segments (0x7b234 : word) = Some W_7b234.
Proof. vm_refl. Qed.
Lemma D_7b234 : decode_any W_7b234 = Some (Op ALU_AND 11 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b238 : bv 32 := 0x02b57263.
Lemma F_7b238 : fetch_word AsanUbsan.M.loaded_segments (0x7b238 : word) = Some W_7b238.
Proof. vm_refl. Qed.
Lemma D_7b238 : decode_any W_7b238 = Some (Branch BC_GEU 10 11 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b23c : bv 32 := 0x40a585b3.
Lemma F_7b23c : fetch_word AsanUbsan.M.loaded_segments (0x7b23c : word) = Some W_7b23c.
Proof. vm_refl. Qed.
Lemma D_7b23c : decode_any W_7b23c = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b240 : bv 32 := 0x00400613.
Lemma F_7b240 : fetch_word AsanUbsan.M.loaded_segments (0x7b240 : word) = Some W_7b240.
Proof. vm_refl. Qed.
Lemma D_7b240 : decode_any W_7b240 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b244 : bv 32 := 0x01813083.
Lemma F_7b244 : fetch_word AsanUbsan.M.loaded_segments (0x7b244 : word) = Some W_7b244.
Proof. vm_refl. Qed.
Lemma D_7b244 : decode_any W_7b244 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b248 : bv 32 := 0x01013403.
Lemma F_7b248 : fetch_word AsanUbsan.M.loaded_segments (0x7b248 : word) = Some W_7b248.
Proof. vm_refl. Qed.
Lemma D_7b248 : decode_any W_7b248 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b24c : bv 32 := 0x00813483.
Lemma F_7b24c : fetch_word AsanUbsan.M.loaded_segments (0x7b24c : word) = Some W_7b24c.
Proof. vm_refl. Qed.
Lemma D_7b24c : decode_any W_7b24c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b250 : bv 32 := 0x00013903.
Lemma F_7b250 : fetch_word AsanUbsan.M.loaded_segments (0x7b250 : word) = Some W_7b250.
Proof. vm_refl. Qed.
Lemma D_7b250 : decode_any W_7b250 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b254 : bv 32 := 0x02010113.
Lemma F_7b254 : fetch_word AsanUbsan.M.loaded_segments (0x7b254 : word) = Some W_7b254.
Proof. vm_refl. Qed.
Lemma D_7b254 : decode_any W_7b254 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b258 : bv 32 := 0xbb1f606f.
Lemma F_7b258 : fetch_word AsanUbsan.M.loaded_segments (0x7b258 : word) = Some W_7b258.
Proof. vm_refl. Qed.
Lemma D_7b258 : decode_any W_7b258 = Some (Jal 0 2059184, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b25c : bv 32 := 0x01813083.
Lemma F_7b25c : fetch_word AsanUbsan.M.loaded_segments (0x7b25c : word) = Some W_7b25c.
Proof. vm_refl. Qed.
Lemma D_7b25c : decode_any W_7b25c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b260 : bv 32 := 0x01013403.
Lemma F_7b260 : fetch_word AsanUbsan.M.loaded_segments (0x7b260 : word) = Some W_7b260.
Proof. vm_refl. Qed.
Lemma D_7b260 : decode_any W_7b260 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b264 : bv 32 := 0x00813483.
Lemma F_7b264 : fetch_word AsanUbsan.M.loaded_segments (0x7b264 : word) = Some W_7b264.
Proof. vm_refl. Qed.
Lemma D_7b264 : decode_any W_7b264 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b268 : bv 32 := 0x00013903.
Lemma F_7b268 : fetch_word AsanUbsan.M.loaded_segments (0x7b268 : word) = Some W_7b268.
Proof. vm_refl. Qed.
Lemma D_7b268 : decode_any W_7b268 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b26c : bv 32 := 0x02010113.
Lemma F_7b26c : fetch_word AsanUbsan.M.loaded_segments (0x7b26c : word) = Some W_7b26c.
Proof. vm_refl. Qed.
Lemma D_7b26c : decode_any W_7b26c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b270 : bv 32 := 0x00008067.
Lemma F_7b270 : fetch_word AsanUbsan.M.loaded_segments (0x7b270 : word) = Some W_7b270.
Proof. vm_refl. Qed.
Lemma D_7b270 : decode_any W_7b270 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b274 : bv 32 := 0xfff97517.
Lemma F_7b274 : fetch_word AsanUbsan.M.loaded_segments (0x7b274 : word) = Some W_7b274.
Proof. vm_refl. Qed.
Lemma D_7b274 : decode_any W_7b274 = Some (Auipc 10 1048471, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b278 : bv 32 := 0x4fe50513.
Lemma F_7b278 : fetch_word AsanUbsan.M.loaded_segments (0x7b278 : word) = Some W_7b278.
Proof. vm_refl. Qed.
Lemma D_7b278 : decode_any W_7b278 = Some (OpImm ALU_ADD 10 10 1278, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b27c : bv 32 := 0xa18f30ef.
Lemma F_7b27c : fetch_word AsanUbsan.M.loaded_segments (0x7b27c : word) = Some W_7b27c.
Proof. vm_refl. Qed.
Lemma D_7b27c : decode_any W_7b27c = Some (Jal 1 2044440, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b280 : bv 32 := 0xf9dfd0ef.
Lemma F_7b280 : fetch_word AsanUbsan.M.loaded_segments (0x7b280 : word) = Some W_7b280.
Proof. vm_refl. Qed.
Lemma D_7b280 : decode_any W_7b280 = Some (Jal 1 2088860, 4%Z).
Proof. vm_refl. Qed.
