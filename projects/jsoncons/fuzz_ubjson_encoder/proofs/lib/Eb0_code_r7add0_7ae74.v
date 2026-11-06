(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_961d8 : bv 32 := 0xfe010113.
Lemma F_961d8 : fetch_word AsanUbsan.M.loaded_segments (0x96228 : word) = Some W_961d8.
Proof. vm_refl. Qed.
Lemma D_961d8 : decode_any W_961d8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_961dc : bv 32 := 0x00113c23.
Lemma F_961dc : fetch_word AsanUbsan.M.loaded_segments (0x9622c : word) = Some W_961dc.
Proof. vm_refl. Qed.
Lemma D_961dc : decode_any W_961dc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_961e0 : bv 32 := 0x00813823.
Lemma F_961e0 : fetch_word AsanUbsan.M.loaded_segments (0x96230 : word) = Some W_961e0.
Proof. vm_refl. Qed.
Lemma D_961e0 : decode_any W_961e0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_961e4 : bv 32 := 0x00913423.
Lemma F_961e4 : fetch_word AsanUbsan.M.loaded_segments (0x96234 : word) = Some W_961e4.
Proof. vm_refl. Qed.
Lemma D_961e4 : decode_any W_961e4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_961e8 : bv 32 := 0x01213023.
Lemma F_961e8 : fetch_word AsanUbsan.M.loaded_segments (0x96238 : word) = Some W_961e8.
Proof. vm_refl. Qed.
Lemma D_961e8 : decode_any W_961e8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_961ec : bv 32 := 0x00058413.
Lemma F_961ec : fetch_word AsanUbsan.M.loaded_segments (0x9623c : word) = Some W_961ec.
Proof. vm_refl. Qed.
Lemma D_961ec : decode_any W_961ec = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_961f0 : bv 32 := 0x000a7597.
Lemma F_961f0 : fetch_word AsanUbsan.M.loaded_segments (0x96240 : word) = Some W_961f0.
Proof. vm_refl. Qed.
Lemma D_961f0 : decode_any W_961f0 = Some (Auipc 11 167, 4%Z).
Proof. vm_refl. Qed.

Definition W_961f4 : bv 32 := 0x6685b903.
Lemma F_961f4 : fetch_word AsanUbsan.M.loaded_segments (0x96244 : word) = Some W_961f4.
Proof. vm_refl. Qed.
Lemma D_961f4 : decode_any W_961f4 = Some (Load SZ8 true 18 11 1640, 4%Z).
Proof. vm_refl. Qed.

Definition W_961f8 : bv 32 := 0x00093583.
Lemma F_961f8 : fetch_word AsanUbsan.M.loaded_segments (0x96248 : word) = Some W_961f8.
Proof. vm_refl. Qed.
Lemma D_961f8 : decode_any W_961f8 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_961fc : bv 32 := 0x00050493.
Lemma F_961fc : fetch_word AsanUbsan.M.loaded_segments (0x9624c : word) = Some W_961fc.
Proof. vm_refl. Qed.
Lemma D_961fc : decode_any W_961fc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96200 : bv 32 := 0x00059863.
Lemma F_96200 : fetch_word AsanUbsan.M.loaded_segments (0x96250 : word) = Some W_96200.
Proof. vm_refl. Qed.
Lemma D_96200 : decode_any W_96200 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_96210 : bv 32 := 0xfff58513.
Lemma F_96210 : fetch_word AsanUbsan.M.loaded_segments (0x96260 : word) = Some W_96210.
Proof. vm_refl. Qed.
Lemma D_96210 : decode_any W_96210 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_96214 : bv 32 := 0x00a5f533.
Lemma F_96214 : fetch_word AsanUbsan.M.loaded_segments (0x96264 : word) = Some W_96214.
Proof. vm_refl. Qed.
Lemma D_96214 : decode_any W_96214 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_96218 : bv 32 := 0x04051a63.
Lemma F_96218 : fetch_word AsanUbsan.M.loaded_segments (0x96268 : word) = Some W_96218.
Proof. vm_refl. Qed.
Lemma D_96218 : decode_any W_96218 = Some (Branch BC_NE 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_9621c : bv 32 := 0x00b484b3.
Lemma F_9621c : fetch_word AsanUbsan.M.loaded_segments (0x9626c : word) = Some W_9621c.
Proof. vm_refl. Qed.
Lemma D_9621c : decode_any W_9621c = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_96220 : bv 32 := 0x40b005b3.
Lemma F_96220 : fetch_word AsanUbsan.M.loaded_segments (0x96270 : word) = Some W_96220.
Proof. vm_refl. Qed.
Lemma D_96220 : decode_any W_96220 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_96224 : bv 32 := 0xfff48513.
Lemma F_96224 : fetch_word AsanUbsan.M.loaded_segments (0x96274 : word) = Some W_96224.
Proof. vm_refl. Qed.
Lemma D_96224 : decode_any W_96224 = Some (OpImm ALU_ADD 10 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_96228 : bv 32 := 0x00b57533.
Lemma F_96228 : fetch_word AsanUbsan.M.loaded_segments (0x96278 : word) = Some W_96228.
Proof. vm_refl. Qed.
Lemma D_96228 : decode_any W_96228 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9622c : bv 32 := 0x00b475b3.
Lemma F_9622c : fetch_word AsanUbsan.M.loaded_segments (0x9627c : word) = Some W_9622c.
Proof. vm_refl. Qed.
Lemma D_9622c : decode_any W_9622c = Some (Op ALU_AND 11 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_96230 : bv 32 := 0x02b57263.
Lemma F_96230 : fetch_word AsanUbsan.M.loaded_segments (0x96280 : word) = Some W_96230.
Proof. vm_refl. Qed.
Lemma D_96230 : decode_any W_96230 = Some (Branch BC_GEU 10 11 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_96234 : bv 32 := 0x40a585b3.
Lemma F_96234 : fetch_word AsanUbsan.M.loaded_segments (0x96284 : word) = Some W_96234.
Proof. vm_refl. Qed.
Lemma D_96234 : decode_any W_96234 = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_96238 : bv 32 := 0x00400613.
Lemma F_96238 : fetch_word AsanUbsan.M.loaded_segments (0x96288 : word) = Some W_96238.
Proof. vm_refl. Qed.
Lemma D_96238 : decode_any W_96238 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9623c : bv 32 := 0x01813083.
Lemma F_9623c : fetch_word AsanUbsan.M.loaded_segments (0x9628c : word) = Some W_9623c.
Proof. vm_refl. Qed.
Lemma D_9623c : decode_any W_9623c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_96240 : bv 32 := 0x01013403.
Lemma F_96240 : fetch_word AsanUbsan.M.loaded_segments (0x96290 : word) = Some W_96240.
Proof. vm_refl. Qed.
Lemma D_96240 : decode_any W_96240 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_96244 : bv 32 := 0x00813483.
Lemma F_96244 : fetch_word AsanUbsan.M.loaded_segments (0x96294 : word) = Some W_96244.
Proof. vm_refl. Qed.
Lemma D_96244 : decode_any W_96244 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_96248 : bv 32 := 0x00013903.
Lemma F_96248 : fetch_word AsanUbsan.M.loaded_segments (0x96298 : word) = Some W_96248.
Proof. vm_refl. Qed.
Lemma D_96248 : decode_any W_96248 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9624c : bv 32 := 0x02010113.
Lemma F_9624c : fetch_word AsanUbsan.M.loaded_segments (0x9629c : word) = Some W_9624c.
Proof. vm_refl. Qed.
Lemma D_9624c : decode_any W_9624c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_96250 : bv 32 := 0xbb1f606f.
Lemma F_96250 : fetch_word AsanUbsan.M.loaded_segments (0x962a0 : word) = Some W_96250.
Proof. vm_refl. Qed.
Lemma D_96250 : decode_any W_96250 = Some (Jal 0 2059184, 4%Z).
Proof. vm_refl. Qed.

Definition W_96254 : bv 32 := 0x01813083.
Lemma F_96254 : fetch_word AsanUbsan.M.loaded_segments (0x962a4 : word) = Some W_96254.
Proof. vm_refl. Qed.
Lemma D_96254 : decode_any W_96254 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_96258 : bv 32 := 0x01013403.
Lemma F_96258 : fetch_word AsanUbsan.M.loaded_segments (0x962a8 : word) = Some W_96258.
Proof. vm_refl. Qed.
Lemma D_96258 : decode_any W_96258 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9625c : bv 32 := 0x00813483.
Lemma F_9625c : fetch_word AsanUbsan.M.loaded_segments (0x962ac : word) = Some W_9625c.
Proof. vm_refl. Qed.
Lemma D_9625c : decode_any W_9625c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_96260 : bv 32 := 0x00013903.
Lemma F_96260 : fetch_word AsanUbsan.M.loaded_segments (0x962b0 : word) = Some W_96260.
Proof. vm_refl. Qed.
Lemma D_96260 : decode_any W_96260 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96264 : bv 32 := 0x02010113.
Lemma F_96264 : fetch_word AsanUbsan.M.loaded_segments (0x962b4 : word) = Some W_96264.
Proof. vm_refl. Qed.
Lemma D_96264 : decode_any W_96264 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_96268 : bv 32 := 0x00008067.
Lemma F_96268 : fetch_word AsanUbsan.M.loaded_segments (0x962b8 : word) = Some W_96268.
Proof. vm_refl. Qed.
Lemma D_96268 : decode_any W_96268 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
