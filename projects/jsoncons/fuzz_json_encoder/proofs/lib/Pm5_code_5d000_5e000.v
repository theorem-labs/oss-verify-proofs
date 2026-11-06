(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5d000 : bv 32 := 0x00f287b3.
Lemma F_5d000 : fetch_word AsanUbsan.M.loaded_segments (0x5d048 : word) = Some W_5d000.
Proof. vm_refl. Qed.
Lemma D_5d000 : decode_any W_5d000 = Some (Op ALU_ADD 15 5 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d004 : bv 32 := 0x00f13c23.
Lemma F_5d004 : fetch_word AsanUbsan.M.loaded_segments (0x5d04c : word) = Some W_5d004.
Proof. vm_refl. Qed.
Lemma D_5d004 : decode_any W_5d004 = Some (Store SZ8 2 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d008 : bv 32 := 0x0b853383.
Lemma F_5d008 : fetch_word AsanUbsan.M.loaded_segments (0x5d050 : word) = Some W_5d008.
Proof. vm_refl. Qed.
Lemma D_5d008 : decode_any W_5d008 = Some (Load SZ8 true 7 10 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d00c : bv 32 := 0x00170713.
Lemma F_5d00c : fetch_word AsanUbsan.M.loaded_segments (0x5d054 : word) = Some W_5d00c.
Proof. vm_refl. Qed.
Lemma D_5d00c : decode_any W_5d00c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d010 : bv 32 := 0x00088293.
Lemma F_5d010 : fetch_word AsanUbsan.M.loaded_segments (0x5d058 : word) = Some W_5d010.
Proof. vm_refl. Qed.
Lemma D_5d010 : decode_any W_5d010 = Some (OpImm ALU_ADD 5 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d014 : bv 32 := 0x00030793.
Lemma F_5d014 : fetch_word AsanUbsan.M.loaded_segments (0x5d05c : word) = Some W_5d014.
Proof. vm_refl. Qed.
Lemma D_5d014 : decode_any W_5d014 = Some (OpImm ALU_ADD 15 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d018 : bv 32 := 0x0475fc63.
Lemma F_5d018 : fetch_word AsanUbsan.M.loaded_segments (0x5d060 : word) = Some W_5d018.
Proof. vm_refl. Qed.
Lemma D_5d018 : decode_any W_5d018 = Some (Branch BC_GEU 11 7 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d01c : bv 32 := 0x02080e63.
Lemma F_5d01c : fetch_word AsanUbsan.M.loaded_segments (0x5d064 : word) = Some W_5d01c.
Proof. vm_refl. Qed.
Lemma D_5d01c : decode_any W_5d01c = Some (Branch BC_EQ 16 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d020 : bv 32 := 0x0002b883.
Lemma F_5d020 : fetch_word AsanUbsan.M.loaded_segments (0x5d068 : word) = Some W_5d020.
Proof. vm_refl. Qed.
Lemma D_5d020 : decode_any W_5d020 = Some (Load SZ8 true 17 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d024 : bv 32 := 0x0b153423.
Lemma F_5d024 : fetch_word AsanUbsan.M.loaded_segments (0x5d06c : word) = Some W_5d024.
Proof. vm_refl. Qed.
Lemma D_5d024 : decode_any W_5d024 = Some (Store SZ8 10 17 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d028 : bv 32 := 0x00089463.
Lemma F_5d028 : fetch_word AsanUbsan.M.loaded_segments (0x5d070 : word) = Some W_5d028.
Proof. vm_refl. Qed.
Lemma D_5d028 : decode_any W_5d028 = Some (Branch BC_NE 17 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d02c : bv 32 := 0x0a053823.
Lemma F_5d02c : fetch_word AsanUbsan.M.loaded_segments (0x5d074 : word) = Some W_5d02c.
Proof. vm_refl. Qed.
Lemma D_5d02c : decode_any W_5d02c = Some (Store SZ8 10 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d030 : bv 32 := 0xfff80813.
Lemma F_5d030 : fetch_word AsanUbsan.M.loaded_segments (0x5d078 : word) = Some W_5d030.
Proof. vm_refl. Qed.
Lemma D_5d030 : decode_any W_5d030 = Some (OpImm ALU_ADD 16 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d034 : bv 32 := 0x0b053023.
Lemma F_5d034 : fetch_word AsanUbsan.M.loaded_segments (0x5d07c : word) = Some W_5d034.
Proof. vm_refl. Qed.
Lemma D_5d034 : decode_any W_5d034 = Some (Store SZ8 10 16 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d038 : bv 32 := 0x0082b303.
Lemma F_5d038 : fetch_word AsanUbsan.M.loaded_segments (0x5d080 : word) = Some W_5d038.
Proof. vm_refl. Qed.
Lemma D_5d038 : decode_any W_5d038 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d03c : bv 32 := 0x0b853383.
Lemma F_5d03c : fetch_word AsanUbsan.M.loaded_segments (0x5d084 : word) = Some W_5d03c.
Proof. vm_refl. Qed.
Lemma D_5d03c : decode_any W_5d03c = Some (Load SZ8 true 7 10 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d040 : bv 32 := 0x40638333.
Lemma F_5d040 : fetch_word AsanUbsan.M.loaded_segments (0x5d088 : word) = Some W_5d040.
Proof. vm_refl. Qed.
Lemma D_5d040 : decode_any W_5d040 = Some (Op ALU_SUB 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d044 : bv 32 := 0x0a653c23.
Lemma F_5d044 : fetch_word AsanUbsan.M.loaded_segments (0x5d08c : word) = Some W_5d044.
Proof. vm_refl. Qed.
Lemma D_5d044 : decode_any W_5d044 = Some (Store SZ8 10 6 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d048 : bv 32 := 0x00028313.
Lemma F_5d048 : fetch_word AsanUbsan.M.loaded_segments (0x5d090 : word) = Some W_5d048.
Proof. vm_refl. Qed.
Lemma D_5d048 : decode_any W_5d048 = Some (OpImm ALU_ADD 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d04c : bv 32 := 0x0002b023.
Lemma F_5d04c : fetch_word AsanUbsan.M.loaded_segments (0x5d094 : word) = Some W_5d04c.
Proof. vm_refl. Qed.
Lemma D_5d04c : decode_any W_5d04c = Some (Store SZ8 5 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d050 : bv 32 := 0xfa0712e3.
Lemma F_5d050 : fetch_word AsanUbsan.M.loaded_segments (0x5d098 : word) = Some W_5d050.
Proof. vm_refl. Qed.
Lemma D_5d050 : decode_any W_5d050 = Some (Branch BC_NE 14 0 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d054 : bv 32 := 0x0140006f.
Lemma F_5d054 : fetch_word AsanUbsan.M.loaded_segments (0x5d09c : word) = Some W_5d054.
Proof. vm_refl. Qed.
Lemma D_5d054 : decode_any W_5d054 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d068 : bv 32 := 0x00613423.
Lemma F_5d068 : fetch_word AsanUbsan.M.loaded_segments (0x5d0b0 : word) = Some W_5d068.
Proof. vm_refl. Qed.
Lemma D_5d068 : decode_any W_5d068 = Some (Store SZ8 2 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d06c : bv 32 := 0xf8dff06f.
Lemma F_5d06c : fetch_word AsanUbsan.M.loaded_segments (0x5d0b4 : word) = Some W_5d06c.
Proof. vm_refl. Qed.
Lemma D_5d06c : decode_any W_5d06c = Some (Jal 0 2097036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d070 : bv 32 := 0x00e13023.
Lemma F_5d070 : fetch_word AsanUbsan.M.loaded_segments (0x5d0b8 : word) = Some W_5d070.
Proof. vm_refl. Qed.
Lemma D_5d070 : decode_any W_5d070 = Some (Store SZ8 2 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d074 : bv 32 := 0x00613823.
Lemma F_5d074 : fetch_word AsanUbsan.M.loaded_segments (0x5d0bc : word) = Some W_5d074.
Proof. vm_refl. Qed.
Lemma D_5d074 : decode_any W_5d074 = Some (Store SZ8 2 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d078 : bv 32 := 0x0310000f.
Lemma F_5d078 : fetch_word AsanUbsan.M.loaded_segments (0x5d0c0 : word) = Some W_5d078.
Proof. vm_refl. Qed.
Lemma D_5d078 : decode_any W_5d078 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d07c : bv 32 := 0x08050c23.
Lemma F_5d07c : fetch_word AsanUbsan.M.loaded_segments (0x5d0c4 : word) = Some W_5d07c.
Proof. vm_refl. Qed.
Lemma D_5d07c : decode_any W_5d07c = Some (Store SZ1 10 0 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d080 : bv 32 := 0x0310000f.
Lemma F_5d080 : fetch_word AsanUbsan.M.loaded_segments (0x5d0c8 : word) = Some W_5d080.
Proof. vm_refl. Qed.
Lemma D_5d080 : decode_any W_5d080 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d084 : bv 32 := 0x08050ca3.
Lemma F_5d084 : fetch_word AsanUbsan.M.loaded_segments (0x5d0cc : word) = Some W_5d084.
Proof. vm_refl. Qed.
Lemma D_5d084 : decode_any W_5d084 = Some (Store SZ1 10 0 153, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d088 : bv 32 := 0x00010593.
Lemma F_5d088 : fetch_word AsanUbsan.M.loaded_segments (0x5d0d0 : word) = Some W_5d088.
Proof. vm_refl. Qed.
Lemma D_5d088 : decode_any W_5d088 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d08c : bv 32 := 0x1fc000ef.
Lemma F_5d08c : fetch_word AsanUbsan.M.loaded_segments (0x5d0d4 : word) = Some W_5d08c.
Proof. vm_refl. Qed.
Lemma D_5d08c : decode_any W_5d08c = Some (Jal 1 508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d090 : bv 32 := 0x04813083.
Lemma F_5d090 : fetch_word AsanUbsan.M.loaded_segments (0x5d0d8 : word) = Some W_5d090.
Proof. vm_refl. Qed.
Lemma D_5d090 : decode_any W_5d090 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d094 : bv 32 := 0x04013403.
Lemma F_5d094 : fetch_word AsanUbsan.M.loaded_segments (0x5d0dc : word) = Some W_5d094.
Proof. vm_refl. Qed.
Lemma D_5d094 : decode_any W_5d094 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d098 : bv 32 := 0x03813483.
Lemma F_5d098 : fetch_word AsanUbsan.M.loaded_segments (0x5d0e0 : word) = Some W_5d098.
Proof. vm_refl. Qed.
Lemma D_5d098 : decode_any W_5d098 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d09c : bv 32 := 0x03013903.
Lemma F_5d09c : fetch_word AsanUbsan.M.loaded_segments (0x5d0e4 : word) = Some W_5d09c.
Proof. vm_refl. Qed.
Lemma D_5d09c : decode_any W_5d09c = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0a0 : bv 32 := 0x02813983.
Lemma F_5d0a0 : fetch_word AsanUbsan.M.loaded_segments (0x5d0e8 : word) = Some W_5d0a0.
Proof. vm_refl. Qed.
Lemma D_5d0a0 : decode_any W_5d0a0 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0a4 : bv 32 := 0x02013a03.
Lemma F_5d0a4 : fetch_word AsanUbsan.M.loaded_segments (0x5d0ec : word) = Some W_5d0a4.
Proof. vm_refl. Qed.
Lemma D_5d0a4 : decode_any W_5d0a4 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0a8 : bv 32 := 0x05010113.
Lemma F_5d0a8 : fetch_word AsanUbsan.M.loaded_segments (0x5d0f0 : word) = Some W_5d0a8.
Proof. vm_refl. Qed.
Lemma D_5d0a8 : decode_any W_5d0a8 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0ac : bv 32 := 0x00008067.
Lemma F_5d0ac : fetch_word AsanUbsan.M.loaded_segments (0x5d0f4 : word) = Some W_5d0ac.
Proof. vm_refl. Qed.
Lemma D_5d0ac : decode_any W_5d0ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d288 : bv 32 := 0xf9010113.
Lemma F_5d288 : fetch_word AsanUbsan.M.loaded_segments (0x5d2d0 : word) = Some W_5d288.
Proof. vm_refl. Qed.
Lemma D_5d288 : decode_any W_5d288 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d28c : bv 32 := 0x06113423.
Lemma F_5d28c : fetch_word AsanUbsan.M.loaded_segments (0x5d2d4 : word) = Some W_5d28c.
Proof. vm_refl. Qed.
Lemma D_5d28c : decode_any W_5d28c = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d290 : bv 32 := 0x06813023.
Lemma F_5d290 : fetch_word AsanUbsan.M.loaded_segments (0x5d2d8 : word) = Some W_5d290.
Proof. vm_refl. Qed.
Lemma D_5d290 : decode_any W_5d290 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d294 : bv 32 := 0x04913c23.
Lemma F_5d294 : fetch_word AsanUbsan.M.loaded_segments (0x5d2dc : word) = Some W_5d294.
Proof. vm_refl. Qed.
Lemma D_5d294 : decode_any W_5d294 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d298 : bv 32 := 0x05213823.
Lemma F_5d298 : fetch_word AsanUbsan.M.loaded_segments (0x5d2e0 : word) = Some W_5d298.
Proof. vm_refl. Qed.
Lemma D_5d298 : decode_any W_5d298 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d29c : bv 32 := 0x05313423.
Lemma F_5d29c : fetch_word AsanUbsan.M.loaded_segments (0x5d2e4 : word) = Some W_5d29c.
Proof. vm_refl. Qed.
Lemma D_5d29c : decode_any W_5d29c = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2a0 : bv 32 := 0x05413023.
Lemma F_5d2a0 : fetch_word AsanUbsan.M.loaded_segments (0x5d2e8 : word) = Some W_5d2a0.
Proof. vm_refl. Qed.
Lemma D_5d2a0 : decode_any W_5d2a0 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2a4 : bv 32 := 0x03513c23.
Lemma F_5d2a4 : fetch_word AsanUbsan.M.loaded_segments (0x5d2ec : word) = Some W_5d2a4.
Proof. vm_refl. Qed.
Lemma D_5d2a4 : decode_any W_5d2a4 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2a8 : bv 32 := 0x03613823.
Lemma F_5d2a8 : fetch_word AsanUbsan.M.loaded_segments (0x5d2f0 : word) = Some W_5d2a8.
Proof. vm_refl. Qed.
Lemma D_5d2a8 : decode_any W_5d2a8 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2ac : bv 32 := 0x03713423.
Lemma F_5d2ac : fetch_word AsanUbsan.M.loaded_segments (0x5d2f4 : word) = Some W_5d2ac.
Proof. vm_refl. Qed.
Lemma D_5d2ac : decode_any W_5d2ac = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2b0 : bv 32 := 0x03813023.
Lemma F_5d2b0 : fetch_word AsanUbsan.M.loaded_segments (0x5d2f8 : word) = Some W_5d2b0.
Proof. vm_refl. Qed.
Lemma D_5d2b0 : decode_any W_5d2b0 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2b4 : bv 32 := 0x01913c23.
Lemma F_5d2b4 : fetch_word AsanUbsan.M.loaded_segments (0x5d2fc : word) = Some W_5d2b4.
Proof. vm_refl. Qed.
Lemma D_5d2b4 : decode_any W_5d2b4 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2b8 : bv 32 := 0x0005b503.
Lemma F_5d2b8 : fetch_word AsanUbsan.M.loaded_segments (0x5d300 : word) = Some W_5d2b8.
Proof. vm_refl. Qed.
Lemma D_5d2b8 : decode_any W_5d2b8 = Some (Load SZ8 true 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2bc : bv 32 := 0x00c13423.
Lemma F_5d2bc : fetch_word AsanUbsan.M.loaded_segments (0x5d304 : word) = Some W_5d2bc.
Proof. vm_refl. Qed.
Lemma D_5d2bc : decode_any W_5d2bc = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2c0 : bv 32 := 0x00d13823.
Lemma F_5d2c0 : fetch_word AsanUbsan.M.loaded_segments (0x5d308 : word) = Some W_5d2c0.
Proof. vm_refl. Qed.
Lemma D_5d2c0 : decode_any W_5d2c0 = Some (Store SZ8 2 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2c4 : bv 32 := 0x0c050463.
Lemma F_5d2c4 : fetch_word AsanUbsan.M.loaded_segments (0x5d30c : word) = Some W_5d2c4.
Proof. vm_refl. Qed.
Lemma D_5d2c4 : decode_any W_5d2c4 = Some (Branch BC_EQ 10 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2c8 : bv 32 := 0x00058413.
Lemma F_5d2c8 : fetch_word AsanUbsan.M.loaded_segments (0x5d310 : word) = Some W_5d2c8.
Proof. vm_refl. Qed.
Lemma D_5d2c8 : decode_any W_5d2c8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2cc : bv 32 := 0x0010d597.
Lemma F_5d2cc : fetch_word AsanUbsan.M.loaded_segments (0x5d314 : word) = Some W_5d2cc.
Proof. vm_refl. Qed.
Lemma D_5d2cc : decode_any W_5d2cc = Some (Auipc 11 269, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2d0 : bv 32 := 0x00100a93.
Lemma F_5d2d0 : fetch_word AsanUbsan.M.loaded_segments (0x5d318 : word) = Some W_5d2d0.
Proof. vm_refl. Qed.
Lemma D_5d2d0 : decode_any W_5d2d0 = Some (OpImm ALU_ADD 21 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2d4 : bv 32 := 0xe4458493.
Lemma F_5d2d4 : fetch_word AsanUbsan.M.loaded_segments (0x5d31c : word) = Some W_5d2d4.
Proof. vm_refl. Qed.
Lemma D_5d2d4 : decode_any W_5d2d4 = Some (OpImm ALU_ADD 9 11 3652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2d8 : bv 32 := 0x025a9a93.
Lemma F_5d2d8 : fetch_word AsanUbsan.M.loaded_segments (0x5d320 : word) = Some W_5d2d8.
Proof. vm_refl. Qed.
Lemma D_5d2d8 : decode_any W_5d2d8 = Some (ShiftImm ALU_SLL 21 21 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2dc : bv 32 := 0x04048913.
Lemma F_5d2dc : fetch_word AsanUbsan.M.loaded_segments (0x5d324 : word) = Some W_5d2dc.
Proof. vm_refl. Qed.
Lemma D_5d2dc : decode_any W_5d2dc = Some (OpImm ALU_ADD 18 9 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2e0 : bv 32 := 0x2b048993.
Lemma F_5d2e0 : fetch_word AsanUbsan.M.loaded_segments (0x5d328 : word) = Some W_5d2e0.
Proof. vm_refl. Qed.
Lemma D_5d2e0 : decode_any W_5d2e0 = Some (OpImm ALU_ADD 19 9 688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2e4 : bv 32 := 0x01c0006f.
Lemma F_5d2e4 : fetch_word AsanUbsan.M.loaded_segments (0x5d32c : word) = Some W_5d2e4.
Proof. vm_refl. Qed.
Lemma D_5d2e4 : decode_any W_5d2e4 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d300 : bv 32 := 0x00843a03.
Lemma F_5d300 : fetch_word AsanUbsan.M.loaded_segments (0x5d348 : word) = Some W_5d300.
Proof. vm_refl. Qed.
Lemma D_5d300 : decode_any W_5d300 = Some (Load SZ8 true 20 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d304 : bv 32 := 0x000a3583.
Lemma F_5d304 : fetch_word AsanUbsan.M.loaded_segments (0x5d34c : word) = Some W_5d304.
Proof. vm_refl. Qed.
Lemma D_5d304 : decode_any W_5d304 = Some (Load SZ8 true 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d308 : bv 32 := 0x00b43423.
Lemma F_5d308 : fetch_word AsanUbsan.M.loaded_segments (0x5d350 : word) = Some W_5d308.
Proof. vm_refl. Qed.
Lemma D_5d308 : decode_any W_5d308 = Some (Store SZ8 8 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d30c : bv 32 := 0x00059463.
Lemma F_5d30c : fetch_word AsanUbsan.M.loaded_segments (0x5d354 : word) = Some W_5d30c.
Proof. vm_refl. Qed.
Lemma D_5d30c : decode_any W_5d30c = Some (Branch BC_NE 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d310 : bv 32 := 0x00043823.
Lemma F_5d310 : fetch_word AsanUbsan.M.loaded_segments (0x5d358 : word) = Some W_5d310.
Proof. vm_refl. Qed.
Lemma D_5d310 : decode_any W_5d310 = Some (Store SZ8 8 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d314 : bv 32 := 0xfff50513.
Lemma F_5d314 : fetch_word AsanUbsan.M.loaded_segments (0x5d35c : word) = Some W_5d314.
Proof. vm_refl. Qed.
Lemma D_5d314 : decode_any W_5d314 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d318 : bv 32 := 0x00a43023.
Lemma F_5d318 : fetch_word AsanUbsan.M.loaded_segments (0x5d360 : word) = Some W_5d318.
Proof. vm_refl. Qed.
Lemma D_5d318 : decode_any W_5d318 = Some (Store SZ8 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d31c : bv 32 := 0x008a3503.
Lemma F_5d31c : fetch_word AsanUbsan.M.loaded_segments (0x5d364 : word) = Some W_5d31c.
Proof. vm_refl. Qed.
Lemma D_5d31c : decode_any W_5d31c = Some (Load SZ8 true 10 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d320 : bv 32 := 0x01843583.
Lemma F_5d320 : fetch_word AsanUbsan.M.loaded_segments (0x5d368 : word) = Some W_5d320.
Proof. vm_refl. Qed.
Lemma D_5d320 : decode_any W_5d320 = Some (Load SZ8 true 11 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d324 : bv 32 := 0x40a585b3.
Lemma F_5d324 : fetch_word AsanUbsan.M.loaded_segments (0x5d36c : word) = Some W_5d324.
Proof. vm_refl. Qed.
Lemma D_5d324 : decode_any W_5d324 = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d328 : bv 32 := 0x00b43c23.
Lemma F_5d328 : fetch_word AsanUbsan.M.loaded_segments (0x5d370 : word) = Some W_5d328.
Proof. vm_refl. Qed.
Lemma D_5d328 : decode_any W_5d328 = Some (Store SZ8 8 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d32c : bv 32 := 0x010a3b03.
Lemma F_5d32c : fetch_word AsanUbsan.M.loaded_segments (0x5d374 : word) = Some W_5d32c.
Proof. vm_refl. Qed.
Lemma D_5d32c : decode_any W_5d32c = Some (Load SZ8 true 22 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d330 : bv 32 := 0x020b0463.
Lemma F_5d330 : fetch_word AsanUbsan.M.loaded_segments (0x5d378 : word) = Some W_5d330.
Proof. vm_refl. Qed.
Lemma D_5d330 : decode_any W_5d330 = Some (Branch BC_EQ 22 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d334 : bv 32 := 0x098a0b93.
Lemma F_5d334 : fetch_word AsanUbsan.M.loaded_segments (0x5d37c : word) = Some W_5d334.
Proof. vm_refl. Qed.
Lemma D_5d334 : decode_any W_5d334 = Some (OpImm ALU_ADD 23 20 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d338 : bv 32 := 0x010b0c13.
Lemma F_5d338 : fetch_word AsanUbsan.M.loaded_segments (0x5d380 : word) = Some W_5d338.
Proof. vm_refl. Qed.
Lemma D_5d338 : decode_any W_5d338 = Some (OpImm ALU_ADD 24 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d33c : bv 32 := 0x01000c93.
Lemma F_5d33c : fetch_word AsanUbsan.M.loaded_segments (0x5d384 : word) = Some W_5d33c.
Proof. vm_refl. Qed.
Lemma D_5d33c : decode_any W_5d33c = Some (OpImm ALU_ADD 25 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d340 : bv 32 := 0xf80bb583.
Lemma F_5d340 : fetch_word AsanUbsan.M.loaded_segments (0x5d388 : word) = Some W_5d340.
Proof. vm_refl. Qed.
Lemma D_5d340 : decode_any W_5d340 = Some (Load SZ8 true 11 23 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d344 : bv 32 := 0x00810513.
Lemma F_5d344 : fetch_word AsanUbsan.M.loaded_segments (0x5d38c : word) = Some W_5d344.
Proof. vm_refl. Qed.
Lemma D_5d344 : decode_any W_5d344 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d348 : bv 32 := 0x078000ef.
Lemma F_5d348 : fetch_word AsanUbsan.M.loaded_segments (0x5d390 : word) = Some W_5d348.
Proof. vm_refl. Qed.
Lemma D_5d348 : decode_any W_5d348 = Some (Jal 1 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d34c : bv 32 := 0x001c8c93.
Lemma F_5d34c : fetch_word AsanUbsan.M.loaded_segments (0x5d394 : word) = Some W_5d34c.
Proof. vm_refl. Qed.
Lemma D_5d34c : decode_any W_5d34c = Some (OpImm ALU_ADD 25 25 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d350 : bv 32 := 0x008b8b93.
Lemma F_5d350 : fetch_word AsanUbsan.M.loaded_segments (0x5d398 : word) = Some W_5d350.
Proof. vm_refl. Qed.
Lemma D_5d350 : decode_any W_5d350 = Some (OpImm ALU_ADD 23 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d354 : bv 32 := 0xff8c96e3.
Lemma F_5d354 : fetch_word AsanUbsan.M.loaded_segments (0x5d39c : word) = Some W_5d354.
Proof. vm_refl. Qed.
Lemma D_5d354 : decode_any W_5d354 = Some (Branch BC_NE 25 24 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d358 : bv 32 := 0x0204b583.
Lemma F_5d358 : fetch_word AsanUbsan.M.loaded_segments (0x5d3a0 : word) = Some W_5d358.
Proof. vm_refl. Qed.
Lemma D_5d358 : decode_any W_5d358 = Some (Load SZ8 true 11 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d35c : bv 32 := 0xf8ba66e3.
Lemma F_5d35c : fetch_word AsanUbsan.M.loaded_segments (0x5d3a4 : word) = Some W_5d35c.
Proof. vm_refl. Qed.
Lemma D_5d35c : decode_any W_5d35c = Some (Branch BC_LTU 20 11 8076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d360 : bv 32 := 0x01558533.
Lemma F_5d360 : fetch_word AsanUbsan.M.loaded_segments (0x5d3a8 : word) = Some W_5d360.
Proof. vm_refl. Qed.
Lemma D_5d360 : decode_any W_5d360 = Some (Op ALU_ADD 10 11 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d364 : bv 32 := 0xf8aa72e3.
Lemma F_5d364 : fetch_word AsanUbsan.M.loaded_segments (0x5d3ac : word) = Some W_5d364.
Proof. vm_refl. Qed.
Lemma D_5d364 : decode_any W_5d364 = Some (Branch BC_GEU 20 10 8068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d368 : bv 32 := 0x00813503.
Lemma F_5d368 : fetch_word AsanUbsan.M.loaded_segments (0x5d3b0 : word) = Some W_5d368.
Proof. vm_refl. Qed.
Lemma D_5d368 : decode_any W_5d368 = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d36c : bv 32 := 0x40ba05b3.
Lemma F_5d36c : fetch_word AsanUbsan.M.loaded_segments (0x5d3b4 : word) = Some W_5d36c.
Proof. vm_refl. Qed.
Lemma D_5d36c : decode_any W_5d36c = Some (Op ALU_SUB 11 20 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d370 : bv 32 := 0x01b59593.
Lemma F_5d370 : fetch_word AsanUbsan.M.loaded_segments (0x5d3b8 : word) = Some W_5d370.
Proof. vm_refl. Qed.
Lemma D_5d370 : decode_any W_5d370 = Some (ShiftImm ALU_SLL 11 11 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d374 : bv 32 := 0x03b5d613.
Lemma F_5d374 : fetch_word AsanUbsan.M.loaded_segments (0x5d3bc : word) = Some W_5d374.
Proof. vm_refl. Qed.
Lemma D_5d374 : decode_any W_5d374 = Some (ShiftImm ALU_SRL 12 11 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d378 : bv 32 := 0x00048593.
Lemma F_5d378 : fetch_word AsanUbsan.M.loaded_segments (0x5d3c0 : word) = Some W_5d378.
Proof. vm_refl. Qed.
Lemma D_5d378 : decode_any W_5d378 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d37c : bv 32 := 0x000a0693.
Lemma F_5d37c : fetch_word AsanUbsan.M.loaded_segments (0x5d3c4 : word) = Some W_5d37c.
Proof. vm_refl. Qed.
Lemma D_5d37c : decode_any W_5d37c = Some (OpImm ALU_ADD 13 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d380 : bv 32 := 0x444000ef.
Lemma F_5d380 : fetch_word AsanUbsan.M.loaded_segments (0x5d3c8 : word) = Some W_5d380.
Proof. vm_refl. Qed.
Lemma D_5d380 : decode_any W_5d380 = Some (Jal 1 1092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d384 : bv 32 := 0x00043503.
Lemma F_5d384 : fetch_word AsanUbsan.M.loaded_segments (0x5d3cc : word) = Some W_5d384.
Proof. vm_refl. Qed.
Lemma D_5d384 : decode_any W_5d384 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d388 : bv 32 := 0xf6051ce3.
Lemma F_5d388 : fetch_word AsanUbsan.M.loaded_segments (0x5d3d0 : word) = Some W_5d388.
Proof. vm_refl. Qed.
Lemma D_5d388 : decode_any W_5d388 = Some (Branch BC_NE 10 0 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d38c : bv 32 := 0x06813083.
Lemma F_5d38c : fetch_word AsanUbsan.M.loaded_segments (0x5d3d4 : word) = Some W_5d38c.
Proof. vm_refl. Qed.
Lemma D_5d38c : decode_any W_5d38c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d390 : bv 32 := 0x06013403.
Lemma F_5d390 : fetch_word AsanUbsan.M.loaded_segments (0x5d3d8 : word) = Some W_5d390.
Proof. vm_refl. Qed.
Lemma D_5d390 : decode_any W_5d390 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d394 : bv 32 := 0x05813483.
Lemma F_5d394 : fetch_word AsanUbsan.M.loaded_segments (0x5d3dc : word) = Some W_5d394.
Proof. vm_refl. Qed.
Lemma D_5d394 : decode_any W_5d394 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d398 : bv 32 := 0x05013903.
Lemma F_5d398 : fetch_word AsanUbsan.M.loaded_segments (0x5d3e0 : word) = Some W_5d398.
Proof. vm_refl. Qed.
Lemma D_5d398 : decode_any W_5d398 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d39c : bv 32 := 0x04813983.
Lemma F_5d39c : fetch_word AsanUbsan.M.loaded_segments (0x5d3e4 : word) = Some W_5d39c.
Proof. vm_refl. Qed.
Lemma D_5d39c : decode_any W_5d39c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3a0 : bv 32 := 0x04013a03.
Lemma F_5d3a0 : fetch_word AsanUbsan.M.loaded_segments (0x5d3e8 : word) = Some W_5d3a0.
Proof. vm_refl. Qed.
Lemma D_5d3a0 : decode_any W_5d3a0 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3a4 : bv 32 := 0x03813a83.
Lemma F_5d3a4 : fetch_word AsanUbsan.M.loaded_segments (0x5d3ec : word) = Some W_5d3a4.
Proof. vm_refl. Qed.
Lemma D_5d3a4 : decode_any W_5d3a4 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3a8 : bv 32 := 0x03013b03.
Lemma F_5d3a8 : fetch_word AsanUbsan.M.loaded_segments (0x5d3f0 : word) = Some W_5d3a8.
Proof. vm_refl. Qed.
Lemma D_5d3a8 : decode_any W_5d3a8 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3ac : bv 32 := 0x02813b83.
Lemma F_5d3ac : fetch_word AsanUbsan.M.loaded_segments (0x5d3f4 : word) = Some W_5d3ac.
Proof. vm_refl. Qed.
Lemma D_5d3ac : decode_any W_5d3ac = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3b0 : bv 32 := 0x02013c03.
Lemma F_5d3b0 : fetch_word AsanUbsan.M.loaded_segments (0x5d3f8 : word) = Some W_5d3b0.
Proof. vm_refl. Qed.
Lemma D_5d3b0 : decode_any W_5d3b0 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3b4 : bv 32 := 0x01813c83.
Lemma F_5d3b4 : fetch_word AsanUbsan.M.loaded_segments (0x5d3fc : word) = Some W_5d3b4.
Proof. vm_refl. Qed.
Lemma D_5d3b4 : decode_any W_5d3b4 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3b8 : bv 32 := 0x07010113.
Lemma F_5d3b8 : fetch_word AsanUbsan.M.loaded_segments (0x5d400 : word) = Some W_5d3b8.
Proof. vm_refl. Qed.
Lemma D_5d3b8 : decode_any W_5d3b8 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3bc : bv 32 := 0x00008067.
Lemma F_5d3bc : fetch_word AsanUbsan.M.loaded_segments (0x5d404 : word) = Some W_5d3bc.
Proof. vm_refl. Qed.
Lemma D_5d3bc : decode_any W_5d3bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3c0 : bv 32 := 0xfd010113.
Lemma F_5d3c0 : fetch_word AsanUbsan.M.loaded_segments (0x5d408 : word) = Some W_5d3c0.
Proof. vm_refl. Qed.
Lemma D_5d3c0 : decode_any W_5d3c0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3c4 : bv 32 := 0x02113423.
Lemma F_5d3c4 : fetch_word AsanUbsan.M.loaded_segments (0x5d40c : word) = Some W_5d3c4.
Proof. vm_refl. Qed.
Lemma D_5d3c4 : decode_any W_5d3c4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3c8 : bv 32 := 0x02813023.
Lemma F_5d3c8 : fetch_word AsanUbsan.M.loaded_segments (0x5d410 : word) = Some W_5d3c8.
Proof. vm_refl. Qed.
Lemma D_5d3c8 : decode_any W_5d3c8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3cc : bv 32 := 0x00913c23.
Lemma F_5d3cc : fetch_word AsanUbsan.M.loaded_segments (0x5d414 : word) = Some W_5d3cc.
Proof. vm_refl. Qed.
Lemma D_5d3cc : decode_any W_5d3cc = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3d0 : bv 32 := 0x01213823.
Lemma F_5d3d0 : fetch_word AsanUbsan.M.loaded_segments (0x5d418 : word) = Some W_5d3d0.
Proof. vm_refl. Qed.
Lemma D_5d3d0 : decode_any W_5d3d0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3d4 : bv 32 := 0x01313423.
Lemma F_5d3d4 : fetch_word AsanUbsan.M.loaded_segments (0x5d41c : word) = Some W_5d3d4.
Proof. vm_refl. Qed.
Lemma D_5d3d4 : decode_any W_5d3d4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3d8 : bv 32 := 0x01413023.
Lemma F_5d3d8 : fetch_word AsanUbsan.M.loaded_segments (0x5d420 : word) = Some W_5d3d8.
Proof. vm_refl. Qed.
Lemma D_5d3d8 : decode_any W_5d3d8 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3dc : bv 32 := 0x00058493.
Lemma F_5d3dc : fetch_word AsanUbsan.M.loaded_segments (0x5d424 : word) = Some W_5d3dc.
Proof. vm_refl. Qed.
Lemma D_5d3dc : decode_any W_5d3dc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3e0 : bv 32 := 0x00050413.
Lemma F_5d3e0 : fetch_word AsanUbsan.M.loaded_segments (0x5d428 : word) = Some W_5d3e0.
Proof. vm_refl. Qed.
Lemma D_5d3e0 : decode_any W_5d3e0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3e4 : bv 32 := 0x0010d517.
Lemma F_5d3e4 : fetch_word AsanUbsan.M.loaded_segments (0x5d42c : word) = Some W_5d3e4.
Proof. vm_refl. Qed.
Lemma D_5d3e4 : decode_any W_5d3e4 = Some (Auipc 10 269, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3e8 : bv 32 := 0xd2c50993.
Lemma F_5d3e8 : fetch_word AsanUbsan.M.loaded_segments (0x5d430 : word) = Some W_5d3e8.
Proof. vm_refl. Qed.
Lemma D_5d3e8 : decode_any W_5d3e8 = Some (OpImm ALU_ADD 19 10 3372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3ec : bv 32 := 0x0209b503.
Lemma F_5d3ec : fetch_word AsanUbsan.M.loaded_segments (0x5d434 : word) = Some W_5d3ec.
Proof. vm_refl. Qed.
Lemma D_5d3ec : decode_any W_5d3ec = Some (Load SZ8 true 10 19 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3f0 : bv 32 := 0x00100a13.
Lemma F_5d3f0 : fetch_word AsanUbsan.M.loaded_segments (0x5d438 : word) = Some W_5d3f0.
Proof. vm_refl. Qed.
Lemma D_5d3f0 : decode_any W_5d3f0 = Some (OpImm ALU_ADD 20 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3f4 : bv 32 := 0x025a1a13.
Lemma F_5d3f4 : fetch_word AsanUbsan.M.loaded_segments (0x5d43c : word) = Some W_5d3f4.
Proof. vm_refl. Qed.
Lemma D_5d3f4 : decode_any W_5d3f4 = Some (ShiftImm ALU_SLL 20 20 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3f8 : bv 32 := 0x02a5ea63.
Lemma F_5d3f8 : fetch_word AsanUbsan.M.loaded_segments (0x5d440 : word) = Some W_5d3f8.
Proof. vm_refl. Qed.
Lemma D_5d3f8 : decode_any W_5d3f8 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3fc : bv 32 := 0x014505b3.
Lemma F_5d3fc : fetch_word AsanUbsan.M.loaded_segments (0x5d444 : word) = Some W_5d3fc.
Proof. vm_refl. Qed.
Lemma D_5d3fc : decode_any W_5d3fc = Some (Op ALU_ADD 11 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d400 : bv 32 := 0x02b4f663.
Lemma F_5d400 : fetch_word AsanUbsan.M.loaded_segments (0x5d448 : word) = Some W_5d400.
Proof. vm_refl. Qed.
Lemma D_5d400 : decode_any W_5d400 = Some (Branch BC_GEU 9 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d404 : bv 32 := 0x40a48733.
Lemma F_5d404 : fetch_word AsanUbsan.M.loaded_segments (0x5d44c : word) = Some W_5d404.
Proof. vm_refl. Qed.
Lemma D_5d404 : decode_any W_5d404 = Some (Op ALU_SUB 14 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d408 : bv 32 := 0x02075693.
Lemma F_5d408 : fetch_word AsanUbsan.M.loaded_segments (0x5d450 : word) = Some W_5d408.
Proof. vm_refl. Qed.
Lemma D_5d408 : decode_any W_5d408 = Some (ShiftImm ALU_SRL 13 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d40c : bv 32 := 0x01f6f613.
Lemma F_5d40c : fetch_word AsanUbsan.M.loaded_segments (0x5d454 : word) = Some W_5d40c.
Proof. vm_refl. Qed.
Lemma D_5d40c : decode_any W_5d40c = Some (OpImm ALU_AND 12 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d410 : bv 32 := 0x01f00793.
Lemma F_5d410 : fetch_word AsanUbsan.M.loaded_segments (0x5d458 : word) = Some W_5d410.
Proof. vm_refl. Qed.
Lemma D_5d410 : decode_any W_5d410 = Some (OpImm ALU_ADD 15 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d414 : bv 32 := 0x1ef60663.
Lemma F_5d414 : fetch_word AsanUbsan.M.loaded_segments (0x5d45c : word) = Some W_5d414.
Proof. vm_refl. Qed.
Lemma D_5d414 : decode_any W_5d414 = Some (Branch BC_EQ 12 15 492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d418 : bv 32 := 0x01100793.
Lemma F_5d418 : fetch_word AsanUbsan.M.loaded_segments (0x5d460 : word) = Some W_5d418.
Proof. vm_refl. Qed.
Lemma D_5d418 : decode_any W_5d418 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d41c : bv 32 := 0x02f67863.
Lemma F_5d41c : fetch_word AsanUbsan.M.loaded_segments (0x5d464 : word) = Some W_5d41c.
Proof. vm_refl. Qed.
Lemma D_5d41c : decode_any W_5d41c = Some (Branch BC_GEU 12 15 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d420 : bv 32 := 0x1c060a63.
Lemma F_5d420 : fetch_word AsanUbsan.M.loaded_segments (0x5d468 : word) = Some W_5d420.
Proof. vm_refl. Qed.
Lemma D_5d420 : decode_any W_5d420 = Some (Branch BC_EQ 12 0 468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d424 : bv 32 := 0x00561793.
Lemma F_5d424 : fetch_word AsanUbsan.M.loaded_segments (0x5d46c : word) = Some W_5d424.
Proof. vm_refl. Qed.
Lemma D_5d424 : decode_any W_5d424 = Some (ShiftImm ALU_SLL 15 12 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d428 : bv 32 := 0x0480006f.
Lemma F_5d428 : fetch_word AsanUbsan.M.loaded_segments (0x5d470 : word) = Some W_5d428.
Proof. vm_refl. Qed.
Lemma D_5d428 : decode_any W_5d428 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d42c : bv 32 := 0x04098513.
Lemma F_5d42c : fetch_word AsanUbsan.M.loaded_segments (0x5d474 : word) = Some W_5d42c.
Proof. vm_refl. Qed.
Lemma D_5d42c : decode_any W_5d42c = Some (OpImm ALU_ADD 10 19 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d430 : bv 32 := 0x00048593.
Lemma F_5d430 : fetch_word AsanUbsan.M.loaded_segments (0x5d478 : word) = Some W_5d430.
Proof. vm_refl. Qed.
Lemma D_5d430 : decode_any W_5d430 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d434 : bv 32 := 0x210000ef.
Lemma F_5d434 : fetch_word AsanUbsan.M.loaded_segments (0x5d47c : word) = Some W_5d434.
Proof. vm_refl. Qed.
Lemma D_5d434 : decode_any W_5d434 = Some (Jal 1 528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d438 : bv 32 := 0x00050913.
Lemma F_5d438 : fetch_word AsanUbsan.M.loaded_segments (0x5d480 : word) = Some W_5d438.
Proof. vm_refl. Qed.
Lemma D_5d438 : decode_any W_5d438 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d43c : bv 32 := 0x0209b503.
Lemma F_5d43c : fetch_word AsanUbsan.M.loaded_segments (0x5d484 : word) = Some W_5d43c.
Proof. vm_refl. Qed.
Lemma D_5d43c : decode_any W_5d43c = Some (Load SZ8 true 10 19 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d440 : bv 32 := 0x014505b3.
Lemma F_5d440 : fetch_word AsanUbsan.M.loaded_segments (0x5d488 : word) = Some W_5d440.
Proof. vm_refl. Qed.
Lemma D_5d440 : decode_any W_5d440 = Some (Op ALU_ADD 11 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d444 : bv 32 := 0x06a97663.
Lemma F_5d444 : fetch_word AsanUbsan.M.loaded_segments (0x5d48c : word) = Some W_5d444.
Proof. vm_refl. Qed.
Lemma D_5d444 : decode_any W_5d444 = Some (Branch BC_GEU 18 10 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d448 : bv 32 := 0x0e40006f.
Lemma F_5d448 : fetch_word AsanUbsan.M.loaded_segments (0x5d490 : word) = Some W_5d448.
Proof. vm_refl. Qed.
Lemma D_5d448 : decode_any W_5d448 = Some (Jal 0 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d44c : bv 32 := 0xff060793.
Lemma F_5d44c : fetch_word AsanUbsan.M.loaded_segments (0x5d494 : word) = Some W_5d44c.
Proof. vm_refl. Qed.
Lemma D_5d44c : decode_any W_5d44c = Some (OpImm ALU_ADD 15 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d450 : bv 32 := 0x20000813.
Lemma F_5d450 : fetch_word AsanUbsan.M.loaded_segments (0x5d498 : word) = Some W_5d450.
Proof. vm_refl. Qed.
Lemma D_5d450 : decode_any W_5d450 = Some (OpImm ALU_ADD 16 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d454 : bv 32 := 0x03f69893.
Lemma F_5d454 : fetch_word AsanUbsan.M.loaded_segments (0x5d49c : word) = Some W_5d454.
Proof. vm_refl. Qed.
Lemma D_5d454 : decode_any W_5d454 = Some (ShiftImm ALU_SLL 17 13 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d458 : bv 32 := 0x0017d793.
Lemma F_5d458 : fetch_word AsanUbsan.M.loaded_segments (0x5d4a0 : word) = Some W_5d458.
Proof. vm_refl. Qed.
Lemma D_5d458 : decode_any W_5d458 = Some (ShiftImm ALU_SRL 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d45c : bv 32 := 0x00f817b3.
Lemma F_5d45c : fetch_word AsanUbsan.M.loaded_segments (0x5d4a4 : word) = Some W_5d45c.
Proof. vm_refl. Qed.
Lemma D_5d45c : decode_any W_5d45c = Some (Op ALU_SLL 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d460 : bv 32 := 0x0017d813.
Lemma F_5d460 : fetch_word AsanUbsan.M.loaded_segments (0x5d4a8 : word) = Some W_5d460.
Proof. vm_refl. Qed.
Lemma D_5d460 : decode_any W_5d460 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d464 : bv 32 := 0x43f8d893.
Lemma F_5d464 : fetch_word AsanUbsan.M.loaded_segments (0x5d4ac : word) = Some W_5d464.
Proof. vm_refl. Qed.
Lemma D_5d464 : decode_any W_5d464 = Some (ShiftImm ALU_SRA 17 17 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d468 : bv 32 := 0x0108f833.
Lemma F_5d468 : fetch_word AsanUbsan.M.loaded_segments (0x5d4b0 : word) = Some W_5d468.
Proof. vm_refl. Qed.
Lemma D_5d468 : decode_any W_5d468 = Some (Op ALU_AND 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d46c : bv 32 := 0x00f807b3.
Lemma F_5d46c : fetch_word AsanUbsan.M.loaded_segments (0x5d4b4 : word) = Some W_5d46c.
Proof. vm_refl. Qed.
Lemma D_5d46c : decode_any W_5d46c = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d470 : bv 32 := 0x02f7573b.
Lemma F_5d470 : fetch_word AsanUbsan.M.loaded_segments (0x5d4b8 : word) = Some W_5d470.
Proof. vm_refl. Qed.
Lemma D_5d470 : decode_any W_5d470 = Some (Mul32 M_DIVU 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d474 : bv 32 := 0x02069693.
Lemma F_5d474 : fetch_word AsanUbsan.M.loaded_segments (0x5d4bc : word) = Some W_5d474.
Proof. vm_refl. Qed.
Lemma D_5d474 : decode_any W_5d474 = Some (ShiftImm ALU_SLL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d478 : bv 32 := 0x0309b803.
Lemma F_5d478 : fetch_word AsanUbsan.M.loaded_segments (0x5d4c0 : word) = Some W_5d478.
Proof. vm_refl. Qed.
Lemma D_5d478 : decode_any W_5d478 = Some (Load SZ8 true 16 19 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d47c : bv 32 := 0x00761613.
Lemma F_5d47c : fetch_word AsanUbsan.M.loaded_segments (0x5d4c4 : word) = Some W_5d47c.
Proof. vm_refl. Qed.
Lemma D_5d47c : decode_any W_5d47c = Some (ShiftImm ALU_SLL 12 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d480 : bv 32 := 0x02071713.
Lemma F_5d480 : fetch_word AsanUbsan.M.loaded_segments (0x5d4c8 : word) = Some W_5d480.
Proof. vm_refl. Qed.
Lemma D_5d480 : decode_any W_5d480 = Some (ShiftImm ALU_SLL 14 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d484 : bv 32 := 0x00a686b3.
Lemma F_5d484 : fetch_word AsanUbsan.M.loaded_segments (0x5d4cc : word) = Some W_5d484.
Proof. vm_refl. Qed.
Lemma D_5d484 : decode_any W_5d484 = Some (Op ALU_ADD 13 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d488 : bv 32 := 0x00c80633.
Lemma F_5d488 : fetch_word AsanUbsan.M.loaded_segments (0x5d4d0 : word) = Some W_5d488.
Proof. vm_refl. Qed.
Lemma D_5d488 : decode_any W_5d488 = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d48c : bv 32 := 0x03063603.
Lemma F_5d48c : fetch_word AsanUbsan.M.loaded_segments (0x5d4d4 : word) = Some W_5d48c.
Proof. vm_refl. Qed.
Lemma D_5d48c : decode_any W_5d48c = Some (Load SZ8 true 12 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d490 : bv 32 := 0x02075713.
Lemma F_5d490 : fetch_word AsanUbsan.M.loaded_segments (0x5d4d8 : word) = Some W_5d490.
Proof. vm_refl. Qed.
Lemma D_5d490 : decode_any W_5d490 = Some (ShiftImm ALU_SRL 14 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d494 : bv 32 := 0x02e78733.
Lemma F_5d494 : fetch_word AsanUbsan.M.loaded_segments (0x5d4dc : word) = Some W_5d494.
Proof. vm_refl. Qed.
Lemma D_5d494 : decode_any W_5d494 = Some (Mul M_MUL 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d498 : bv 32 := 0x00f707b3.
Lemma F_5d498 : fetch_word AsanUbsan.M.loaded_segments (0x5d4e0 : word) = Some W_5d498.
Proof. vm_refl. Qed.
Lemma D_5d498 : decode_any W_5d498 = Some (Op ALU_ADD 15 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d49c : bv 32 := 0x00f63633.
Lemma F_5d49c : fetch_word AsanUbsan.M.loaded_segments (0x5d4e4 : word) = Some W_5d49c.
Proof. vm_refl. Qed.
Lemma D_5d49c : decode_any W_5d49c = Some (Op ALU_SLTU 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4a0 : bv 32 := 0x00e686b3.
Lemma F_5d4a0 : fetch_word AsanUbsan.M.loaded_segments (0x5d4e8 : word) = Some W_5d4a0.
Proof. vm_refl. Qed.
Lemma D_5d4a0 : decode_any W_5d4a0 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4a4 : bv 32 := 0xfff60613.
Lemma F_5d4a4 : fetch_word AsanUbsan.M.loaded_segments (0x5d4ec : word) = Some W_5d4a4.
Proof. vm_refl. Qed.
Lemma D_5d4a4 : decode_any W_5d4a4 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4a8 : bv 32 := 0x00d67933.
Lemma F_5d4a8 : fetch_word AsanUbsan.M.loaded_segments (0x5d4f0 : word) = Some W_5d4a8.
Proof. vm_refl. Qed.
Lemma D_5d4a8 : decode_any W_5d4a8 = Some (Op ALU_AND 18 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4ac : bv 32 := 0x08a96063.
Lemma F_5d4ac : fetch_word AsanUbsan.M.loaded_segments (0x5d4f4 : word) = Some W_5d4ac.
Proof. vm_refl. Qed.
Lemma D_5d4ac : decode_any W_5d4ac = Some (Branch BC_LTU 18 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4b0 : bv 32 := 0x06b97e63.
Lemma F_5d4b0 : fetch_word AsanUbsan.M.loaded_segments (0x5d4f8 : word) = Some W_5d4b0.
Proof. vm_refl. Qed.
Lemma D_5d4b0 : decode_any W_5d4b0 = Some (Branch BC_GEU 18 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4b4 : bv 32 := 0x00990e63.
Lemma F_5d4b4 : fetch_word AsanUbsan.M.loaded_segments (0x5d4fc : word) = Some W_5d4b4.
Proof. vm_refl. Qed.
Lemma D_5d4b4 : decode_any W_5d4b4 = Some (Branch BC_EQ 18 9 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4b8 : bv 32 := 0xfffb3517.
Lemma F_5d4b8 : fetch_word AsanUbsan.M.loaded_segments (0x5d500 : word) = Some W_5d4b8.
Proof. vm_refl. Qed.
Lemma D_5d4b8 : decode_any W_5d4b8 = Some (Auipc 10 1048499, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4bc : bv 32 := 0xe8853703.
Lemma F_5d4bc : fetch_word AsanUbsan.M.loaded_segments (0x5d504 : word) = Some W_5d4bc.
Proof. vm_refl. Qed.
Lemma D_5d4bc : decode_any W_5d4bc = Some (Load SZ8 true 14 10 3720, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4c0 : bv 32 := 0x160936af.
Lemma F_5d4c0 : fetch_word AsanUbsan.M.loaded_segments (0x5d508 : word) = Some W_5d4c0.
Proof. vm_refl. Qed.
Lemma D_5d4c0 : decode_any W_5d4c0 = Some (Lr AD true true 13 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4c4 : bv 32 := 0x16e69463.
Lemma F_5d4c4 : fetch_word AsanUbsan.M.loaded_segments (0x5d50c : word) = Some W_5d4c4.
Proof. vm_refl. Qed.
Lemma D_5d4c4 : decode_any W_5d4c4 = Some (Branch BC_NE 13 14 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4c8 : bv 32 := 0x1a09352f.
Lemma F_5d4c8 : fetch_word AsanUbsan.M.loaded_segments (0x5d510 : word) = Some W_5d4c8.
Proof. vm_refl. Qed.
Lemma D_5d4c8 : decode_any W_5d4c8 = Some (Sc AD false true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4cc : bv 32 := 0xfe051ae3.
Lemma F_5d4cc : fetch_word AsanUbsan.M.loaded_segments (0x5d514 : word) = Some W_5d4cc.
Proof. vm_refl. Qed.
Lemma D_5d4cc : decode_any W_5d4cc = Some (Branch BC_NE 10 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4d0 : bv 32 := 0xffc4f613.
Lemma F_5d4d0 : fetch_word AsanUbsan.M.loaded_segments (0x5d518 : word) = Some W_5d4d0.
Proof. vm_refl. Qed.
Lemma D_5d4d0 : decode_any W_5d4d0 = Some (OpImm ALU_AND 12 9 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4d4 : bv 32 := 0x00349513.
Lemma F_5d4d4 : fetch_word AsanUbsan.M.loaded_segments (0x5d51c : word) = Some W_5d4d4.
Proof. vm_refl. Qed.
Lemma D_5d4d4 : decode_any W_5d4d4 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4d8 : bv 32 := 0x0ff00593.
Lemma F_5d4d8 : fetch_word AsanUbsan.M.loaded_segments (0x5d520 : word) = Some W_5d4d8.
Proof. vm_refl. Qed.
Lemma D_5d4d8 : decode_any W_5d4d8 = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4dc : bv 32 := 0x00300693.
Lemma F_5d4dc : fetch_word AsanUbsan.M.loaded_segments (0x5d524 : word) = Some W_5d4dc.
Proof. vm_refl. Qed.
Lemma D_5d4dc : decode_any W_5d4dc = Some (OpImm ALU_ADD 13 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4e0 : bv 32 := 0x00a5973b.
Lemma F_5d4e0 : fetch_word AsanUbsan.M.loaded_segments (0x5d528 : word) = Some W_5d4e0.
Proof. vm_refl. Qed.
Lemma D_5d4e0 : decode_any W_5d4e0 = Some (Op32 ALU_SLL 14 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4e4 : bv 32 := 0x00a696bb.
Lemma F_5d4e4 : fetch_word AsanUbsan.M.loaded_segments (0x5d52c : word) = Some W_5d4e4.
Proof. vm_refl. Qed.
Lemma D_5d4e4 : decode_any W_5d4e4 = Some (Op32 ALU_SLL 13 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4e8 : bv 32 := 0x160625af.
Lemma F_5d4e8 : fetch_word AsanUbsan.M.loaded_segments (0x5d530 : word) = Some W_5d4e8.
Proof. vm_refl. Qed.
Lemma D_5d4e8 : decode_any W_5d4e8 = Some (Lr AW true true 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4ec : bv 32 := 0x00e5f7b3.
Lemma F_5d4ec : fetch_word AsanUbsan.M.loaded_segments (0x5d534 : word) = Some W_5d4ec.
Proof. vm_refl. Qed.
Lemma D_5d4ec : decode_any W_5d4ec = Some (Op ALU_AND 15 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4f0 : bv 32 := 0x10d79c63.
Lemma F_5d4f0 : fetch_word AsanUbsan.M.loaded_segments (0x5d538 : word) = Some W_5d4f0.
Proof. vm_refl. Qed.
Lemma D_5d4f0 : decode_any W_5d4f0 = Some (Branch BC_NE 15 13 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4f4 : bv 32 := 0x0005c7b3.
Lemma F_5d4f4 : fetch_word AsanUbsan.M.loaded_segments (0x5d53c : word) = Some W_5d4f4.
Proof. vm_refl. Qed.
Lemma D_5d4f4 : decode_any W_5d4f4 = Some (Op ALU_XOR 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4f8 : bv 32 := 0x00e7f7b3.
Lemma F_5d4f8 : fetch_word AsanUbsan.M.loaded_segments (0x5d540 : word) = Some W_5d4f8.
Proof. vm_refl. Qed.
Lemma D_5d4f8 : decode_any W_5d4f8 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4fc : bv 32 := 0x00f5c7b3.
Lemma F_5d4fc : fetch_word AsanUbsan.M.loaded_segments (0x5d544 : word) = Some W_5d4fc.
Proof. vm_refl. Qed.
Lemma D_5d4fc : decode_any W_5d4fc = Some (Op ALU_XOR 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d500 : bv 32 := 0x1af627af.
Lemma F_5d500 : fetch_word AsanUbsan.M.loaded_segments (0x5d548 : word) = Some W_5d500.
Proof. vm_refl. Qed.
Lemma D_5d500 : decode_any W_5d500 = Some (Sc AW false true 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d504 : bv 32 := 0xfe0792e3.
Lemma F_5d504 : fetch_word AsanUbsan.M.loaded_segments (0x5d54c : word) = Some W_5d504.
Proof. vm_refl. Qed.
Lemma D_5d504 : decode_any W_5d504 = Some (Branch BC_NE 15 0 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d508 : bv 32 := 0x0024d583.
Lemma F_5d508 : fetch_word AsanUbsan.M.loaded_segments (0x5d550 : word) = Some W_5d508.
Proof. vm_refl. Qed.
Lemma D_5d508 : decode_any W_5d508 = Some (Load SZ2 false 11 9 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d50c : bv 32 := 0x0044e603.
Lemma F_5d50c : fetch_word AsanUbsan.M.loaded_segments (0x5d554 : word) = Some W_5d50c.
Proof. vm_refl. Qed.
Lemma D_5d50c : decode_any W_5d50c = Some (Load SZ4 false 12 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d510 : bv 32 := 0x01048513.
Lemma F_5d510 : fetch_word AsanUbsan.M.loaded_segments (0x5d558 : word) = Some W_5d510.
Proof. vm_refl. Qed.
Lemma D_5d510 : decode_any W_5d510 = Some (OpImm ALU_ADD 10 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d514 : bv 32 := 0x02059593.
Lemma F_5d514 : fetch_word AsanUbsan.M.loaded_segments (0x5d55c : word) = Some W_5d514.
Proof. vm_refl. Qed.
Lemma D_5d514 : decode_any W_5d514 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d518 : bv 32 := 0x00c5e5b3.
Lemma F_5d518 : fetch_word AsanUbsan.M.loaded_segments (0x5d560 : word) = Some W_5d518.
Proof. vm_refl. Qed.
Lemma D_5d518 : decode_any W_5d518 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d51c : bv 32 := 0x00758593.
Lemma F_5d51c : fetch_word AsanUbsan.M.loaded_segments (0x5d564 : word) = Some W_5d51c.
Proof. vm_refl. Qed.
Lemma D_5d51c : decode_any W_5d51c = Some (OpImm ALU_ADD 11 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d520 : bv 32 := 0xff85f593.
Lemma F_5d520 : fetch_word AsanUbsan.M.loaded_segments (0x5d568 : word) = Some W_5d520.
Proof. vm_refl. Qed.
Lemma D_5d520 : decode_any W_5d520 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d524 : bv 32 := 0x0fa00613.
Lemma F_5d524 : fetch_word AsanUbsan.M.loaded_segments (0x5d56c : word) = Some W_5d524.
Proof. vm_refl. Qed.
Lemma D_5d524 : decode_any W_5d524 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d528 : bv 32 := 0x444260ef.
Lemma F_5d528 : fetch_word AsanUbsan.M.loaded_segments (0x5d570 : word) = Some W_5d528.
Proof. vm_refl. Qed.
Lemma D_5d528 : decode_any W_5d528 = Some (Jal 1 156740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d52c : bv 32 := 0x3b82e0ef.
Lemma F_5d52c : fetch_word AsanUbsan.M.loaded_segments (0x5d574 : word) = Some W_5d52c.
Proof. vm_refl. Qed.
Lemma D_5d52c : decode_any W_5d52c = Some (Jal 1 189368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d530 : bv 32 := 0x0024d583.
Lemma F_5d530 : fetch_word AsanUbsan.M.loaded_segments (0x5d578 : word) = Some W_5d530.
Proof. vm_refl. Qed.
Lemma D_5d530 : decode_any W_5d530 = Some (Load SZ2 false 11 9 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d534 : bv 32 := 0x0044e603.
Lemma F_5d534 : fetch_word AsanUbsan.M.loaded_segments (0x5d57c : word) = Some W_5d534.
Proof. vm_refl. Qed.
Lemma D_5d534 : decode_any W_5d534 = Some (Load SZ4 false 12 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d538 : bv 32 := 0x03053683.
Lemma F_5d538 : fetch_word AsanUbsan.M.loaded_segments (0x5d580 : word) = Some W_5d538.
Proof. vm_refl. Qed.
Lemma D_5d538 : decode_any W_5d538 = Some (Load SZ8 true 13 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d53c : bv 32 := 0x02853703.
Lemma F_5d53c : fetch_word AsanUbsan.M.loaded_segments (0x5d584 : word) = Some W_5d53c.
Proof. vm_refl. Qed.
Lemma D_5d53c : decode_any W_5d53c = Some (Load SZ8 true 14 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d540 : bv 32 := 0x02059593.
Lemma F_5d540 : fetch_word AsanUbsan.M.loaded_segments (0x5d588 : word) = Some W_5d540.
Proof. vm_refl. Qed.
Lemma D_5d540 : decode_any W_5d540 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d544 : bv 32 := 0x00c5e5b3.
Lemma F_5d544 : fetch_word AsanUbsan.M.loaded_segments (0x5d58c : word) = Some W_5d544.
Proof. vm_refl. Qed.
Lemma D_5d544 : decode_any W_5d544 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d548 : bv 32 := 0x00d585b3.
Lemma F_5d548 : fetch_word AsanUbsan.M.loaded_segments (0x5d590 : word) = Some W_5d548.
Proof. vm_refl. Qed.
Lemma D_5d548 : decode_any W_5d548 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d54c : bv 32 := 0x00170713.
Lemma F_5d54c : fetch_word AsanUbsan.M.loaded_segments (0x5d594 : word) = Some W_5d54c.
Proof. vm_refl. Qed.
Lemma D_5d54c : decode_any W_5d54c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d550 : bv 32 := 0x02e53423.
Lemma F_5d550 : fetch_word AsanUbsan.M.loaded_segments (0x5d598 : word) = Some W_5d550.
Proof. vm_refl. Qed.
Lemma D_5d550 : decode_any W_5d550 = Some (Store SZ8 10 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d554 : bv 32 := 0x02b53823.
Lemma F_5d554 : fetch_word AsanUbsan.M.loaded_segments (0x5d59c : word) = Some W_5d554.
Proof. vm_refl. Qed.
Lemma D_5d554 : decode_any W_5d554 = Some (Store SZ8 10 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d558 : bv 32 := 0x04090863.
Lemma F_5d558 : fetch_word AsanUbsan.M.loaded_segments (0x5d5a0 : word) = Some W_5d558.
Proof. vm_refl. Qed.
Lemma D_5d558 : decode_any W_5d558 = Some (Branch BC_EQ 18 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d55c : bv 32 := 0x0209b583.
Lemma F_5d55c : fetch_word AsanUbsan.M.loaded_segments (0x5d5a4 : word) = Some W_5d55c.
Proof. vm_refl. Qed.
Lemma D_5d55c : decode_any W_5d55c = Some (Load SZ8 true 11 19 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d560 : bv 32 := 0x06b96463.
Lemma F_5d560 : fetch_word AsanUbsan.M.loaded_segments (0x5d5a8 : word) = Some W_5d560.
Proof. vm_refl. Qed.
Lemma D_5d560 : decode_any W_5d560 = Some (Branch BC_LTU 18 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d564 : bv 32 := 0x01458a33.
Lemma F_5d564 : fetch_word AsanUbsan.M.loaded_segments (0x5d5ac : word) = Some W_5d564.
Proof. vm_refl. Qed.
Lemma D_5d564 : decode_any W_5d564 = Some (Op ALU_ADD 20 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d568 : bv 32 := 0x07497063.
Lemma F_5d568 : fetch_word AsanUbsan.M.loaded_segments (0x5d5b0 : word) = Some W_5d568.
Proof. vm_refl. Qed.
Lemma D_5d568 : decode_any W_5d568 = Some (Branch BC_GEU 18 20 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d56c : bv 32 := 0x00043503.
Lemma F_5d56c : fetch_word AsanUbsan.M.loaded_segments (0x5d5b4 : word) = Some W_5d56c.
Proof. vm_refl. Qed.
Lemma D_5d56c : decode_any W_5d56c = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d570 : bv 32 := 0x40b905b3.
Lemma F_5d570 : fetch_word AsanUbsan.M.loaded_segments (0x5d5b8 : word) = Some W_5d570.
Proof. vm_refl. Qed.
Lemma D_5d570 : decode_any W_5d570 = Some (Op ALU_SUB 11 18 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d574 : bv 32 := 0x01b59593.
Lemma F_5d574 : fetch_word AsanUbsan.M.loaded_segments (0x5d5bc : word) = Some W_5d574.
Proof. vm_refl. Qed.
Lemma D_5d574 : decode_any W_5d574 = Some (ShiftImm ALU_SLL 11 11 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d578 : bv 32 := 0x03b5d613.
Lemma F_5d578 : fetch_word AsanUbsan.M.loaded_segments (0x5d5c0 : word) = Some W_5d578.
Proof. vm_refl. Qed.
Lemma D_5d578 : decode_any W_5d578 = Some (ShiftImm ALU_SRL 12 11 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d57c : bv 32 := 0x0010d597.
Lemma F_5d57c : fetch_word AsanUbsan.M.loaded_segments (0x5d5c4 : word) = Some W_5d57c.
Proof. vm_refl. Qed.
Lemma D_5d57c : decode_any W_5d57c = Some (Auipc 11 269, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d580 : bv 32 := 0xb9458593.
Lemma F_5d580 : fetch_word AsanUbsan.M.loaded_segments (0x5d5c8 : word) = Some W_5d580.
Proof. vm_refl. Qed.
Lemma D_5d580 : decode_any W_5d580 = Some (OpImm ALU_ADD 11 11 2964, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d584 : bv 32 := 0x00090693.
Lemma F_5d584 : fetch_word AsanUbsan.M.loaded_segments (0x5d5cc : word) = Some W_5d584.
Proof. vm_refl. Qed.
Lemma D_5d584 : decode_any W_5d584 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d588 : bv 32 := 0x02813083.
Lemma F_5d588 : fetch_word AsanUbsan.M.loaded_segments (0x5d5d0 : word) = Some W_5d588.
Proof. vm_refl. Qed.
Lemma D_5d588 : decode_any W_5d588 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d58c : bv 32 := 0x02013403.
Lemma F_5d58c : fetch_word AsanUbsan.M.loaded_segments (0x5d5d4 : word) = Some W_5d58c.
Proof. vm_refl. Qed.
Lemma D_5d58c : decode_any W_5d58c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d590 : bv 32 := 0x01813483.
Lemma F_5d590 : fetch_word AsanUbsan.M.loaded_segments (0x5d5d8 : word) = Some W_5d590.
Proof. vm_refl. Qed.
Lemma D_5d590 : decode_any W_5d590 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d594 : bv 32 := 0x01013903.
Lemma F_5d594 : fetch_word AsanUbsan.M.loaded_segments (0x5d5dc : word) = Some W_5d594.
Proof. vm_refl. Qed.
Lemma D_5d594 : decode_any W_5d594 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d598 : bv 32 := 0x00813983.
Lemma F_5d598 : fetch_word AsanUbsan.M.loaded_segments (0x5d5e0 : word) = Some W_5d598.
Proof. vm_refl. Qed.
Lemma D_5d598 : decode_any W_5d598 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d59c : bv 32 := 0x00013a03.
Lemma F_5d59c : fetch_word AsanUbsan.M.loaded_segments (0x5d5e4 : word) = Some W_5d59c.
Proof. vm_refl. Qed.
Lemma D_5d59c : decode_any W_5d59c = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5a0 : bv 32 := 0x03010113.
Lemma F_5d5a0 : fetch_word AsanUbsan.M.loaded_segments (0x5d5e8 : word) = Some W_5d5a0.
Proof. vm_refl. Qed.
Lemma D_5d5a0 : decode_any W_5d5a0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5a4 : bv 32 := 0x2200006f.
Lemma F_5d5a4 : fetch_word AsanUbsan.M.loaded_segments (0x5d5ec : word) = Some W_5d5a4.
Proof. vm_refl. Qed.
Lemma D_5d5a4 : decode_any W_5d5a4 = Some (Jal 0 544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5c8 : bv 32 := 0x04098513.
Lemma F_5d5c8 : fetch_word AsanUbsan.M.loaded_segments (0x5d610 : word) = Some W_5d5c8.
Proof. vm_refl. Qed.
Lemma D_5d5c8 : decode_any W_5d5c8 = Some (OpImm ALU_ADD 10 19 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5cc : bv 32 := 0x2b098593.
Lemma F_5d5cc : fetch_word AsanUbsan.M.loaded_segments (0x5d614 : word) = Some W_5d5cc.
Proof. vm_refl. Qed.
Lemma D_5d5cc : decode_any W_5d5cc = Some (OpImm ALU_ADD 11 19 688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5d0 : bv 32 := 0x00090613.
Lemma F_5d5d0 : fetch_word AsanUbsan.M.loaded_segments (0x5d618 : word) = Some W_5d5d0.
Proof. vm_refl. Qed.
Lemma D_5d5d0 : decode_any W_5d5d0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5d4 : bv 32 := 0x02813083.
Lemma F_5d5d4 : fetch_word AsanUbsan.M.loaded_segments (0x5d61c : word) = Some W_5d5d4.
Proof. vm_refl. Qed.
Lemma D_5d5d4 : decode_any W_5d5d4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5d8 : bv 32 := 0x02013403.
Lemma F_5d5d8 : fetch_word AsanUbsan.M.loaded_segments (0x5d620 : word) = Some W_5d5d8.
Proof. vm_refl. Qed.
Lemma D_5d5d8 : decode_any W_5d5d8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5dc : bv 32 := 0x01813483.
Lemma F_5d5dc : fetch_word AsanUbsan.M.loaded_segments (0x5d624 : word) = Some W_5d5dc.
Proof. vm_refl. Qed.
Lemma D_5d5dc : decode_any W_5d5dc = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5e0 : bv 32 := 0x01013903.
Lemma F_5d5e0 : fetch_word AsanUbsan.M.loaded_segments (0x5d628 : word) = Some W_5d5e0.
Proof. vm_refl. Qed.
Lemma D_5d5e0 : decode_any W_5d5e0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5e4 : bv 32 := 0x00813983.
Lemma F_5d5e4 : fetch_word AsanUbsan.M.loaded_segments (0x5d62c : word) = Some W_5d5e4.
Proof. vm_refl. Qed.
Lemma D_5d5e4 : decode_any W_5d5e4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5e8 : bv 32 := 0x00013a03.
Lemma F_5d5e8 : fetch_word AsanUbsan.M.loaded_segments (0x5d630 : word) = Some W_5d5e8.
Proof. vm_refl. Qed.
Lemma D_5d5e8 : decode_any W_5d5e8 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5ec : bv 32 := 0x03010113.
Lemma F_5d5ec : fetch_word AsanUbsan.M.loaded_segments (0x5d634 : word) = Some W_5d5ec.
Proof. vm_refl. Qed.
Lemma D_5d5ec : decode_any W_5d5ec = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5f0 : bv 32 := 0x39c0006f.
Lemma F_5d5f0 : fetch_word AsanUbsan.M.loaded_segments (0x5d638 : word) = Some W_5d5f0.
Proof. vm_refl. Qed.
Lemma D_5d5f0 : decode_any W_5d5f0 = Some (Jal 0 924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d644 : bv 32 := 0xfe010113.
Lemma F_5d644 : fetch_word AsanUbsan.M.loaded_segments (0x5d68c : word) = Some W_5d644.
Proof. vm_refl. Qed.
Lemma D_5d644 : decode_any W_5d644 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d648 : bv 32 := 0x00113c23.
Lemma F_5d648 : fetch_word AsanUbsan.M.loaded_segments (0x5d690 : word) = Some W_5d648.
Proof. vm_refl. Qed.
Lemma D_5d648 : decode_any W_5d648 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d64c : bv 32 := 0x00813823.
Lemma F_5d64c : fetch_word AsanUbsan.M.loaded_segments (0x5d694 : word) = Some W_5d64c.
Proof. vm_refl. Qed.
Lemma D_5d64c : decode_any W_5d64c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d650 : bv 32 := 0x00913423.
Lemma F_5d650 : fetch_word AsanUbsan.M.loaded_segments (0x5d698 : word) = Some W_5d650.
Proof. vm_refl. Qed.
Lemma D_5d650 : decode_any W_5d650 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d654 : bv 32 := 0x01213023.
Lemma F_5d654 : fetch_word AsanUbsan.M.loaded_segments (0x5d69c : word) = Some W_5d654.
Proof. vm_refl. Qed.
Lemma D_5d654 : decode_any W_5d654 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d658 : bv 32 := 0x26850413.
Lemma F_5d658 : fetch_word AsanUbsan.M.loaded_segments (0x5d6a0 : word) = Some W_5d658.
Proof. vm_refl. Qed.
Lemma D_5d658 : decode_any W_5d658 = Some (OpImm ALU_ADD 8 10 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d65c : bv 32 := 0x0ff00613.
Lemma F_5d65c : fetch_word AsanUbsan.M.loaded_segments (0x5d6a4 : word) = Some W_5d65c.
Proof. vm_refl. Qed.
Lemma D_5d65c : decode_any W_5d65c = Some (OpImm ALU_ADD 12 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d660 : bv 32 := 0xffc47693.
Lemma F_5d660 : fetch_word AsanUbsan.M.loaded_segments (0x5d6a8 : word) = Some W_5d660.
Proof. vm_refl. Qed.
Lemma D_5d660 : decode_any W_5d660 = Some (OpImm ALU_AND 13 8 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d664 : bv 32 := 0x00100713.
Lemma F_5d664 : fetch_word AsanUbsan.M.loaded_segments (0x5d6ac : word) = Some W_5d664.
Proof. vm_refl. Qed.
Lemma D_5d664 : decode_any W_5d664 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d668 : bv 32 := 0x1406a7af.
Lemma F_5d668 : fetch_word AsanUbsan.M.loaded_segments (0x5d6b0 : word) = Some W_5d668.
Proof. vm_refl. Qed.
Lemma D_5d668 : decode_any W_5d668 = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d66c : bv 32 := 0x00070813.
Lemma F_5d66c : fetch_word AsanUbsan.M.loaded_segments (0x5d6b4 : word) = Some W_5d66c.
Proof. vm_refl. Qed.
Lemma D_5d66c : decode_any W_5d66c = Some (OpImm ALU_ADD 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d670 : bv 32 := 0x0107c833.
Lemma F_5d670 : fetch_word AsanUbsan.M.loaded_segments (0x5d6b8 : word) = Some W_5d670.
Proof. vm_refl. Qed.
Lemma D_5d670 : decode_any W_5d670 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d674 : bv 32 := 0x00c87833.
Lemma F_5d674 : fetch_word AsanUbsan.M.loaded_segments (0x5d6bc : word) = Some W_5d674.
Proof. vm_refl. Qed.
Lemma D_5d674 : decode_any W_5d674 = Some (Op ALU_AND 16 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d678 : bv 32 := 0x0107c833.
Lemma F_5d678 : fetch_word AsanUbsan.M.loaded_segments (0x5d6c0 : word) = Some W_5d678.
Proof. vm_refl. Qed.
Lemma D_5d678 : decode_any W_5d678 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d67c : bv 32 := 0x1906a82f.
Lemma F_5d67c : fetch_word AsanUbsan.M.loaded_segments (0x5d6c4 : word) = Some W_5d67c.
Proof. vm_refl. Qed.
Lemma D_5d67c : decode_any W_5d67c = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d680 : bv 32 := 0xfe0814e3.
Lemma F_5d680 : fetch_word AsanUbsan.M.loaded_segments (0x5d6c8 : word) = Some W_5d680.
Proof. vm_refl. Qed.
Lemma D_5d680 : decode_any W_5d680 = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d684 : bv 32 := 0x0ff7f613.
Lemma F_5d684 : fetch_word AsanUbsan.M.loaded_segments (0x5d6cc : word) = Some W_5d684.
Proof. vm_refl. Qed.
Lemma D_5d684 : decode_any W_5d684 = Some (OpImm ALU_AND 12 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d688 : bv 32 := 0x08061663.
Lemma F_5d688 : fetch_word AsanUbsan.M.loaded_segments (0x5d6d0 : word) = Some W_5d688.
Proof. vm_refl. Qed.
Lemma D_5d688 : decode_any W_5d688 = Some (Branch BC_NE 12 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d68c : bv 32 := 0x03853703.
Lemma F_5d68c : fetch_word AsanUbsan.M.loaded_segments (0x5d6d4 : word) = Some W_5d68c.
Proof. vm_refl. Qed.
Lemma D_5d68c : decode_any W_5d68c = Some (Load SZ8 true 14 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d690 : bv 32 := 0x0a070263.
Lemma F_5d690 : fetch_word AsanUbsan.M.loaded_segments (0x5d6d8 : word) = Some W_5d690.
Proof. vm_refl. Qed.
Lemma D_5d690 : decode_any W_5d690 = Some (Branch BC_EQ 14 0 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d694 : bv 32 := 0x00000693.
Lemma F_5d694 : fetch_word AsanUbsan.M.loaded_segments (0x5d6dc : word) = Some W_5d694.
Proof. vm_refl. Qed.
Lemma D_5d694 : decode_any W_5d694 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d698 : bv 32 := 0x00853603.
Lemma F_5d698 : fetch_word AsanUbsan.M.loaded_segments (0x5d6e0 : word) = Some W_5d698.
Proof. vm_refl. Qed.
Lemma D_5d698 : decode_any W_5d698 = Some (Load SZ8 true 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d69c : bv 32 := 0x00371713.
Lemma F_5d69c : fetch_word AsanUbsan.M.loaded_segments (0x5d6e4 : word) = Some W_5d69c.
Proof. vm_refl. Qed.
Lemma D_5d69c : decode_any W_5d69c = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6a0 : bv 32 := 0x00e60733.
Lemma F_5d6a0 : fetch_word AsanUbsan.M.loaded_segments (0x5d6e8 : word) = Some W_5d6a0.
Proof. vm_refl. Qed.
Lemma D_5d6a0 : decode_any W_5d6a0 = Some (Op ALU_ADD 14 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6a4 : bv 32 := 0x00c0006f.
Lemma F_5d6a4 : fetch_word AsanUbsan.M.loaded_segments (0x5d6ec : word) = Some W_5d6a4.
Proof. vm_refl. Qed.
Lemma D_5d6a4 : decode_any W_5d6a4 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6a8 : bv 32 := 0x00860613.
Lemma F_5d6a8 : fetch_word AsanUbsan.M.loaded_segments (0x5d6f0 : word) = Some W_5d6a8.
Proof. vm_refl. Qed.
Lemma D_5d6a8 : decode_any W_5d6a8 = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6ac : bv 32 := 0x02e60863.
Lemma F_5d6ac : fetch_word AsanUbsan.M.loaded_segments (0x5d6f4 : word) = Some W_5d6ac.
Proof. vm_refl. Qed.
Lemma D_5d6ac : decode_any W_5d6ac = Some (Branch BC_EQ 12 14 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6b0 : bv 32 := 0x00063783.
Lemma F_5d6b0 : fetch_word AsanUbsan.M.loaded_segments (0x5d6f8 : word) = Some W_5d6b0.
Proof. vm_refl. Qed.
Lemma D_5d6b0 : decode_any W_5d6b0 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6b4 : bv 32 := 0x40f588b3.
Lemma F_5d6b4 : fetch_word AsanUbsan.M.loaded_segments (0x5d6fc : word) = Some W_5d6b4.
Proof. vm_refl. Qed.
Lemma D_5d6b4 : decode_any W_5d6b4 = Some (Op ALU_SUB 17 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6b8 : bv 32 := 0x40d582b3.
Lemma F_5d6b8 : fetch_word AsanUbsan.M.loaded_segments (0x5d700 : word) = Some W_5d6b8.
Proof. vm_refl. Qed.
Lemma D_5d6b8 : decode_any W_5d6b8 = Some (Op ALU_SUB 5 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6bc : bv 32 := 0x00078813.
Lemma F_5d6bc : fetch_word AsanUbsan.M.loaded_segments (0x5d704 : word) = Some W_5d6bc.
Proof. vm_refl. Qed.
Lemma D_5d6bc : decode_any W_5d6bc = Some (OpImm ALU_ADD 16 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6c0 : bv 32 := 0x0058e863.
Lemma F_5d6c0 : fetch_word AsanUbsan.M.loaded_segments (0x5d708 : word) = Some W_5d6c0.
Proof. vm_refl. Qed.
Lemma D_5d6c0 : decode_any W_5d6c0 = Some (Branch BC_LTU 17 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6c4 : bv 32 := 0x00068813.
Lemma F_5d6c4 : fetch_word AsanUbsan.M.loaded_segments (0x5d70c : word) = Some W_5d6c4.
Proof. vm_refl. Qed.
Lemma D_5d6c4 : decode_any W_5d6c4 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6c8 : bv 32 := 0xfef5e0e3.
Lemma F_5d6c8 : fetch_word AsanUbsan.M.loaded_segments (0x5d710 : word) = Some W_5d6c8.
Proof. vm_refl. Qed.
Lemma D_5d6c8 : decode_any W_5d6c8 = Some (Branch BC_LTU 11 15 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6cc : bv 32 := 0x0080006f.
Lemma F_5d6cc : fetch_word AsanUbsan.M.loaded_segments (0x5d714 : word) = Some W_5d6cc.
Proof. vm_refl. Qed.
Lemma D_5d6cc : decode_any W_5d6cc = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6d0 : bv 32 := 0xfcf5ece3.
Lemma F_5d6d0 : fetch_word AsanUbsan.M.loaded_segments (0x5d718 : word) = Some W_5d6d0.
Proof. vm_refl. Qed.
Lemma D_5d6d0 : decode_any W_5d6d0 = Some (Branch BC_LTU 11 15 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6d4 : bv 32 := 0x00080693.
Lemma F_5d6d4 : fetch_word AsanUbsan.M.loaded_segments (0x5d71c : word) = Some W_5d6d4.
Proof. vm_refl. Qed.
Lemma D_5d6d4 : decode_any W_5d6d4 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6d8 : bv 32 := 0xfd1ff06f.
Lemma F_5d6d8 : fetch_word AsanUbsan.M.loaded_segments (0x5d720 : word) = Some W_5d6d8.
Proof. vm_refl. Qed.
Lemma D_5d6d8 : decode_any W_5d6d8 = Some (Jal 0 2097104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6dc : bv 32 := 0x04068c63.
Lemma F_5d6dc : fetch_word AsanUbsan.M.loaded_segments (0x5d724 : word) = Some W_5d6dc.
Proof. vm_refl. Qed.
Lemma D_5d6dc : decode_any W_5d6dc = Some (Branch BC_EQ 13 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6e0 : bv 32 := 0x0006b703.
Lemma F_5d6e0 : fetch_word AsanUbsan.M.loaded_segments (0x5d728 : word) = Some W_5d6e0.
Proof. vm_refl. Qed.
Lemma D_5d6e0 : decode_any W_5d6e0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6e4 : bv 32 := 0x06e6ea63.
Lemma F_5d6e4 : fetch_word AsanUbsan.M.loaded_segments (0x5d72c : word) = Some W_5d6e4.
Proof. vm_refl. Qed.
Lemma D_5d6e4 : decode_any W_5d6e4 = Some (Branch BC_LTU 13 14 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6e8 : bv 32 := 0x0086b603.
Lemma F_5d6e8 : fetch_word AsanUbsan.M.loaded_segments (0x5d730 : word) = Some W_5d6e8.
Proof. vm_refl. Qed.
Lemma D_5d6e8 : decode_any W_5d6e8 = Some (Load SZ8 true 12 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6ec : bv 32 := 0x00e60733.
Lemma F_5d6ec : fetch_word AsanUbsan.M.loaded_segments (0x5d734 : word) = Some W_5d6ec.
Proof. vm_refl. Qed.
Lemma D_5d6ec : decode_any W_5d6ec = Some (Op ALU_ADD 14 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6f0 : bv 32 := 0x08e6f063.
Lemma F_5d6f0 : fetch_word AsanUbsan.M.loaded_segments (0x5d738 : word) = Some W_5d6f0.
Proof. vm_refl. Qed.
Lemma D_5d6f0 : decode_any W_5d6f0 = Some (Branch BC_GEU 13 14 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6f4 : bv 32 := 0x08d5ea63.
Lemma F_5d6f4 : fetch_word AsanUbsan.M.loaded_segments (0x5d73c : word) = Some W_5d6f4.
Proof. vm_refl. Qed.
Lemma D_5d6f4 : decode_any W_5d6f4 = Some (Branch BC_LTU 11 13 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6f8 : bv 32 := 0x02e5fe63.
Lemma F_5d6f8 : fetch_word AsanUbsan.M.loaded_segments (0x5d740 : word) = Some W_5d6f8.
Proof. vm_refl. Qed.
Lemma D_5d6f8 : decode_any W_5d6f8 = Some (Branch BC_GEU 11 14 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6fc : bv 32 := 0x00053503.
Lemma F_5d6fc : fetch_word AsanUbsan.M.loaded_segments (0x5d744 : word) = Some W_5d6fc.
Proof. vm_refl. Qed.
Lemma D_5d6fc : decode_any W_5d6fc = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d700 : bv 32 := 0xfff50593.
Lemma F_5d700 : fetch_word AsanUbsan.M.loaded_segments (0x5d748 : word) = Some W_5d700.
Proof. vm_refl. Qed.
Lemma D_5d700 : decode_any W_5d700 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d704 : bv 32 := 0x00d5f5b3.
Lemma F_5d704 : fetch_word AsanUbsan.M.loaded_segments (0x5d74c : word) = Some W_5d704.
Proof. vm_refl. Qed.
Lemma D_5d704 : decode_any W_5d704 = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d708 : bv 32 := 0x08059e63.
Lemma F_5d708 : fetch_word AsanUbsan.M.loaded_segments (0x5d750 : word) = Some W_5d708.
Proof. vm_refl. Qed.
Lemma D_5d708 : decode_any W_5d708 = Some (Branch BC_NE 11 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d70c : bv 32 := 0x00d50533.
Lemma F_5d70c : fetch_word AsanUbsan.M.loaded_segments (0x5d754 : word) = Some W_5d70c.
Proof. vm_refl. Qed.
Lemma D_5d70c : decode_any W_5d70c = Some (Op ALU_ADD 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d710 : bv 32 := 0x0280006f.
Lemma F_5d710 : fetch_word AsanUbsan.M.loaded_segments (0x5d758 : word) = Some W_5d710.
Proof. vm_refl. Qed.
Lemma D_5d710 : decode_any W_5d710 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d738 : bv 32 := 0x0310000f.
Lemma F_5d738 : fetch_word AsanUbsan.M.loaded_segments (0x5d780 : word) = Some W_5d738.
Proof. vm_refl. Qed.
Lemma D_5d738 : decode_any W_5d738 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d73c : bv 32 := 0x00040023.
Lemma F_5d73c : fetch_word AsanUbsan.M.loaded_segments (0x5d784 : word) = Some W_5d73c.
Proof. vm_refl. Qed.
Lemma D_5d73c : decode_any W_5d73c = Some (Store SZ1 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d740 : bv 32 := 0x01813083.
Lemma F_5d740 : fetch_word AsanUbsan.M.loaded_segments (0x5d788 : word) = Some W_5d740.
Proof. vm_refl. Qed.
Lemma D_5d740 : decode_any W_5d740 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d744 : bv 32 := 0x01013403.
Lemma F_5d744 : fetch_word AsanUbsan.M.loaded_segments (0x5d78c : word) = Some W_5d744.
Proof. vm_refl. Qed.
Lemma D_5d744 : decode_any W_5d744 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d748 : bv 32 := 0x00813483.
Lemma F_5d748 : fetch_word AsanUbsan.M.loaded_segments (0x5d790 : word) = Some W_5d748.
Proof. vm_refl. Qed.
Lemma D_5d748 : decode_any W_5d748 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d74c : bv 32 := 0x00013903.
Lemma F_5d74c : fetch_word AsanUbsan.M.loaded_segments (0x5d794 : word) = Some W_5d74c.
Proof. vm_refl. Qed.
Lemma D_5d74c : decode_any W_5d74c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d750 : bv 32 := 0x02010113.
Lemma F_5d750 : fetch_word AsanUbsan.M.loaded_segments (0x5d798 : word) = Some W_5d750.
Proof. vm_refl. Qed.
Lemma D_5d750 : decode_any W_5d750 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d754 : bv 32 := 0x00008067.
Lemma F_5d754 : fetch_word AsanUbsan.M.loaded_segments (0x5d79c : word) = Some W_5d754.
Proof. vm_refl. Qed.
Lemma D_5d754 : decode_any W_5d754 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7c4 : bv 32 := 0xfd010113.
Lemma F_5d7c4 : fetch_word AsanUbsan.M.loaded_segments (0x5d80c : word) = Some W_5d7c4.
Proof. vm_refl. Qed.
Lemma D_5d7c4 : decode_any W_5d7c4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7c8 : bv 32 := 0x02113423.
Lemma F_5d7c8 : fetch_word AsanUbsan.M.loaded_segments (0x5d810 : word) = Some W_5d7c8.
Proof. vm_refl. Qed.
Lemma D_5d7c8 : decode_any W_5d7c8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7cc : bv 32 := 0x02813023.
Lemma F_5d7cc : fetch_word AsanUbsan.M.loaded_segments (0x5d814 : word) = Some W_5d7cc.
Proof. vm_refl. Qed.
Lemma D_5d7cc : decode_any W_5d7cc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7d0 : bv 32 := 0x00913c23.
Lemma F_5d7d0 : fetch_word AsanUbsan.M.loaded_segments (0x5d818 : word) = Some W_5d7d0.
Proof. vm_refl. Qed.
Lemma D_5d7d0 : decode_any W_5d7d0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7d4 : bv 32 := 0x01213823.
Lemma F_5d7d4 : fetch_word AsanUbsan.M.loaded_segments (0x5d81c : word) = Some W_5d7d4.
Proof. vm_refl. Qed.
Lemma D_5d7d4 : decode_any W_5d7d4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7d8 : bv 32 := 0x01313423.
Lemma F_5d7d8 : fetch_word AsanUbsan.M.loaded_segments (0x5d820 : word) = Some W_5d7d8.
Proof. vm_refl. Qed.
Lemma D_5d7d8 : decode_any W_5d7d8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7dc : bv 32 := 0x01413023.
Lemma F_5d7dc : fetch_word AsanUbsan.M.loaded_segments (0x5d824 : word) = Some W_5d7dc.
Proof. vm_refl. Qed.
Lemma D_5d7dc : decode_any W_5d7dc = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7e0 : bv 32 := 0x08060463.
Lemma F_5d7e0 : fetch_word AsanUbsan.M.loaded_segments (0x5d828 : word) = Some W_5d7e0.
Proof. vm_refl. Qed.
Lemma D_5d7e0 : decode_any W_5d7e0 = Some (Branch BC_EQ 12 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7e4 : bv 32 := 0x02000713.
Lemma F_5d7e4 : fetch_word AsanUbsan.M.loaded_segments (0x5d82c : word) = Some W_5d7e4.
Proof. vm_refl. Qed.
Lemma D_5d7e4 : decode_any W_5d7e4 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7e8 : bv 32 := 0x0ae67063.
Lemma F_5d7e8 : fetch_word AsanUbsan.M.loaded_segments (0x5d830 : word) = Some W_5d7e8.
Proof. vm_refl. Qed.
Lemma D_5d7e8 : decode_any W_5d7e8 = Some (Branch BC_GEU 12 14 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7ec : bv 32 := 0x05000713.
Lemma F_5d7ec : fetch_word AsanUbsan.M.loaded_segments (0x5d834 : word) = Some W_5d7ec.
Proof. vm_refl. Qed.
Lemma D_5d7ec : decode_any W_5d7ec = Some (OpImm ALU_ADD 14 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7f0 : bv 32 := 0x02e60433.
Lemma F_5d7f0 : fetch_word AsanUbsan.M.loaded_segments (0x5d838 : word) = Some W_5d7f0.
Proof. vm_refl. Qed.
Lemma D_5d7f0 : decode_any W_5d7f0 = Some (Mul M_MUL 8 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7f4 : bv 32 := 0x00850433.
Lemma F_5d7f4 : fetch_word AsanUbsan.M.loaded_segments (0x5d83c : word) = Some W_5d7f4.
Proof. vm_refl. Qed.
Lemma D_5d7f4 : decode_any W_5d7f4 = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7f8 : bv 32 := 0x00442783.
Lemma F_5d7f8 : fetch_word AsanUbsan.M.loaded_segments (0x5d840 : word) = Some W_5d7f8.
Proof. vm_refl. Qed.
Lemma D_5d7f8 : decode_any W_5d7f8 = Some (Load SZ4 true 15 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7fc : bv 32 := 0x0a078863.
Lemma F_5d7fc : fetch_word AsanUbsan.M.loaded_segments (0x5d844 : word) = Some W_5d7fc.
Proof. vm_refl. Qed.
Lemma D_5d7fc : decode_any W_5d7fc = Some (Branch BC_EQ 15 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d800 : bv 32 := 0x00042703.
Lemma F_5d800 : fetch_word AsanUbsan.M.loaded_segments (0x5d848 : word) = Some W_5d800.
Proof. vm_refl. Qed.
Lemma D_5d800 : decode_any W_5d800 = Some (Load SZ4 true 14 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d804 : bv 32 := 0x14f70863.
Lemma F_5d804 : fetch_word AsanUbsan.M.loaded_segments (0x5d84c : word) = Some W_5d804.
Proof. vm_refl. Qed.
Lemma D_5d804 : decode_any W_5d804 = Some (Branch BC_EQ 14 15 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d808 : bv 32 := 0x0205b583.
Lemma F_5d808 : fetch_word AsanUbsan.M.loaded_segments (0x5d850 : word) = Some W_5d808.
Proof. vm_refl. Qed.
Lemma D_5d808 : decode_any W_5d808 = Some (Load SZ8 true 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d80c : bv 32 := 0x02061613.
Lemma F_5d80c : fetch_word AsanUbsan.M.loaded_segments (0x5d854 : word) = Some W_5d80c.
Proof. vm_refl. Qed.
Lemma D_5d80c : decode_any W_5d80c = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d810 : bv 32 := 0x40c686b3.
Lemma F_5d810 : fetch_word AsanUbsan.M.loaded_segments (0x5d858 : word) = Some W_5d810.
Proof. vm_refl. Qed.
Lemma D_5d810 : decode_any W_5d810 = Some (Op ALU_SUB 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d814 : bv 32 := 0x02071613.
Lemma F_5d814 : fetch_word AsanUbsan.M.loaded_segments (0x5d85c : word) = Some W_5d814.
Proof. vm_refl. Qed.
Lemma D_5d814 : decode_any W_5d814 = Some (ShiftImm ALU_SLL 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d818 : bv 32 := 0x00170713.
Lemma F_5d818 : fetch_word AsanUbsan.M.loaded_segments (0x5d860 : word) = Some W_5d818.
Proof. vm_refl. Qed.
Lemma D_5d818 : decode_any W_5d818 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d81c : bv 32 := 0x40b686b3.
Lemma F_5d81c : fetch_word AsanUbsan.M.loaded_segments (0x5d864 : word) = Some W_5d81c.
Proof. vm_refl. Qed.
Lemma D_5d81c : decode_any W_5d81c = Some (Op ALU_SUB 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d820 : bv 32 := 0x00843583.
Lemma F_5d820 : fetch_word AsanUbsan.M.loaded_segments (0x5d868 : word) = Some W_5d820.
Proof. vm_refl. Qed.
Lemma D_5d820 : decode_any W_5d820 = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d824 : bv 32 := 0x7ff50513.
Lemma F_5d824 : fetch_word AsanUbsan.M.loaded_segments (0x5d86c : word) = Some W_5d824.
Proof. vm_refl. Qed.
Lemma D_5d824 : decode_any W_5d824 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d828 : bv 32 := 0x01e65613.
Lemma F_5d828 : fetch_word AsanUbsan.M.loaded_segments (0x5d870 : word) = Some W_5d828.
Proof. vm_refl. Qed.
Lemma D_5d828 : decode_any W_5d828 = Some (ShiftImm ALU_SRL 12 12 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d82c : bv 32 := 0x21150513.
Lemma F_5d82c : fetch_word AsanUbsan.M.loaded_segments (0x5d874 : word) = Some W_5d82c.
Proof. vm_refl. Qed.
Lemma D_5d82c : decode_any W_5d82c = Some (OpImm ALU_ADD 10 10 529, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d830 : bv 32 := 0x00c40633.
Lemma F_5d830 : fetch_word AsanUbsan.M.loaded_segments (0x5d878 : word) = Some W_5d830.
Proof. vm_refl. Qed.
Lemma D_5d830 : decode_any W_5d830 = Some (Op ALU_ADD 12 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d834 : bv 32 := 0x0046d693.
Lemma F_5d834 : fetch_word AsanUbsan.M.loaded_segments (0x5d87c : word) = Some W_5d834.
Proof. vm_refl. Qed.
Lemma D_5d834 : decode_any W_5d834 = Some (ShiftImm ALU_SRL 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d838 : bv 32 := 0x00e42023.
Lemma F_5d838 : fetch_word AsanUbsan.M.loaded_segments (0x5d880 : word) = Some W_5d838.
Proof. vm_refl. Qed.
Lemma D_5d838 : decode_any W_5d838 = Some (Store SZ4 8 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d83c : bv 32 := 0x00d62823.
Lemma F_5d83c : fetch_word AsanUbsan.M.loaded_segments (0x5d884 : word) = Some W_5d83c.
Proof. vm_refl. Qed.
Lemma D_5d83c : decode_any W_5d83c = Some (Store SZ4 12 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d840 : bv 32 := 0x40b005b3.
Lemma F_5d840 : fetch_word AsanUbsan.M.loaded_segments (0x5d888 : word) = Some W_5d840.
Proof. vm_refl. Qed.
Lemma D_5d840 : decode_any W_5d840 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d844 : bv 32 := 0x00b5302f.
Lemma F_5d844 : fetch_word AsanUbsan.M.loaded_segments (0x5d88c : word) = Some W_5d844.
Proof. vm_refl. Qed.
Lemma D_5d844 : decode_any W_5d844 = Some (Amo AMO_ADD AD false false 0 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d848 : bv 32 := 0x02813083.
Lemma F_5d848 : fetch_word AsanUbsan.M.loaded_segments (0x5d890 : word) = Some W_5d848.
Proof. vm_refl. Qed.
Lemma D_5d848 : decode_any W_5d848 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d84c : bv 32 := 0x02013403.
Lemma F_5d84c : fetch_word AsanUbsan.M.loaded_segments (0x5d894 : word) = Some W_5d84c.
Proof. vm_refl. Qed.
Lemma D_5d84c : decode_any W_5d84c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d850 : bv 32 := 0x01813483.
Lemma F_5d850 : fetch_word AsanUbsan.M.loaded_segments (0x5d898 : word) = Some W_5d850.
Proof. vm_refl. Qed.
Lemma D_5d850 : decode_any W_5d850 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d854 : bv 32 := 0x01013903.
Lemma F_5d854 : fetch_word AsanUbsan.M.loaded_segments (0x5d89c : word) = Some W_5d854.
Proof. vm_refl. Qed.
Lemma D_5d854 : decode_any W_5d854 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d858 : bv 32 := 0x00813983.
Lemma F_5d858 : fetch_word AsanUbsan.M.loaded_segments (0x5d8a0 : word) = Some W_5d858.
Proof. vm_refl. Qed.
Lemma D_5d858 : decode_any W_5d858 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d85c : bv 32 := 0x00013a03.
Lemma F_5d85c : fetch_word AsanUbsan.M.loaded_segments (0x5d8a4 : word) = Some W_5d85c.
Proof. vm_refl. Qed.
Lemma D_5d85c : decode_any W_5d85c = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d860 : bv 32 := 0x03010113.
Lemma F_5d860 : fetch_word AsanUbsan.M.loaded_segments (0x5d8a8 : word) = Some W_5d860.
Proof. vm_refl. Qed.
Lemma D_5d860 : decode_any W_5d860 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d864 : bv 32 := 0x00008067.
Lemma F_5d864 : fetch_word AsanUbsan.M.loaded_segments (0x5d8ac : word) = Some W_5d864.
Proof. vm_refl. Qed.
Lemma D_5d864 : decode_any W_5d864 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d954 : bv 32 := 0x00050493.
Lemma F_5d954 : fetch_word AsanUbsan.M.loaded_segments (0x5d99c : word) = Some W_5d954.
Proof. vm_refl. Qed.
Lemma D_5d954 : decode_any W_5d954 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d958 : bv 32 := 0x00058913.
Lemma F_5d958 : fetch_word AsanUbsan.M.loaded_segments (0x5d9a0 : word) = Some W_5d958.
Proof. vm_refl. Qed.
Lemma D_5d958 : decode_any W_5d958 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d95c : bv 32 := 0x00040593.
Lemma F_5d95c : fetch_word AsanUbsan.M.loaded_segments (0x5d9a4 : word) = Some W_5d95c.
Proof. vm_refl. Qed.
Lemma D_5d95c : decode_any W_5d95c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d960 : bv 32 := 0x00060993.
Lemma F_5d960 : fetch_word AsanUbsan.M.loaded_segments (0x5d9a8 : word) = Some W_5d960.
Proof. vm_refl. Qed.
Lemma D_5d960 : decode_any W_5d960 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d964 : bv 32 := 0x00090613.
Lemma F_5d964 : fetch_word AsanUbsan.M.loaded_segments (0x5d9ac : word) = Some W_5d964.
Proof. vm_refl. Qed.
Lemma D_5d964 : decode_any W_5d964 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d968 : bv 32 := 0x00068a13.
Lemma F_5d968 : fetch_word AsanUbsan.M.loaded_segments (0x5d9b0 : word) = Some W_5d968.
Proof. vm_refl. Qed.
Lemma D_5d968 : decode_any W_5d968 = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d96c : bv 32 := 0x00098693.
Lemma F_5d96c : fetch_word AsanUbsan.M.loaded_segments (0x5d9b4 : word) = Some W_5d96c.
Proof. vm_refl. Qed.
Lemma D_5d96c : decode_any W_5d96c = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d970 : bv 32 := 0x1e8000ef.
Lemma F_5d970 : fetch_word AsanUbsan.M.loaded_segments (0x5d9b8 : word) = Some W_5d970.
Proof. vm_refl. Qed.
Lemma D_5d970 : decode_any W_5d970 = Some (Jal 1 488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d974 : bv 32 := 0x00090593.
Lemma F_5d974 : fetch_word AsanUbsan.M.loaded_segments (0x5d9bc : word) = Some W_5d974.
Proof. vm_refl. Qed.
Lemma D_5d974 : decode_any W_5d974 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d978 : bv 32 := 0x000a0693.
Lemma F_5d978 : fetch_word AsanUbsan.M.loaded_segments (0x5d9c0 : word) = Some W_5d978.
Proof. vm_refl. Qed.
Lemma D_5d978 : decode_any W_5d978 = Some (OpImm ALU_ADD 13 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d97c : bv 32 := 0x00048513.
Lemma F_5d97c : fetch_word AsanUbsan.M.loaded_segments (0x5d9c4 : word) = Some W_5d97c.
Proof. vm_refl. Qed.
Lemma D_5d97c : decode_any W_5d97c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d980 : bv 32 := 0x00098613.
Lemma F_5d980 : fetch_word AsanUbsan.M.loaded_segments (0x5d9c8 : word) = Some W_5d980.
Proof. vm_refl. Qed.
Lemma D_5d980 : decode_any W_5d980 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d984 : bv 32 := 0x00042703.
Lemma F_5d984 : fetch_word AsanUbsan.M.loaded_segments (0x5d9cc : word) = Some W_5d984.
Proof. vm_refl. Qed.
Lemma D_5d984 : decode_any W_5d984 = Some (Load SZ4 true 14 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d988 : bv 32 := 0xe81ff06f.
Lemma F_5d988 : fetch_word AsanUbsan.M.loaded_segments (0x5d9d0 : word) = Some W_5d988.
Proof. vm_refl. Qed.
Lemma D_5d988 : decode_any W_5d988 = Some (Jal 0 2096768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d98c : bv 32 := 0xfe010113.
Lemma F_5d98c : fetch_word AsanUbsan.M.loaded_segments (0x5d9d4 : word) = Some W_5d98c.
Proof. vm_refl. Qed.
Lemma D_5d98c : decode_any W_5d98c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d990 : bv 32 := 0x00113c23.
Lemma F_5d990 : fetch_word AsanUbsan.M.loaded_segments (0x5d9d8 : word) = Some W_5d990.
Proof. vm_refl. Qed.
Lemma D_5d990 : decode_any W_5d990 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d994 : bv 32 := 0x00813823.
Lemma F_5d994 : fetch_word AsanUbsan.M.loaded_segments (0x5d9dc : word) = Some W_5d994.
Proof. vm_refl. Qed.
Lemma D_5d994 : decode_any W_5d994 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d998 : bv 32 := 0x00913423.
Lemma F_5d998 : fetch_word AsanUbsan.M.loaded_segments (0x5d9e0 : word) = Some W_5d998.
Proof. vm_refl. Qed.
Lemma D_5d998 : decode_any W_5d998 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d99c : bv 32 := 0x01213023.
Lemma F_5d99c : fetch_word AsanUbsan.M.loaded_segments (0x5d9e4 : word) = Some W_5d99c.
Proof. vm_refl. Qed.
Lemma D_5d99c : decode_any W_5d99c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9a0 : bv 32 := 0x00053703.
Lemma F_5d9a0 : fetch_word AsanUbsan.M.loaded_segments (0x5d9e8 : word) = Some W_5d9a0.
Proof. vm_refl. Qed.
Lemma D_5d9a0 : decode_any W_5d9a0 = Some (Load SZ8 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9a4 : bv 32 := 0xfff70693.
Lemma F_5d9a4 : fetch_word AsanUbsan.M.loaded_segments (0x5d9ec : word) = Some W_5d9a4.
Proof. vm_refl. Qed.
Lemma D_5d9a4 : decode_any W_5d9a4 = Some (OpImm ALU_ADD 13 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9a8 : bv 32 := 0x00c6f6b3.
Lemma F_5d9a8 : fetch_word AsanUbsan.M.loaded_segments (0x5d9f0 : word) = Some W_5d9a8.
Proof. vm_refl. Qed.
Lemma D_5d9a8 : decode_any W_5d9a8 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9ac : bv 32 := 0x12069263.
Lemma F_5d9ac : fetch_word AsanUbsan.M.loaded_segments (0x5d9f4 : word) = Some W_5d9ac.
Proof. vm_refl. Qed.
Lemma D_5d9ac : decode_any W_5d9ac = Some (Branch BC_NE 13 0 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9b0 : bv 32 := 0x26850693.
Lemma F_5d9b0 : fetch_word AsanUbsan.M.loaded_segments (0x5d9f8 : word) = Some W_5d9b0.
Proof. vm_refl. Qed.
Lemma D_5d9b0 : decode_any W_5d9b0 = Some (OpImm ALU_ADD 13 10 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9b4 : bv 32 := 0x0ff00793.
Lemma F_5d9b4 : fetch_word AsanUbsan.M.loaded_segments (0x5d9fc : word) = Some W_5d9b4.
Proof. vm_refl. Qed.
Lemma D_5d9b4 : decode_any W_5d9b4 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9b8 : bv 32 := 0xffc6f813.
Lemma F_5d9b8 : fetch_word AsanUbsan.M.loaded_segments (0x5da00 : word) = Some W_5d9b8.
Proof. vm_refl. Qed.
Lemma D_5d9b8 : decode_any W_5d9b8 = Some (OpImm ALU_AND 16 13 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9bc : bv 32 := 0x00100893.
Lemma F_5d9bc : fetch_word AsanUbsan.M.loaded_segments (0x5da04 : word) = Some W_5d9bc.
Proof. vm_refl. Qed.
Lemma D_5d9bc : decode_any W_5d9bc = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9c0 : bv 32 := 0x140822af.
Lemma F_5d9c0 : fetch_word AsanUbsan.M.loaded_segments (0x5da08 : word) = Some W_5d9c0.
Proof. vm_refl. Qed.
Lemma D_5d9c0 : decode_any W_5d9c0 = Some (Lr AW true false 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9c4 : bv 32 := 0x00088313.
Lemma F_5d9c4 : fetch_word AsanUbsan.M.loaded_segments (0x5da0c : word) = Some W_5d9c4.
Proof. vm_refl. Qed.
Lemma D_5d9c4 : decode_any W_5d9c4 = Some (OpImm ALU_ADD 6 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9c8 : bv 32 := 0x0062c333.
Lemma F_5d9c8 : fetch_word AsanUbsan.M.loaded_segments (0x5da10 : word) = Some W_5d9c8.
Proof. vm_refl. Qed.
Lemma D_5d9c8 : decode_any W_5d9c8 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9cc : bv 32 := 0x00f37333.
Lemma F_5d9cc : fetch_word AsanUbsan.M.loaded_segments (0x5da14 : word) = Some W_5d9cc.
Proof. vm_refl. Qed.
Lemma D_5d9cc : decode_any W_5d9cc = Some (Op ALU_AND 6 6 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9d0 : bv 32 := 0x0062c333.
Lemma F_5d9d0 : fetch_word AsanUbsan.M.loaded_segments (0x5da18 : word) = Some W_5d9d0.
Proof. vm_refl. Qed.
Lemma D_5d9d0 : decode_any W_5d9d0 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9d4 : bv 32 := 0x1868232f.
Lemma F_5d9d4 : fetch_word AsanUbsan.M.loaded_segments (0x5da1c : word) = Some W_5d9d4.
Proof. vm_refl. Qed.
Lemma D_5d9d4 : decode_any W_5d9d4 = Some (Sc AW false false 6 16 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9d8 : bv 32 := 0xfe0314e3.
Lemma F_5d9d8 : fetch_word AsanUbsan.M.loaded_segments (0x5da20 : word) = Some W_5d9d8.
Proof. vm_refl. Qed.
Lemma D_5d9d8 : decode_any W_5d9d8 = Some (Branch BC_NE 6 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9dc : bv 32 := 0x0ff2f793.
Lemma F_5d9dc : fetch_word AsanUbsan.M.loaded_segments (0x5da24 : word) = Some W_5d9dc.
Proof. vm_refl. Qed.
Lemma D_5d9dc : decode_any W_5d9dc = Some (OpImm ALU_AND 15 5 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9e0 : bv 32 := 0x40e60433.
Lemma F_5d9e0 : fetch_word AsanUbsan.M.loaded_segments (0x5da28 : word) = Some W_5d9e0.
Proof. vm_refl. Qed.
Lemma D_5d9e0 : decode_any W_5d9e0 = Some (Op ALU_SUB 8 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9e4 : bv 32 := 0x10079663.
Lemma F_5d9e4 : fetch_word AsanUbsan.M.loaded_segments (0x5da2c : word) = Some W_5d9e4.
Proof. vm_refl. Qed.
Lemma D_5d9e4 : decode_any W_5d9e4 = Some (Branch BC_NE 15 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9e8 : bv 32 := 0x01843683.
Lemma F_5d9e8 : fetch_word AsanUbsan.M.loaded_segments (0x5da30 : word) = Some W_5d9e8.
Proof. vm_refl. Qed.
Lemma D_5d9e8 : decode_any W_5d9e8 = Some (Load SZ8 true 13 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9ec : bv 32 := 0x00853783.
Lemma F_5d9ec : fetch_word AsanUbsan.M.loaded_segments (0x5da34 : word) = Some W_5d9ec.
Proof. vm_refl. Qed.
Lemma D_5d9ec : decode_any W_5d9ec = Some (Load SZ8 true 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9f0 : bv 32 := 0x00369613.
Lemma F_5d9f0 : fetch_word AsanUbsan.M.loaded_segments (0x5da38 : word) = Some W_5d9f0.
Proof. vm_refl. Qed.
Lemma D_5d9f0 : decode_any W_5d9f0 = Some (ShiftImm ALU_SLL 12 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9f4 : bv 32 := 0x00c78633.
Lemma F_5d9f4 : fetch_word AsanUbsan.M.loaded_segments (0x5da3c : word) = Some W_5d9f4.
Proof. vm_refl. Qed.
Lemma D_5d9f4 : decode_any W_5d9f4 = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9f8 : bv 32 := 0x00063703.
Lemma F_5d9f8 : fetch_word AsanUbsan.M.loaded_segments (0x5da40 : word) = Some W_5d9f8.
Proof. vm_refl. Qed.
Lemma D_5d9f8 : decode_any W_5d9f8 = Some (Load SZ8 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9fc : bv 32 := 0x12871263.
Lemma F_5d9fc : fetch_word AsanUbsan.M.loaded_segments (0x5da44 : word) = Some W_5d9fc.
Proof. vm_refl. Qed.
Lemma D_5d9fc : decode_any W_5d9fc = Some (Branch BC_NE 14 8 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da00 : bv 32 := 0x03853703.
Lemma F_5da00 : fetch_word AsanUbsan.M.loaded_segments (0x5da48 : word) = Some W_5da00.
Proof. vm_refl. Qed.
Lemma D_5da00 : decode_any W_5da00 = Some (Load SZ8 true 14 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da04 : bv 32 := 0x12e6fe63.
Lemma F_5da04 : fetch_word AsanUbsan.M.loaded_segments (0x5da4c : word) = Some W_5da04.
Proof. vm_refl. Qed.
Lemma D_5da04 : decode_any W_5da04 = Some (Branch BC_GEU 13 14 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da08 : bv 32 := 0x00371813.
Lemma F_5da08 : fetch_word AsanUbsan.M.loaded_segments (0x5da50 : word) = Some W_5da08.
Proof. vm_refl. Qed.
Lemma D_5da08 : decode_any W_5da08 = Some (ShiftImm ALU_SLL 16 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da0c : bv 32 := 0x00843883.
Lemma F_5da0c : fetch_word AsanUbsan.M.loaded_segments (0x5da54 : word) = Some W_5da0c.
Proof. vm_refl. Qed.
Lemma D_5da0c : decode_any W_5da0c = Some (Load SZ8 true 17 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da10 : bv 32 := 0x00f807b3.
Lemma F_5da10 : fetch_word AsanUbsan.M.loaded_segments (0x5da58 : word) = Some W_5da10.
Proof. vm_refl. Qed.
Lemma D_5da10 : decode_any W_5da10 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da14 : bv 32 := 0x05053803.
Lemma F_5da14 : fetch_word AsanUbsan.M.loaded_segments (0x5da5c : word) = Some W_5da14.
Proof. vm_refl. Qed.
Lemma D_5da14 : decode_any W_5da14 = Some (Load SZ8 true 16 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da18 : bv 32 := 0x05853283.
Lemma F_5da18 : fetch_word AsanUbsan.M.loaded_segments (0x5da60 : word) = Some W_5da18.
Proof. vm_refl. Qed.
Lemma D_5da18 : decode_any W_5da18 = Some (Load SZ8 true 5 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da1c : bv 32 := 0xfff70713.
Lemma F_5da1c : fetch_word AsanUbsan.M.loaded_segments (0x5da64 : word) = Some W_5da1c.
Proof. vm_refl. Qed.
Lemma D_5da1c : decode_any W_5da1c = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da20 : bv 32 := 0xff87b783.
Lemma F_5da20 : fetch_word AsanUbsan.M.loaded_segments (0x5da68 : word) = Some W_5da20.
Proof. vm_refl. Qed.
Lemma D_5da20 : decode_any W_5da20 = Some (Load SZ8 true 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da24 : bv 32 := 0x00180813.
Lemma F_5da24 : fetch_word AsanUbsan.M.loaded_segments (0x5da6c : word) = Some W_5da24.
Proof. vm_refl. Qed.
Lemma D_5da24 : decode_any W_5da24 = Some (OpImm ALU_ADD 16 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da28 : bv 32 := 0x411282b3.
Lemma F_5da28 : fetch_word AsanUbsan.M.loaded_segments (0x5da70 : word) = Some W_5da28.
Proof. vm_refl. Qed.
Lemma D_5da28 : decode_any W_5da28 = Some (Op ALU_SUB 5 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da2c : bv 32 := 0x02e53c23.
Lemma F_5da2c : fetch_word AsanUbsan.M.loaded_segments (0x5da74 : word) = Some W_5da2c.
Proof. vm_refl. Qed.
Lemma D_5da2c : decode_any W_5da2c = Some (Store SZ8 10 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da30 : bv 32 := 0x04050023.
Lemma F_5da30 : fetch_word AsanUbsan.M.loaded_segments (0x5da78 : word) = Some W_5da30.
Proof. vm_refl. Qed.
Lemma D_5da30 : decode_any W_5da30 = Some (Store SZ1 10 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da34 : bv 32 := 0x05053823.
Lemma F_5da34 : fetch_word AsanUbsan.M.loaded_segments (0x5da7c : word) = Some W_5da34.
Proof. vm_refl. Qed.
Lemma D_5da34 : decode_any W_5da34 = Some (Store SZ8 10 16 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da38 : bv 32 := 0x04553c23.
Lemma F_5da38 : fetch_word AsanUbsan.M.loaded_segments (0x5da80 : word) = Some W_5da38.
Proof. vm_refl. Qed.
Lemma D_5da38 : decode_any W_5da38 = Some (Store SZ8 10 5 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da3c : bv 32 := 0x01058713.
Lemma F_5da3c : fetch_word AsanUbsan.M.loaded_segments (0x5da84 : word) = Some W_5da3c.
Proof. vm_refl. Qed.
Lemma D_5da3c : decode_any W_5da3c = Some (OpImm ALU_ADD 14 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da40 : bv 32 := 0x41100833.
Lemma F_5da40 : fetch_word AsanUbsan.M.loaded_segments (0x5da88 : word) = Some W_5da40.
Proof. vm_refl. Qed.
Lemma D_5da40 : decode_any W_5da40 = Some (Op ALU_SUB 16 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da44 : bv 32 := 0x00f63023.
Lemma F_5da44 : fetch_word AsanUbsan.M.loaded_segments (0x5da8c : word) = Some W_5da44.
Proof. vm_refl. Qed.
Lemma D_5da44 : decode_any W_5da44 = Some (Store SZ8 12 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da48 : bv 32 := 0x00d7bc23.
Lemma F_5da48 : fetch_word AsanUbsan.M.loaded_segments (0x5da90 : word) = Some W_5da48.
Proof. vm_refl. Qed.
Lemma D_5da48 : decode_any W_5da48 = Some (Store SZ8 15 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da4c : bv 32 := 0x0107302f.
Lemma F_5da4c : fetch_word AsanUbsan.M.loaded_segments (0x5da94 : word) = Some W_5da4c.
Proof. vm_refl. Qed.
Lemma D_5da4c : decode_any W_5da4c = Some (Amo AMO_ADD AD false false 0 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da50 : bv 32 := 0x00843603.
Lemma F_5da50 : fetch_word AsanUbsan.M.loaded_segments (0x5da98 : word) = Some W_5da50.
Proof. vm_refl. Qed.
Lemma D_5da50 : decode_any W_5da50 = Some (Load SZ8 true 12 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da54 : bv 32 := 0x01858593.
Lemma F_5da54 : fetch_word AsanUbsan.M.loaded_segments (0x5da9c : word) = Some W_5da54.
Proof. vm_refl. Qed.
Lemma D_5da54 : decode_any W_5da54 = Some (OpImm ALU_ADD 11 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da58 : bv 32 := 0x40c00633.
Lemma F_5da58 : fetch_word AsanUbsan.M.loaded_segments (0x5daa0 : word) = Some W_5da58.
Proof. vm_refl. Qed.
Lemma D_5da58 : decode_any W_5da58 = Some (Op ALU_SUB 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da5c : bv 32 := 0x00c5b02f.
Lemma F_5da5c : fetch_word AsanUbsan.M.loaded_segments (0x5daa4 : word) = Some W_5da5c.
Proof. vm_refl. Qed.
Lemma D_5da5c : decode_any W_5da5c = Some (Amo AMO_ADD AD false false 0 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da60 : bv 32 := 0x0310000f.
Lemma F_5da60 : fetch_word AsanUbsan.M.loaded_segments (0x5daa8 : word) = Some W_5da60.
Proof. vm_refl. Qed.
Lemma D_5da60 : decode_any W_5da60 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da64 : bv 32 := 0x26050423.
Lemma F_5da64 : fetch_word AsanUbsan.M.loaded_segments (0x5daac : word) = Some W_5da64.
Proof. vm_refl. Qed.
Lemma D_5da64 : decode_any W_5da64 = Some (Store SZ1 10 0 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da68 : bv 32 := 0x00043483.
Lemma F_5da68 : fetch_word AsanUbsan.M.loaded_segments (0x5dab0 : word) = Some W_5da68.
Proof. vm_refl. Qed.
Lemma D_5da68 : decode_any W_5da68 = Some (Load SZ8 true 9 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da6c : bv 32 := 0x00843903.
Lemma F_5da6c : fetch_word AsanUbsan.M.loaded_segments (0x5dab4 : word) = Some W_5da6c.
Proof. vm_refl. Qed.
Lemma D_5da6c : decode_any W_5da6c = Some (Load SZ8 true 18 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da70 : bv 32 := 0x00048513.
Lemma F_5da70 : fetch_word AsanUbsan.M.loaded_segments (0x5dab8 : word) = Some W_5da70.
Proof. vm_refl. Qed.
Lemma D_5da70 : decode_any W_5da70 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da74 : bv 32 := 0x00090593.
Lemma F_5da74 : fetch_word AsanUbsan.M.loaded_segments (0x5dabc : word) = Some W_5da74.
Proof. vm_refl. Qed.
Lemma D_5da74 : decode_any W_5da74 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da78 : bv 32 := 0x00000613.
Lemma F_5da78 : fetch_word AsanUbsan.M.loaded_segments (0x5dac0 : word) = Some W_5da78.
Proof. vm_refl. Qed.
Lemma D_5da78 : decode_any W_5da78 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da7c : bv 32 := 0x6f1250ef.
Lemma F_5da7c : fetch_word AsanUbsan.M.loaded_segments (0x5dac4 : word) = Some W_5da7c.
Proof. vm_refl. Qed.
Lemma D_5da7c : decode_any W_5da7c = Some (Jal 1 155376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da80 : bv 32 := 0x00048513.
Lemma F_5da80 : fetch_word AsanUbsan.M.loaded_segments (0x5dac8 : word) = Some W_5da80.
Proof. vm_refl. Qed.
Lemma D_5da80 : decode_any W_5da80 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da84 : bv 32 := 0x00090593.
Lemma F_5da84 : fetch_word AsanUbsan.M.loaded_segments (0x5dacc : word) = Some W_5da84.
Proof. vm_refl. Qed.
Lemma D_5da84 : decode_any W_5da84 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da88 : bv 32 := 0x0cd240ef.
Lemma F_5da88 : fetch_word AsanUbsan.M.loaded_segments (0x5dad0 : word) = Some W_5da88.
Proof. vm_refl. Qed.
Lemma D_5da88 : decode_any W_5da88 = Some (Jal 1 149708, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da8c : bv 32 := 0x6592d0ef.
Lemma F_5da8c : fetch_word AsanUbsan.M.loaded_segments (0x5dad4 : word) = Some W_5da8c.
Proof. vm_refl. Qed.
Lemma D_5da8c : decode_any W_5da8c = Some (Jal 1 187992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da90 : bv 32 := 0x06053683.
Lemma F_5da90 : fetch_word AsanUbsan.M.loaded_segments (0x5dad8 : word) = Some W_5da90.
Proof. vm_refl. Qed.
Lemma D_5da90 : decode_any W_5da90 = Some (Load SZ8 true 13 10 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da94 : bv 32 := 0x05853703.
Lemma F_5da94 : fetch_word AsanUbsan.M.loaded_segments (0x5dadc : word) = Some W_5da94.
Proof. vm_refl. Qed.
Lemma D_5da94 : decode_any W_5da94 = Some (Load SZ8 true 14 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da98 : bv 32 := 0x00043603.
Lemma F_5da98 : fetch_word AsanUbsan.M.loaded_segments (0x5dae0 : word) = Some W_5da98.
Proof. vm_refl. Qed.
Lemma D_5da98 : decode_any W_5da98 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da9c : bv 32 := 0x00843583.
Lemma F_5da9c : fetch_word AsanUbsan.M.loaded_segments (0x5dae4 : word) = Some W_5da9c.
Proof. vm_refl. Qed.
Lemma D_5da9c : decode_any W_5da9c = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5daa0 : bv 32 := 0x012686b3.
Lemma F_5daa0 : fetch_word AsanUbsan.M.loaded_segments (0x5dae8 : word) = Some W_5daa0.
Proof. vm_refl. Qed.
Lemma D_5daa0 : decode_any W_5daa0 = Some (Op ALU_ADD 13 13 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5daa4 : bv 32 := 0x00170713.
Lemma F_5daa4 : fetch_word AsanUbsan.M.loaded_segments (0x5daec : word) = Some W_5daa4.
Proof. vm_refl. Qed.
Lemma D_5daa4 : decode_any W_5daa4 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5daa8 : bv 32 := 0x04e53c23.
Lemma F_5daa8 : fetch_word AsanUbsan.M.loaded_segments (0x5daf0 : word) = Some W_5daa8.
Proof. vm_refl. Qed.
Lemma D_5daa8 : decode_any W_5daa8 = Some (Store SZ8 10 14 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5daac : bv 32 := 0x06d53023.
Lemma F_5daac : fetch_word AsanUbsan.M.loaded_segments (0x5daf4 : word) = Some W_5daac.
Proof. vm_refl. Qed.
Lemma D_5daac : decode_any W_5daac = Some (Store SZ8 10 13 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dab0 : bv 32 := 0x00060513.
Lemma F_5dab0 : fetch_word AsanUbsan.M.loaded_segments (0x5daf8 : word) = Some W_5dab0.
Proof. vm_refl. Qed.
Lemma D_5dab0 : decode_any W_5dab0 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dab4 : bv 32 := 0x00000613.
Lemma F_5dab4 : fetch_word AsanUbsan.M.loaded_segments (0x5dafc : word) = Some W_5dab4.
Proof. vm_refl. Qed.
Lemma D_5dab4 : decode_any W_5dab4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dab8 : bv 32 := 0x01813083.
Lemma F_5dab8 : fetch_word AsanUbsan.M.loaded_segments (0x5db00 : word) = Some W_5dab8.
Proof. vm_refl. Qed.
Lemma D_5dab8 : decode_any W_5dab8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dabc : bv 32 := 0x01013403.
Lemma F_5dabc : fetch_word AsanUbsan.M.loaded_segments (0x5db04 : word) = Some W_5dabc.
Proof. vm_refl. Qed.
Lemma D_5dabc : decode_any W_5dabc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dac0 : bv 32 := 0x00813483.
Lemma F_5dac0 : fetch_word AsanUbsan.M.loaded_segments (0x5db08 : word) = Some W_5dac0.
Proof. vm_refl. Qed.
Lemma D_5dac0 : decode_any W_5dac0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dac4 : bv 32 := 0x00013903.
Lemma F_5dac4 : fetch_word AsanUbsan.M.loaded_segments (0x5db0c : word) = Some W_5dac4.
Proof. vm_refl. Qed.
Lemma D_5dac4 : decode_any W_5dac4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dac8 : bv 32 := 0x02010113.
Lemma F_5dac8 : fetch_word AsanUbsan.M.loaded_segments (0x5db10 : word) = Some W_5dac8.
Proof. vm_refl. Qed.
Lemma D_5dac8 : decode_any W_5dac8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dacc : bv 32 := 0x0353806f.
Lemma F_5dacc : fetch_word AsanUbsan.M.loaded_segments (0x5db14 : word) = Some W_5dacc.
Proof. vm_refl. Qed.
Lemma D_5dacc : decode_any W_5dacc = Some (Jal 0 231476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db58 : bv 32 := 0xfc010113.
Lemma F_5db58 : fetch_word AsanUbsan.M.loaded_segments (0x5dba0 : word) = Some W_5db58.
Proof. vm_refl. Qed.
Lemma D_5db58 : decode_any W_5db58 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db5c : bv 32 := 0x02113c23.
Lemma F_5db5c : fetch_word AsanUbsan.M.loaded_segments (0x5dba4 : word) = Some W_5db5c.
Proof. vm_refl. Qed.
Lemma D_5db5c : decode_any W_5db5c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db60 : bv 32 := 0x02013423.
Lemma F_5db60 : fetch_word AsanUbsan.M.loaded_segments (0x5dba8 : word) = Some W_5db60.
Proof. vm_refl. Qed.
Lemma D_5db60 : decode_any W_5db60 = Some (Store SZ8 2 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db64 : bv 32 := 0x02013823.
Lemma F_5db64 : fetch_word AsanUbsan.M.loaded_segments (0x5dbac : word) = Some W_5db64.
Proof. vm_refl. Qed.
Lemma D_5db64 : decode_any W_5db64 = Some (Store SZ8 2 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db68 : bv 32 := 0x0005a803.
Lemma F_5db68 : fetch_word AsanUbsan.M.loaded_segments (0x5dbb0 : word) = Some W_5db68.
Proof. vm_refl. Qed.
Lemma D_5db68 : decode_any W_5db68 = Some (Load SZ4 true 16 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db6c : bv 32 := 0x0045e783.
Lemma F_5db6c : fetch_word AsanUbsan.M.loaded_segments (0x5dbb4 : word) = Some W_5db6c.
Proof. vm_refl. Qed.
Lemma D_5db6c : decode_any W_5db6c = Some (Load SZ4 false 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db70 : bv 32 := 0x00c13423.
Lemma F_5db70 : fetch_word AsanUbsan.M.loaded_segments (0x5dbb8 : word) = Some W_5db70.
Proof. vm_refl. Qed.
Lemma D_5db70 : decode_any W_5db70 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db74 : bv 32 := 0x00013823.
Lemma F_5db74 : fetch_word AsanUbsan.M.loaded_segments (0x5dbbc : word) = Some W_5db74.
Proof. vm_refl. Qed.
Lemma D_5db74 : decode_any W_5db74 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db78 : bv 32 := 0x00013c23.
Lemma F_5db78 : fetch_word AsanUbsan.M.loaded_segments (0x5dbc0 : word) = Some W_5db78.
Proof. vm_refl. Qed.
Lemma D_5db78 : decode_any W_5db78 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db7c : bv 32 := 0x02013023.
Lemma F_5db7c : fetch_word AsanUbsan.M.loaded_segments (0x5dbc4 : word) = Some W_5db7c.
Proof. vm_refl. Qed.
Lemma D_5db7c : decode_any W_5db7c = Some (Store SZ8 2 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db80 : bv 32 := 0x0017d793.
Lemma F_5db80 : fetch_word AsanUbsan.M.loaded_segments (0x5dbc8 : word) = Some W_5db80.
Proof. vm_refl. Qed.
Lemma D_5db80 : decode_any W_5db80 = Some (ShiftImm ALU_SRL 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db84 : bv 32 := 0x02081713.
Lemma F_5db84 : fetch_word AsanUbsan.M.loaded_segments (0x5dbcc : word) = Some W_5db84.
Proof. vm_refl. Qed.
Lemma D_5db84 : decode_any W_5db84 = Some (ShiftImm ALU_SLL 14 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db88 : bv 32 := 0x02075713.
Lemma F_5db88 : fetch_word AsanUbsan.M.loaded_segments (0x5dbd0 : word) = Some W_5db88.
Proof. vm_refl. Qed.
Lemma D_5db88 : decode_any W_5db88 = Some (ShiftImm ALU_SRL 14 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db8c : bv 32 := 0x04f86663.
Lemma F_5db8c : fetch_word AsanUbsan.M.loaded_segments (0x5dbd4 : word) = Some W_5db8c.
Proof. vm_refl. Qed.
Lemma D_5db8c : decode_any W_5db8c = Some (Branch BC_LTU 16 15 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db90 : bv 32 := 0x40f70733.
Lemma F_5db90 : fetch_word AsanUbsan.M.loaded_segments (0x5dbd8 : word) = Some W_5db90.
Proof. vm_refl. Qed.
Lemma D_5db90 : decode_any W_5db90 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db94 : bv 32 := 0x7ff50513.
Lemma F_5db94 : fetch_word AsanUbsan.M.loaded_segments (0x5dbdc : word) = Some W_5db94.
Proof. vm_refl. Qed.
Lemma D_5db94 : decode_any W_5db94 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db98 : bv 32 := 0x00e5a023.
Lemma F_5db98 : fetch_word AsanUbsan.M.loaded_segments (0x5dbe0 : word) = Some W_5db98.
Proof. vm_refl. Qed.
Lemma D_5db98 : decode_any W_5db98 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db9c : bv 32 := 0x20150813.
Lemma F_5db9c : fetch_word AsanUbsan.M.loaded_segments (0x5dbe4 : word) = Some W_5db9c.
Proof. vm_refl. Qed.
Lemma D_5db9c : decode_any W_5db9c = Some (OpImm ALU_ADD 16 10 513, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dba0 : bv 32 := 0x00271713.
Lemma F_5dba0 : fetch_word AsanUbsan.M.loaded_segments (0x5dbe8 : word) = Some W_5dba0.
Proof. vm_refl. Qed.
Lemma D_5dba0 : decode_any W_5dba0 = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dba4 : bv 32 := 0x00e585b3.
Lemma F_5dba4 : fetch_word AsanUbsan.M.loaded_segments (0x5dbec : word) = Some W_5dba4.
Proof. vm_refl. Qed.
Lemma D_5dba4 : decode_any W_5dba4 = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dba8 : bv 32 := 0x01058713.
Lemma F_5dba8 : fetch_word AsanUbsan.M.loaded_segments (0x5dbf0 : word) = Some W_5dba8.
Proof. vm_refl. Qed.
Lemma D_5dba8 : decode_any W_5dba8 = Some (OpImm ALU_ADD 14 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbac : bv 32 := 0x00810593.
Lemma F_5dbac : fetch_word AsanUbsan.M.loaded_segments (0x5dbf4 : word) = Some W_5dbac.
Proof. vm_refl. Qed.
Lemma D_5dbac : decode_any W_5dbac = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbb0 : bv 32 := 0x00060513.
Lemma F_5dbb0 : fetch_word AsanUbsan.M.loaded_segments (0x5dbf8 : word) = Some W_5dbb0.
Proof. vm_refl. Qed.
Lemma D_5dbb0 : decode_any W_5dbb0 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbb4 : bv 32 := 0x00080613.
Lemma F_5dbb4 : fetch_word AsanUbsan.M.loaded_segments (0x5dbfc : word) = Some W_5dbb4.
Proof. vm_refl. Qed.
Lemma D_5dbb4 : decode_any W_5dbb4 = Some (OpImm ALU_ADD 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbb8 : bv 32 := 0x144000ef.
Lemma F_5dbb8 : fetch_word AsanUbsan.M.loaded_segments (0x5dc00 : word) = Some W_5dbb8.
Proof. vm_refl. Qed.
Lemma D_5dbb8 : decode_any W_5dbb8 = Some (Jal 1 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbbc : bv 32 := 0x02013503.
Lemma F_5dbbc : fetch_word AsanUbsan.M.loaded_segments (0x5dc04 : word) = Some W_5dbbc.
Proof. vm_refl. Qed.
Lemma D_5dbbc : decode_any W_5dbbc = Some (Load SZ8 true 10 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbc0 : bv 32 := 0x02813583.
Lemma F_5dbc0 : fetch_word AsanUbsan.M.loaded_segments (0x5dc08 : word) = Some W_5dbc0.
Proof. vm_refl. Qed.
Lemma D_5dbc0 : decode_any W_5dbc0 = Some (Load SZ8 true 11 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbc4 : bv 32 := 0x00000613.
Lemma F_5dbc4 : fetch_word AsanUbsan.M.loaded_segments (0x5dc0c : word) = Some W_5dbc4.
Proof. vm_refl. Qed.
Lemma D_5dbc4 : decode_any W_5dbc4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbc8 : bv 32 := 0x738380ef.
Lemma F_5dbc8 : fetch_word AsanUbsan.M.loaded_segments (0x5dc10 : word) = Some W_5dbc8.
Proof. vm_refl. Qed.
Lemma D_5dbc8 : decode_any W_5dbc8 = Some (Jal 1 231224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbcc : bv 32 := 0x03813083.
Lemma F_5dbcc : fetch_word AsanUbsan.M.loaded_segments (0x5dc14 : word) = Some W_5dbcc.
Proof. vm_refl. Qed.
Lemma D_5dbcc : decode_any W_5dbcc = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbd0 : bv 32 := 0x04010113.
Lemma F_5dbd0 : fetch_word AsanUbsan.M.loaded_segments (0x5dc18 : word) = Some W_5dbd0.
Proof. vm_refl. Qed.
Lemma D_5dbd0 : decode_any W_5dbd0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbd4 : bv 32 := 0x00008067.
Lemma F_5dbd4 : fetch_word AsanUbsan.M.loaded_segments (0x5dc1c : word) = Some W_5dbd4.
Proof. vm_refl. Qed.
Lemma D_5dbd4 : decode_any W_5dbd4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dcfc : bv 32 := 0xf8010113.
Lemma F_5dcfc : fetch_word AsanUbsan.M.loaded_segments (0x5dd44 : word) = Some W_5dcfc.
Proof. vm_refl. Qed.
Lemma D_5dcfc : decode_any W_5dcfc = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd00 : bv 32 := 0x06113c23.
Lemma F_5dd00 : fetch_word AsanUbsan.M.loaded_segments (0x5dd48 : word) = Some W_5dd00.
Proof. vm_refl. Qed.
Lemma D_5dd00 : decode_any W_5dd00 = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd04 : bv 32 := 0x06813823.
Lemma F_5dd04 : fetch_word AsanUbsan.M.loaded_segments (0x5dd4c : word) = Some W_5dd04.
Proof. vm_refl. Qed.
Lemma D_5dd04 : decode_any W_5dd04 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd08 : bv 32 := 0x06913423.
Lemma F_5dd08 : fetch_word AsanUbsan.M.loaded_segments (0x5dd50 : word) = Some W_5dd08.
Proof. vm_refl. Qed.
Lemma D_5dd08 : decode_any W_5dd08 = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd0c : bv 32 := 0x07213023.
Lemma F_5dd0c : fetch_word AsanUbsan.M.loaded_segments (0x5dd54 : word) = Some W_5dd0c.
Proof. vm_refl. Qed.
Lemma D_5dd0c : decode_any W_5dd0c = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd10 : bv 32 := 0x05313c23.
Lemma F_5dd10 : fetch_word AsanUbsan.M.loaded_segments (0x5dd58 : word) = Some W_5dd10.
Proof. vm_refl. Qed.
Lemma D_5dd10 : decode_any W_5dd10 = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd14 : bv 32 := 0x05413823.
Lemma F_5dd14 : fetch_word AsanUbsan.M.loaded_segments (0x5dd5c : word) = Some W_5dd14.
Proof. vm_refl. Qed.
Lemma D_5dd14 : decode_any W_5dd14 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd18 : bv 32 := 0x05513423.
Lemma F_5dd18 : fetch_word AsanUbsan.M.loaded_segments (0x5dd60 : word) = Some W_5dd18.
Proof. vm_refl. Qed.
Lemma D_5dd18 : decode_any W_5dd18 = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd1c : bv 32 := 0x05613023.
Lemma F_5dd1c : fetch_word AsanUbsan.M.loaded_segments (0x5dd64 : word) = Some W_5dd1c.
Proof. vm_refl. Qed.
Lemma D_5dd1c : decode_any W_5dd1c = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd20 : bv 32 := 0x03713c23.
Lemma F_5dd20 : fetch_word AsanUbsan.M.loaded_segments (0x5dd68 : word) = Some W_5dd20.
Proof. vm_refl. Qed.
Lemma D_5dd20 : decode_any W_5dd20 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd24 : bv 32 := 0x03813823.
Lemma F_5dd24 : fetch_word AsanUbsan.M.loaded_segments (0x5dd6c : word) = Some W_5dd24.
Proof. vm_refl. Qed.
Lemma D_5dd24 : decode_any W_5dd24 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd28 : bv 32 := 0x03913423.
Lemma F_5dd28 : fetch_word AsanUbsan.M.loaded_segments (0x5dd70 : word) = Some W_5dd28.
Proof. vm_refl. Qed.
Lemma D_5dd28 : decode_any W_5dd28 = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd2c : bv 32 := 0x03a13023.
Lemma F_5dd2c : fetch_word AsanUbsan.M.loaded_segments (0x5dd74 : word) = Some W_5dd2c.
Proof. vm_refl. Qed.
Lemma D_5dd2c : decode_any W_5dd2c = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd30 : bv 32 := 0x01b13c23.
Lemma F_5dd30 : fetch_word AsanUbsan.M.loaded_segments (0x5dd78 : word) = Some W_5dd30.
Proof. vm_refl. Qed.
Lemma D_5dd30 : decode_any W_5dd30 = Some (Store SZ8 2 27 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd34 : bv 32 := 0x00078a93.
Lemma F_5dd34 : fetch_word AsanUbsan.M.loaded_segments (0x5dd7c : word) = Some W_5dd34.
Proof. vm_refl. Qed.
Lemma D_5dd34 : decode_any W_5dd34 = Some (OpImm ALU_ADD 21 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd38 : bv 32 := 0x00070b13.
Lemma F_5dd38 : fetch_word AsanUbsan.M.loaded_segments (0x5dd80 : word) = Some W_5dd38.
Proof. vm_refl. Qed.
Lemma D_5dd38 : decode_any W_5dd38 = Some (OpImm ALU_ADD 22 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd3c : bv 32 := 0x00068913.
Lemma F_5dd3c : fetch_word AsanUbsan.M.loaded_segments (0x5dd84 : word) = Some W_5dd3c.
Proof. vm_refl. Qed.
Lemma D_5dd3c : decode_any W_5dd3c = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd40 : bv 32 := 0x00058993.
Lemma F_5dd40 : fetch_word AsanUbsan.M.loaded_segments (0x5dd88 : word) = Some W_5dd40.
Proof. vm_refl. Qed.
Lemma D_5dd40 : decode_any W_5dd40 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd44 : bv 32 := 0x00050a13.
Lemma F_5dd44 : fetch_word AsanUbsan.M.loaded_segments (0x5dd8c : word) = Some W_5dd44.
Proof. vm_refl. Qed.
Lemma D_5dd44 : decode_any W_5dd44 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd48 : bv 32 := 0x00000513.
Lemma F_5dd48 : fetch_word AsanUbsan.M.loaded_segments (0x5dd90 : word) = Some W_5dd48.
Proof. vm_refl. Qed.
Lemma D_5dd48 : decode_any W_5dd48 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd4c : bv 32 := 0x00100d93.
Lemma F_5dd4c : fetch_word AsanUbsan.M.loaded_segments (0x5dd94 : word) = Some W_5dd4c.
Proof. vm_refl. Qed.
Lemma D_5dd4c : decode_any W_5dd4c = Some (OpImm ALU_ADD 27 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd50 : bv 32 := 0x020a3603.
Lemma F_5dd50 : fetch_word AsanUbsan.M.loaded_segments (0x5dd98 : word) = Some W_5dd50.
Proof. vm_refl. Qed.
Lemma D_5dd50 : decode_any W_5dd50 = Some (Load SZ8 true 12 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd54 : bv 32 := 0x030a3403.
Lemma F_5dd54 : fetch_word AsanUbsan.M.loaded_segments (0x5dd9c : word) = Some W_5dd54.
Proof. vm_refl. Qed.
Lemma D_5dd54 : decode_any W_5dd54 = Some (Load SZ8 true 8 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd58 : bv 32 := 0x00769693.
Lemma F_5dd58 : fetch_word AsanUbsan.M.loaded_segments (0x5dda0 : word) = Some W_5dd58.
Proof. vm_refl. Qed.
Lemma D_5dd58 : decode_any W_5dd58 = Some (ShiftImm ALU_SLL 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd5c : bv 32 := 0x02091713.
Lemma F_5dd5c : fetch_word AsanUbsan.M.loaded_segments (0x5dda4 : word) = Some W_5dd5c.
Proof. vm_refl. Qed.
Lemma D_5dd5c : decode_any W_5dd5c = Some (ShiftImm ALU_SLL 14 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd60 : bv 32 := 0x00700793.
Lemma F_5dd60 : fetch_word AsanUbsan.M.loaded_segments (0x5dda8 : word) = Some W_5dd60.
Proof. vm_refl. Qed.
Lemma D_5dd60 : decode_any W_5dd60 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd64 : bv 32 := 0xfff00593.
Lemma F_5dd64 : fetch_word AsanUbsan.M.loaded_segments (0x5ddac : word) = Some W_5dd64.
Proof. vm_refl. Qed.
Lemma D_5dd64 : decode_any W_5dd64 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd68 : bv 32 := 0x03dd9c13.
Lemma F_5dd68 : fetch_word AsanUbsan.M.loaded_segments (0x5ddb0 : word) = Some W_5dd68.
Proof. vm_refl. Qed.
Lemma D_5dd68 : decode_any W_5dd68 = Some (ShiftImm ALU_SLL 24 27 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd6c : bv 32 := 0x01d79793.
Lemma F_5dd6c : fetch_word AsanUbsan.M.loaded_segments (0x5ddb4 : word) = Some W_5dd6c.
Proof. vm_refl. Qed.
Lemma D_5dd6c : decode_any W_5dd6c = Some (ShiftImm ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd70 : bv 32 := 0x028d9b93.
Lemma F_5dd70 : fetch_word AsanUbsan.M.loaded_segments (0x5ddb8 : word) = Some W_5dd70.
Proof. vm_refl. Qed.
Lemma D_5dd70 : decode_any W_5dd70 = Some (ShiftImm ALU_SLL 23 27 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd74 : bv 32 := 0x001b8813.
Lemma F_5dd74 : fetch_word AsanUbsan.M.loaded_segments (0x5ddbc : word) = Some W_5dd74.
Proof. vm_refl. Qed.
Lemma D_5dd74 : decode_any W_5dd74 = Some (OpImm ALU_ADD 16 23 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd78 : bv 32 := 0x01481813.
Lemma F_5dd78 : fetch_word AsanUbsan.M.loaded_segments (0x5ddc0 : word) = Some W_5dd78.
Proof. vm_refl. Qed.
Lemma D_5dd78 : decode_any W_5dd78 = Some (ShiftImm ALU_SLL 16 16 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd7c : bv 32 := 0x00d40433.
Lemma F_5dd7c : fetch_word AsanUbsan.M.loaded_segments (0x5ddc4 : word) = Some W_5dd7c.
Proof. vm_refl. Qed.
Lemma D_5dd7c : decode_any W_5dd7c = Some (Op ALU_ADD 8 8 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd80 : bv 32 := 0x00e60633.
Lemma F_5dd80 : fetch_word AsanUbsan.M.loaded_segments (0x5ddc8 : word) = Some W_5dd80.
Proof. vm_refl. Qed.
Lemma D_5dd80 : decode_any W_5dd80 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd84 : bv 32 := 0xfff80d13.
Lemma F_5dd84 : fetch_word AsanUbsan.M.loaded_segments (0x5ddcc : word) = Some W_5dd84.
Proof. vm_refl. Qed.
Lemma D_5dd84 : decode_any W_5dd84 = Some (OpImm ALU_ADD 26 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd88 : bv 32 := 0x00f60cb3.
Lemma F_5dd88 : fetch_word AsanUbsan.M.loaded_segments (0x5ddd0 : word) = Some W_5dd88.
Proof. vm_refl. Qed.
Lemma D_5dd88 : decode_any W_5dd88 = Some (Op ALU_ADD 25 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd8c : bv 32 := 0x00043683.
Lemma F_5dd8c : fetch_word AsanUbsan.M.loaded_segments (0x5ddd4 : word) = Some W_5dd8c.
Proof. vm_refl. Qed.
Lemma D_5dd8c : decode_any W_5dd8c = Some (Load SZ8 true 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd90 : bv 32 := 0x00840713.
Lemma F_5dd90 : fetch_word AsanUbsan.M.loaded_segments (0x5ddd8 : word) = Some W_5dd90.
Proof. vm_refl. Qed.
Lemma D_5dd90 : decode_any W_5dd90 = Some (OpImm ALU_ADD 14 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd94 : bv 32 := 0x00e13823.
Lemma F_5dd94 : fetch_word AsanUbsan.M.loaded_segments (0x5dddc : word) = Some W_5dd94.
Proof. vm_refl. Qed.
Lemma D_5dd94 : decode_any W_5dd94 = Some (Store SZ8 2 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd98 : bv 32 := 0x03cd9d93.
Lemma F_5dd98 : fetch_word AsanUbsan.M.loaded_segments (0x5dde0 : word) = Some W_5dd98.
Proof. vm_refl. Qed.
Lemma D_5dd98 : decode_any W_5dd98 = Some (ShiftImm ALU_SLL 27 27 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd9c : bv 32 := 0x5dc00893.
Lemma F_5dd9c : fetch_word AsanUbsan.M.loaded_segments (0x5dde4 : word) = Some W_5dd9c.
Proof. vm_refl. Qed.
Lemma D_5dd9c : decode_any W_5dd9c = Some (OpImm ALU_ADD 17 0 1500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dda0 : bv 32 := 0x03d59493.
Lemma F_5dda0 : fetch_word AsanUbsan.M.loaded_segments (0x5dde8 : word) = Some W_5dda0.
Proof. vm_refl. Qed.
Lemma D_5dda0 : decode_any W_5dda0 = Some (ShiftImm ALU_SLL 9 11 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dda4 : bv 32 := 0xfff48493.
Lemma F_5dda4 : fetch_word AsanUbsan.M.loaded_segments (0x5ddec : word) = Some W_5dda4.
Proof. vm_refl. Qed.
Lemma D_5dda4 : decode_any W_5dda4 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dda8 : bv 32 := 0x01a6f733.
Lemma F_5dda8 : fetch_word AsanUbsan.M.loaded_segments (0x5ddf0 : word) = Some W_5dda8.
Proof. vm_refl. Qed.
Lemma D_5dda8 : decode_any W_5dda8 = Some (Op ALU_AND 14 13 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddac : bv 32 := 0x02071663.
Lemma F_5ddac : fetch_word AsanUbsan.M.loaded_segments (0x5ddf4 : word) = Some W_5ddac.
Proof. vm_refl. Qed.
Lemma D_5ddac : decode_any W_5ddac = Some (Branch BC_NE 14 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddb0 : bv 32 := 0x01b6e733.
Lemma F_5ddb0 : fetch_word AsanUbsan.M.loaded_segments (0x5ddf8 : word) = Some W_5ddb0.
Proof. vm_refl. Qed.
Lemma D_5ddb0 : decode_any W_5ddb0 = Some (Op ALU_OR 14 13 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddb4 : bv 32 := 0x00e5f7b3.
Lemma F_5ddb4 : fetch_word AsanUbsan.M.loaded_segments (0x5ddfc : word) = Some W_5ddb4.
Proof. vm_refl. Qed.
Lemma D_5ddb4 : decode_any W_5ddb4 = Some (Op ALU_AND 15 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddb8 : bv 32 := 0x1604372f.
Lemma F_5ddb8 : fetch_word AsanUbsan.M.loaded_segments (0x5de00 : word) = Some W_5ddb8.
Proof. vm_refl. Qed.
Lemma D_5ddb8 : decode_any W_5ddb8 = Some (Lr AD true true 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddbc : bv 32 := 0x00d71663.
Lemma F_5ddbc : fetch_word AsanUbsan.M.loaded_segments (0x5de04 : word) = Some W_5ddbc.
Proof. vm_refl. Qed.
Lemma D_5ddbc : decode_any W_5ddbc = Some (Branch BC_NE 14 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddc0 : bv 32 := 0x1af4382f.
Lemma F_5ddc0 : fetch_word AsanUbsan.M.loaded_segments (0x5de08 : word) = Some W_5ddc0.
Proof. vm_refl. Qed.
Lemma D_5ddc0 : decode_any W_5ddc0 = Some (Sc AD false true 16 8 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddc4 : bv 32 := 0xfe081ae3.
Lemma F_5ddc4 : fetch_word AsanUbsan.M.loaded_segments (0x5de0c : word) = Some W_5ddc4.
Proof. vm_refl. Qed.
Lemma D_5ddc4 : decode_any W_5ddc4 = Some (Branch BC_NE 16 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddc8 : bv 32 := 0x08d70063.
Lemma F_5ddc8 : fetch_word AsanUbsan.M.loaded_segments (0x5de10 : word) = Some W_5ddc8.
Proof. vm_refl. Qed.
Lemma D_5ddc8 : decode_any W_5ddc8 = Some (Branch BC_EQ 14 13 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de48 : bv 32 := 0x01043483.
Lemma F_5de48 : fetch_word AsanUbsan.M.loaded_segments (0x5de90 : word) = Some W_5de48.
Proof. vm_refl. Qed.
Lemma D_5de48 : decode_any W_5de48 = Some (Load SZ8 true 9 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de4c : bv 32 := 0x01548bb3.
Lemma F_5de4c : fetch_word AsanUbsan.M.loaded_segments (0x5de94 : word) = Some W_5de4c.
Proof. vm_refl. Qed.
Lemma D_5de4c : decode_any W_5de4c = Some (Op ALU_ADD 23 9 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de50 : bv 32 := 0x000a0513.
Lemma F_5de50 : fetch_word AsanUbsan.M.loaded_segments (0x5de98 : word) = Some W_5de50.
Proof. vm_refl. Qed.
Lemma D_5de50 : decode_any W_5de50 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de54 : bv 32 := 0x00040593.
Lemma F_5de54 : fetch_word AsanUbsan.M.loaded_segments (0x5de9c : word) = Some W_5de54.
Proof. vm_refl. Qed.
Lemma D_5de54 : decode_any W_5de54 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de58 : bv 32 := 0x000b8693.
Lemma F_5de58 : fetch_word AsanUbsan.M.loaded_segments (0x5dea0 : word) = Some W_5de58.
Proof. vm_refl. Qed.
Lemma D_5de58 : decode_any W_5de58 = Some (OpImm ALU_ADD 13 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de5c : bv 32 := 0x1c8000ef.
Lemma F_5de5c : fetch_word AsanUbsan.M.loaded_segments (0x5dea4 : word) = Some W_5de5c.
Proof. vm_refl. Qed.
Lemma D_5de5c : decode_any W_5de5c = Some (Jal 1 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de60 : bv 32 := 0x18050463.
Lemma F_5de60 : fetch_word AsanUbsan.M.loaded_segments (0x5dea8 : word) = Some W_5de60.
Proof. vm_refl. Qed.
Lemma D_5de60 : decode_any W_5de60 = Some (Branch BC_EQ 10 0 392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de64 : bv 32 := 0x020a8463.
Lemma F_5de64 : fetch_word AsanUbsan.M.loaded_segments (0x5deac : word) = Some W_5de64.
Proof. vm_refl. Qed.
Lemma D_5de64 : decode_any W_5de64 = Some (Branch BC_EQ 21 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de68 : bv 32 := 0x00249493.
Lemma F_5de68 : fetch_word AsanUbsan.M.loaded_segments (0x5deb0 : word) = Some W_5de68.
Proof. vm_refl. Qed.
Lemma D_5de68 : decode_any W_5de68 = Some (ShiftImm ALU_SLL 9 9 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de6c : bv 32 := 0x009c8cb3.
Lemma F_5de6c : fetch_word AsanUbsan.M.loaded_segments (0x5deb4 : word) = Some W_5de6c.
Proof. vm_refl. Qed.
Lemma D_5de6c : decode_any W_5de6c = Some (Op ALU_ADD 25 25 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de70 : bv 32 := 0x002a9513.
Lemma F_5de70 : fetch_word AsanUbsan.M.loaded_segments (0x5deb8 : word) = Some W_5de70.
Proof. vm_refl. Qed.
Lemma D_5de70 : decode_any W_5de70 = Some (ShiftImm ALU_SLL 10 21 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de74 : bv 32 := 0x00ab0533.
Lemma F_5de74 : fetch_word AsanUbsan.M.loaded_segments (0x5debc : word) = Some W_5de74.
Proof. vm_refl. Qed.
Lemma D_5de74 : decode_any W_5de74 = Some (Op ALU_ADD 10 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de78 : bv 32 := 0x000b2583.
Lemma F_5de78 : fetch_word AsanUbsan.M.loaded_segments (0x5dec0 : word) = Some W_5de78.
Proof. vm_refl. Qed.
Lemma D_5de78 : decode_any W_5de78 = Some (Load SZ4 true 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de7c : bv 32 := 0x004b0b13.
Lemma F_5de7c : fetch_word AsanUbsan.M.loaded_segments (0x5dec4 : word) = Some W_5de7c.
Proof. vm_refl. Qed.
Lemma D_5de7c : decode_any W_5de7c = Some (OpImm ALU_ADD 22 22 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de80 : bv 32 := 0x00bca023.
Lemma F_5de80 : fetch_word AsanUbsan.M.loaded_segments (0x5dec8 : word) = Some W_5de80.
Proof. vm_refl. Qed.
Lemma D_5de80 : decode_any W_5de80 = Some (Store SZ4 25 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de84 : bv 32 := 0x004c8c93.
Lemma F_5de84 : fetch_word AsanUbsan.M.loaded_segments (0x5decc : word) = Some W_5de84.
Proof. vm_refl. Qed.
Lemma D_5de84 : decode_any W_5de84 = Some (OpImm ALU_ADD 25 25 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de88 : bv 32 := 0xfeab18e3.
Lemma F_5de88 : fetch_word AsanUbsan.M.loaded_segments (0x5ded0 : word) = Some W_5de88.
Proof. vm_refl. Qed.
Lemma D_5de88 : decode_any W_5de88 = Some (Branch BC_NE 22 10 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de8c : bv 32 := 0x05043503.
Lemma F_5de8c : fetch_word AsanUbsan.M.loaded_segments (0x5ded4 : word) = Some W_5de8c.
Proof. vm_refl. Qed.
Lemma D_5de8c : decode_any W_5de8c = Some (Load SZ8 true 10 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de90 : bv 32 := 0x01743823.
Lemma F_5de90 : fetch_word AsanUbsan.M.loaded_segments (0x5ded8 : word) = Some W_5de90.
Proof. vm_refl. Qed.
Lemma D_5de90 : decode_any W_5de90 = Some (Store SZ8 8 23 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de94 : bv 32 := 0x01550533.
Lemma F_5de94 : fetch_word AsanUbsan.M.loaded_segments (0x5dedc : word) = Some W_5de94.
Proof. vm_refl. Qed.
Lemma D_5de94 : decode_any W_5de94 = Some (Op ALU_ADD 10 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de98 : bv 32 := 0x04a43823.
Lemma F_5de98 : fetch_word AsanUbsan.M.loaded_segments (0x5dee0 : word) = Some W_5de98.
Proof. vm_refl. Qed.
Lemma D_5de98 : decode_any W_5de98 = Some (Store SZ8 8 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de9c : bv 32 := 0x000a0513.
Lemma F_5de9c : fetch_word AsanUbsan.M.loaded_segments (0x5dee4 : word) = Some W_5de9c.
Proof. vm_refl. Qed.
Lemma D_5de9c : decode_any W_5de9c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dea0 : bv 32 := 0x00098593.
Lemma F_5dea0 : fetch_word AsanUbsan.M.loaded_segments (0x5dee8 : word) = Some W_5dea0.
Proof. vm_refl. Qed.
Lemma D_5dea0 : decode_any W_5dea0 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dea4 : bv 32 := 0x00090613.
Lemma F_5dea4 : fetch_word AsanUbsan.M.loaded_segments (0x5deec : word) = Some W_5dea4.
Proof. vm_refl. Qed.
Lemma D_5dea4 : decode_any W_5dea4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dea8 : bv 32 := 0x00000693.
Lemma F_5dea8 : fetch_word AsanUbsan.M.loaded_segments (0x5def0 : word) = Some W_5dea8.
Proof. vm_refl. Qed.
Lemma D_5dea8 : decode_any W_5dea8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5deac : bv 32 := 0x2f8000ef.
Lemma F_5deac : fetch_word AsanUbsan.M.loaded_segments (0x5def4 : word) = Some W_5deac.
Proof. vm_refl. Qed.
Lemma D_5deac : decode_any W_5deac = Some (Jal 1 760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5deb0 : bv 32 := 0x00043503.
Lemma F_5deb0 : fetch_word AsanUbsan.M.loaded_segments (0x5def8 : word) = Some W_5deb0.
Proof. vm_refl. Qed.
Lemma D_5deb0 : decode_any W_5deb0 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5deb4 : bv 32 := 0xfff00813.
Lemma F_5deb4 : fetch_word AsanUbsan.M.loaded_segments (0x5defc : word) = Some W_5deb4.
Proof. vm_refl. Qed.
Lemma D_5deb4 : decode_any W_5deb4 = Some (OpImm ALU_ADD 16 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5deb8 : bv 32 := 0x00300613.
Lemma F_5deb8 : fetch_word AsanUbsan.M.loaded_segments (0x5df00 : word) = Some W_5deb8.
Proof. vm_refl. Qed.
Lemma D_5deb8 : decode_any W_5deb8 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5debc : bv 32 := 0x001005b7.
Lemma F_5debc : fetch_word AsanUbsan.M.loaded_segments (0x5df04 : word) = Some W_5debc.
Proof. vm_refl. Qed.
Lemma D_5debc : decode_any W_5debc = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dec0 : bv 32 := 0xfffb2697.
Lemma F_5dec0 : fetch_word AsanUbsan.M.loaded_segments (0x5df08 : word) = Some W_5dec0.
Proof. vm_refl. Qed.
Lemma D_5dec0 : decode_any W_5dec0 = Some (Auipc 13 1048498, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dec4 : bv 32 := 0x03c81713.
Lemma F_5dec4 : fetch_word AsanUbsan.M.loaded_segments (0x5df0c : word) = Some W_5dec4.
Proof. vm_refl. Qed.
Lemma D_5dec4 : decode_any W_5dec4 = Some (ShiftImm ALU_SLL 14 16 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dec8 : bv 32 := 0x03d61613.
Lemma F_5dec8 : fetch_word AsanUbsan.M.loaded_segments (0x5df10 : word) = Some W_5dec8.
Proof. vm_refl. Qed.
Lemma D_5dec8 : decode_any W_5dec8 = Some (ShiftImm ALU_SLL 12 12 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5decc : bv 32 := 0xfff58593.
Lemma F_5decc : fetch_word AsanUbsan.M.loaded_segments (0x5df14 : word) = Some W_5decc.
Proof. vm_refl. Qed.
Lemma D_5decc : decode_any W_5decc = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ded0 : bv 32 := 0x5506b683.
Lemma F_5ded0 : fetch_word AsanUbsan.M.loaded_segments (0x5df18 : word) = Some W_5ded0.
Proof. vm_refl. Qed.
Lemma D_5ded0 : decode_any W_5ded0 = Some (Load SZ8 true 13 13 1360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ded4 : bv 32 := 0xfff70713.
Lemma F_5ded4 : fetch_word AsanUbsan.M.loaded_segments (0x5df1c : word) = Some W_5ded4.
Proof. vm_refl. Qed.
Lemma D_5ded4 : decode_any W_5ded4 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ded8 : bv 32 := 0x02859793.
Lemma F_5ded8 : fetch_word AsanUbsan.M.loaded_segments (0x5df20 : word) = Some W_5ded8.
Proof. vm_refl. Qed.
Lemma D_5ded8 : decode_any W_5ded8 = Some (ShiftImm ALU_SLL 15 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dedc : bv 32 := 0x02881813.
Lemma F_5dedc : fetch_word AsanUbsan.M.loaded_segments (0x5df24 : word) = Some W_5dedc.
Proof. vm_refl. Qed.
Lemma D_5dedc : decode_any W_5dedc = Some (ShiftImm ALU_SLL 16 16 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dee0 : bv 32 := 0x00100893.
Lemma F_5dee0 : fetch_word AsanUbsan.M.loaded_segments (0x5df28 : word) = Some W_5dee0.
Proof. vm_refl. Qed.
Lemma D_5dee0 : decode_any W_5dee0 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dee4 : bv 32 := 0x03e89893.
Lemma F_5dee4 : fetch_word AsanUbsan.M.loaded_segments (0x5df2c : word) = Some W_5dee4.
Proof. vm_refl. Qed.
Lemma D_5dee4 : decode_any W_5dee4 = Some (ShiftImm ALU_SLL 17 17 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dee8 : bv 32 := 0x01c0006f.
Lemma F_5dee8 : fetch_word AsanUbsan.M.loaded_segments (0x5df30 : word) = Some W_5dee8.
Proof. vm_refl. Qed.
Lemma D_5dee8 : decode_any W_5dee8 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5deec : bv 32 := 0x1604332f.
Lemma F_5deec : fetch_word AsanUbsan.M.loaded_segments (0x5df34 : word) = Some W_5deec.
Proof. vm_refl. Qed.
Lemma D_5deec : decode_any W_5deec = Some (Lr AD true true 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5def0 : bv 32 := 0x00a31663.
Lemma F_5def0 : fetch_word AsanUbsan.M.loaded_segments (0x5df38 : word) = Some W_5def0.
Proof. vm_refl. Qed.
Lemma D_5def0 : decode_any W_5def0 = Some (Branch BC_NE 6 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5def4 : bv 32 := 0x1a5433af.
Lemma F_5def4 : fetch_word AsanUbsan.M.loaded_segments (0x5df3c : word) = Some W_5def4.
Proof. vm_refl. Qed.
Lemma D_5def4 : decode_any W_5def4 = Some (Sc AD false true 7 8 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5def8 : bv 32 := 0xfe039ae3.
Lemma F_5def8 : fetch_word AsanUbsan.M.loaded_segments (0x5df40 : word) = Some W_5def8.
Proof. vm_refl. Qed.
Lemma D_5def8 : decode_any W_5def8 = Some (Branch BC_NE 7 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5defc : bv 32 := 0x06a30463.
Lemma F_5defc : fetch_word AsanUbsan.M.loaded_segments (0x5df44 : word) = Some W_5defc.
Proof. vm_refl. Qed.
Lemma D_5defc : decode_any W_5defc = Some (Branch BC_EQ 6 10 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df04 : bv 32 := 0x00c575b3.
Lemma F_5df04 : fetch_word AsanUbsan.M.loaded_segments (0x5df4c : word) = Some W_5df04.
Proof. vm_refl. Qed.
Lemma D_5df04 : decode_any W_5df04 = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df08 : bv 32 := 0x00e572b3.
Lemma F_5df08 : fetch_word AsanUbsan.M.loaded_segments (0x5df50 : word) = Some W_5df08.
Proof. vm_refl. Qed.
Lemma D_5df08 : decode_any W_5df08 = Some (Op ALU_AND 5 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df0c : bv 32 := 0x02059663.
Lemma F_5df0c : fetch_word AsanUbsan.M.loaded_segments (0x5df54 : word) = Some W_5df0c.
Proof. vm_refl. Qed.
Lemma D_5df0c : decode_any W_5df0c = Some (Branch BC_NE 11 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df10 : bv 32 := 0x00f575b3.
Lemma F_5df10 : fetch_word AsanUbsan.M.loaded_segments (0x5df58 : word) = Some W_5df10.
Proof. vm_refl. Qed.
Lemma D_5df10 : decode_any W_5df10 = Some (Op ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df14 : bv 32 := 0x02058263.
Lemma F_5df14 : fetch_word AsanUbsan.M.loaded_segments (0x5df5c : word) = Some W_5df14.
Proof. vm_refl. Qed.
Lemma D_5df14 : decode_any W_5df14 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df38 : bv 32 := 0x018575b3.
Lemma F_5df38 : fetch_word AsanUbsan.M.loaded_segments (0x5df80 : word) = Some W_5df38.
Proof. vm_refl. Qed.
Lemma D_5df38 : decode_any W_5df38 = Some (Op ALU_AND 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df3c : bv 32 := 0x00b035b3.
Lemma F_5df3c : fetch_word AsanUbsan.M.loaded_segments (0x5df84 : word) = Some W_5df3c.
Proof. vm_refl. Qed.
Lemma D_5df3c : decode_any W_5df3c = Some (Op ALU_SLTU 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df40 : bv 32 := 0x01455313.
Lemma F_5df40 : fetch_word AsanUbsan.M.loaded_segments (0x5df88 : word) = Some W_5df40.
Proof. vm_refl. Qed.
Lemma D_5df40 : decode_any W_5df40 = Some (ShiftImm ALU_SRL 6 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df44 : bv 32 := 0xfff58593.
Lemma F_5df44 : fetch_word AsanUbsan.M.loaded_segments (0x5df8c : word) = Some W_5df44.
Proof. vm_refl. Qed.
Lemma D_5df44 : decode_any W_5df44 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df48 : bv 32 := 0x00b375b3.
Lemma F_5df48 : fetch_word AsanUbsan.M.loaded_segments (0x5df90 : word) = Some W_5df48.
Proof. vm_refl. Qed.
Lemma D_5df48 : decode_any W_5df48 = Some (Op ALU_AND 11 6 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df4c : bv 32 := 0x02c59593.
Lemma F_5df4c : fetch_word AsanUbsan.M.loaded_segments (0x5df94 : word) = Some W_5df4c.
Proof. vm_refl. Qed.
Lemma D_5df4c : decode_any W_5df4c = Some (ShiftImm ALU_SLL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df50 : bv 32 := 0x02c5d593.
Lemma F_5df50 : fetch_word AsanUbsan.M.loaded_segments (0x5df98 : word) = Some W_5df50.
Proof. vm_refl. Qed.
Lemma D_5df50 : decode_any W_5df50 = Some (ShiftImm ALU_SRL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df54 : bv 32 := 0xf8058ce3.
Lemma F_5df54 : fetch_word AsanUbsan.M.loaded_segments (0x5df9c : word) = Some W_5df54.
Proof. vm_refl. Qed.
Lemma D_5df54 : decode_any W_5df54 = Some (Branch BC_EQ 11 0 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df64 : bv 32 := 0x0a059c63.
Lemma F_5df64 : fetch_word AsanUbsan.M.loaded_segments (0x5dfac : word) = Some W_5df64.
Proof. vm_refl. Qed.
Lemma D_5df64 : decode_any W_5df64 = Some (Branch BC_NE 11 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df68 : bv 32 := 0x07813083.
Lemma F_5df68 : fetch_word AsanUbsan.M.loaded_segments (0x5dfb0 : word) = Some W_5df68.
Proof. vm_refl. Qed.
Lemma D_5df68 : decode_any W_5df68 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df6c : bv 32 := 0x07013403.
Lemma F_5df6c : fetch_word AsanUbsan.M.loaded_segments (0x5dfb4 : word) = Some W_5df6c.
Proof. vm_refl. Qed.
Lemma D_5df6c : decode_any W_5df6c = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df70 : bv 32 := 0x06813483.
Lemma F_5df70 : fetch_word AsanUbsan.M.loaded_segments (0x5dfb8 : word) = Some W_5df70.
Proof. vm_refl. Qed.
Lemma D_5df70 : decode_any W_5df70 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df74 : bv 32 := 0x06013903.
Lemma F_5df74 : fetch_word AsanUbsan.M.loaded_segments (0x5dfbc : word) = Some W_5df74.
Proof. vm_refl. Qed.
Lemma D_5df74 : decode_any W_5df74 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df78 : bv 32 := 0x05813983.
Lemma F_5df78 : fetch_word AsanUbsan.M.loaded_segments (0x5dfc0 : word) = Some W_5df78.
Proof. vm_refl. Qed.
Lemma D_5df78 : decode_any W_5df78 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df7c : bv 32 := 0x05013a03.
Lemma F_5df7c : fetch_word AsanUbsan.M.loaded_segments (0x5dfc4 : word) = Some W_5df7c.
Proof. vm_refl. Qed.
Lemma D_5df7c : decode_any W_5df7c = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df80 : bv 32 := 0x04813a83.
Lemma F_5df80 : fetch_word AsanUbsan.M.loaded_segments (0x5dfc8 : word) = Some W_5df80.
Proof. vm_refl. Qed.
Lemma D_5df80 : decode_any W_5df80 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df84 : bv 32 := 0x04013b03.
Lemma F_5df84 : fetch_word AsanUbsan.M.loaded_segments (0x5dfcc : word) = Some W_5df84.
Proof. vm_refl. Qed.
Lemma D_5df84 : decode_any W_5df84 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df88 : bv 32 := 0x03813b83.
Lemma F_5df88 : fetch_word AsanUbsan.M.loaded_segments (0x5dfd0 : word) = Some W_5df88.
Proof. vm_refl. Qed.
Lemma D_5df88 : decode_any W_5df88 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df8c : bv 32 := 0x03013c03.
Lemma F_5df8c : fetch_word AsanUbsan.M.loaded_segments (0x5dfd4 : word) = Some W_5df8c.
Proof. vm_refl. Qed.
Lemma D_5df8c : decode_any W_5df8c = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df90 : bv 32 := 0x02813c83.
Lemma F_5df90 : fetch_word AsanUbsan.M.loaded_segments (0x5dfd8 : word) = Some W_5df90.
Proof. vm_refl. Qed.
Lemma D_5df90 : decode_any W_5df90 = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df94 : bv 32 := 0x02013d03.
Lemma F_5df94 : fetch_word AsanUbsan.M.loaded_segments (0x5dfdc : word) = Some W_5df94.
Proof. vm_refl. Qed.
Lemma D_5df94 : decode_any W_5df94 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df98 : bv 32 := 0x01813d83.
Lemma F_5df98 : fetch_word AsanUbsan.M.loaded_segments (0x5dfe0 : word) = Some W_5df98.
Proof. vm_refl. Qed.
Lemma D_5df98 : decode_any W_5df98 = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df9c : bv 32 := 0x08010113.
Lemma F_5df9c : fetch_word AsanUbsan.M.loaded_segments (0x5dfe4 : word) = Some W_5df9c.
Proof. vm_refl. Qed.
Lemma D_5df9c : decode_any W_5df9c = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfa0 : bv 32 := 0x00008067.
Lemma F_5dfa0 : fetch_word AsanUbsan.M.loaded_segments (0x5dfe8 : word) = Some W_5dfa0.
Proof. vm_refl. Qed.
Lemma D_5dfa0 : decode_any W_5dfa0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

