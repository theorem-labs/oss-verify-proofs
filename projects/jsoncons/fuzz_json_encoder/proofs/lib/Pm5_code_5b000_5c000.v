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
Definition W_5b000 : bv 32 := 0x00090593.
Lemma F_5b000 : fetch_word AsanUbsan.M.loaded_segments (0x5b048 : word) = Some W_5b000.
Proof. vm_refl. Qed.
Lemma D_5b000 : decode_any W_5b000 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b004 : bv 32 := 0x00048613.
Lemma F_5b004 : fetch_word AsanUbsan.M.loaded_segments (0x5b04c : word) = Some W_5b004.
Proof. vm_refl. Qed.
Lemma D_5b004 : decode_any W_5b004 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b008 : bv 32 := 0x00040693.
Lemma F_5b008 : fetch_word AsanUbsan.M.loaded_segments (0x5b050 : word) = Some W_5b008.
Proof. vm_refl. Qed.
Lemma D_5b008 : decode_any W_5b008 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b00c : bv 32 := 0x03813083.
Lemma F_5b00c : fetch_word AsanUbsan.M.loaded_segments (0x5b054 : word) = Some W_5b00c.
Proof. vm_refl. Qed.
Lemma D_5b00c : decode_any W_5b00c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b010 : bv 32 := 0x03013403.
Lemma F_5b010 : fetch_word AsanUbsan.M.loaded_segments (0x5b058 : word) = Some W_5b010.
Proof. vm_refl. Qed.
Lemma D_5b010 : decode_any W_5b010 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b014 : bv 32 := 0x02813483.
Lemma F_5b014 : fetch_word AsanUbsan.M.loaded_segments (0x5b05c : word) = Some W_5b014.
Proof. vm_refl. Qed.
Lemma D_5b014 : decode_any W_5b014 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b018 : bv 32 := 0x02013903.
Lemma F_5b018 : fetch_word AsanUbsan.M.loaded_segments (0x5b060 : word) = Some W_5b018.
Proof. vm_refl. Qed.
Lemma D_5b018 : decode_any W_5b018 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b01c : bv 32 := 0x01813983.
Lemma F_5b01c : fetch_word AsanUbsan.M.loaded_segments (0x5b064 : word) = Some W_5b01c.
Proof. vm_refl. Qed.
Lemma D_5b01c : decode_any W_5b01c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b020 : bv 32 := 0x01013a03.
Lemma F_5b020 : fetch_word AsanUbsan.M.loaded_segments (0x5b068 : word) = Some W_5b020.
Proof. vm_refl. Qed.
Lemma D_5b020 : decode_any W_5b020 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b024 : bv 32 := 0x00813a83.
Lemma F_5b024 : fetch_word AsanUbsan.M.loaded_segments (0x5b06c : word) = Some W_5b024.
Proof. vm_refl. Qed.
Lemma D_5b024 : decode_any W_5b024 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b028 : bv 32 := 0x00013b03.
Lemma F_5b028 : fetch_word AsanUbsan.M.loaded_segments (0x5b070 : word) = Some W_5b028.
Proof. vm_refl. Qed.
Lemma D_5b028 : decode_any W_5b028 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b02c : bv 32 := 0x04010113.
Lemma F_5b02c : fetch_word AsanUbsan.M.loaded_segments (0x5b074 : word) = Some W_5b02c.
Proof. vm_refl. Qed.
Lemma D_5b02c : decode_any W_5b02c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b030 : bv 32 := 0x2cc0406f.
Lemma F_5b030 : fetch_word AsanUbsan.M.loaded_segments (0x5b078 : word) = Some W_5b030.
Proof. vm_refl. Qed.
Lemma D_5b030 : decode_any W_5b030 = Some (Jal 0 17100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b054 : bv 32 := 0xff010113.
Lemma F_5b054 : fetch_word AsanUbsan.M.loaded_segments (0x5b09c : word) = Some W_5b054.
Proof. vm_refl. Qed.
Lemma D_5b054 : decode_any W_5b054 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b058 : bv 32 := 0x00113423.
Lemma F_5b058 : fetch_word AsanUbsan.M.loaded_segments (0x5b0a0 : word) = Some W_5b058.
Proof. vm_refl. Qed.
Lemma D_5b058 : decode_any W_5b058 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b05c : bv 32 := 0x00813023.
Lemma F_5b05c : fetch_word AsanUbsan.M.loaded_segments (0x5b0a4 : word) = Some W_5b05c.
Proof. vm_refl. Qed.
Lemma D_5b05c : decode_any W_5b05c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b060 : bv 32 := 0x00058693.
Lemma F_5b060 : fetch_word AsanUbsan.M.loaded_segments (0x5b0a8 : word) = Some W_5b060.
Proof. vm_refl. Qed.
Lemma D_5b060 : decode_any W_5b060 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b064 : bv 32 := 0x00050593.
Lemma F_5b064 : fetch_word AsanUbsan.M.loaded_segments (0x5b0ac : word) = Some W_5b064.
Proof. vm_refl. Qed.
Lemma D_5b064 : decode_any W_5b064 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b068 : bv 32 := 0x0010f517.
Lemma F_5b068 : fetch_word AsanUbsan.M.loaded_segments (0x5b0b0 : word) = Some W_5b068.
Proof. vm_refl. Qed.
Lemma D_5b068 : decode_any W_5b068 = Some (Auipc 10 271, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b06c : bv 32 := 0x00800613.
Lemma F_5b06c : fetch_word AsanUbsan.M.loaded_segments (0x5b0b4 : word) = Some W_5b06c.
Proof. vm_refl. Qed.
Lemma D_5b06c : decode_any W_5b06c = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b070 : bv 32 := 0x00100713.
Lemma F_5b070 : fetch_word AsanUbsan.M.loaded_segments (0x5b0b8 : word) = Some W_5b070.
Proof. vm_refl. Qed.
Lemma D_5b070 : decode_any W_5b070 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b074 : bv 32 := 0x0a850513.
Lemma F_5b074 : fetch_word AsanUbsan.M.loaded_segments (0x5b0bc : word) = Some W_5b074.
Proof. vm_refl. Qed.
Lemma D_5b074 : decode_any W_5b074 = Some (OpImm ALU_ADD 10 10 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b078 : bv 32 := 0x00100793.
Lemma F_5b078 : fetch_word AsanUbsan.M.loaded_segments (0x5b0c0 : word) = Some W_5b078.
Proof. vm_refl. Qed.
Lemma D_5b078 : decode_any W_5b078 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b07c : bv 32 := 0x034000ef.
Lemma F_5b07c : fetch_word AsanUbsan.M.loaded_segments (0x5b0c4 : word) = Some W_5b07c.
Proof. vm_refl. Qed.
Lemma D_5b07c : decode_any W_5b07c = Some (Jal 1 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b080 : bv 32 := 0x00050a63.
Lemma F_5b080 : fetch_word AsanUbsan.M.loaded_segments (0x5b0c8 : word) = Some W_5b080.
Proof. vm_refl. Qed.
Lemma D_5b080 : decode_any W_5b080 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b084 : bv 32 := 0x00813083.
Lemma F_5b084 : fetch_word AsanUbsan.M.loaded_segments (0x5b0cc : word) = Some W_5b084.
Proof. vm_refl. Qed.
Lemma D_5b084 : decode_any W_5b084 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b088 : bv 32 := 0x00013403.
Lemma F_5b088 : fetch_word AsanUbsan.M.loaded_segments (0x5b0d0 : word) = Some W_5b088.
Proof. vm_refl. Qed.
Lemma D_5b088 : decode_any W_5b088 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b08c : bv 32 := 0x01010113.
Lemma F_5b08c : fetch_word AsanUbsan.M.loaded_segments (0x5b0d4 : word) = Some W_5b08c.
Proof. vm_refl. Qed.
Lemma D_5b08c : decode_any W_5b08c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b090 : bv 32 := 0x00008067.
Lemma F_5b090 : fetch_word AsanUbsan.M.loaded_segments (0x5b0d8 : word) = Some W_5b090.
Proof. vm_refl. Qed.
Lemma D_5b090 : decode_any W_5b090 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0b0 : bv 32 := 0xf8010113.
Lemma F_5b0b0 : fetch_word AsanUbsan.M.loaded_segments (0x5b0f8 : word) = Some W_5b0b0.
Proof. vm_refl. Qed.
Lemma D_5b0b0 : decode_any W_5b0b0 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0b4 : bv 32 := 0x06113c23.
Lemma F_5b0b4 : fetch_word AsanUbsan.M.loaded_segments (0x5b0fc : word) = Some W_5b0b4.
Proof. vm_refl. Qed.
Lemma D_5b0b4 : decode_any W_5b0b4 = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0b8 : bv 32 := 0x06813823.
Lemma F_5b0b8 : fetch_word AsanUbsan.M.loaded_segments (0x5b100 : word) = Some W_5b0b8.
Proof. vm_refl. Qed.
Lemma D_5b0b8 : decode_any W_5b0b8 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0bc : bv 32 := 0x06913423.
Lemma F_5b0bc : fetch_word AsanUbsan.M.loaded_segments (0x5b104 : word) = Some W_5b0bc.
Proof. vm_refl. Qed.
Lemma D_5b0bc : decode_any W_5b0bc = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0c0 : bv 32 := 0x07213023.
Lemma F_5b0c0 : fetch_word AsanUbsan.M.loaded_segments (0x5b108 : word) = Some W_5b0c0.
Proof. vm_refl. Qed.
Lemma D_5b0c0 : decode_any W_5b0c0 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0c4 : bv 32 := 0x05313c23.
Lemma F_5b0c4 : fetch_word AsanUbsan.M.loaded_segments (0x5b10c : word) = Some W_5b0c4.
Proof. vm_refl. Qed.
Lemma D_5b0c4 : decode_any W_5b0c4 = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0c8 : bv 32 := 0x05413823.
Lemma F_5b0c8 : fetch_word AsanUbsan.M.loaded_segments (0x5b110 : word) = Some W_5b0c8.
Proof. vm_refl. Qed.
Lemma D_5b0c8 : decode_any W_5b0c8 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0cc : bv 32 := 0x05513423.
Lemma F_5b0cc : fetch_word AsanUbsan.M.loaded_segments (0x5b114 : word) = Some W_5b0cc.
Proof. vm_refl. Qed.
Lemma D_5b0cc : decode_any W_5b0cc = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0d0 : bv 32 := 0x05613023.
Lemma F_5b0d0 : fetch_word AsanUbsan.M.loaded_segments (0x5b118 : word) = Some W_5b0d0.
Proof. vm_refl. Qed.
Lemma D_5b0d0 : decode_any W_5b0d0 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0d4 : bv 32 := 0x03713c23.
Lemma F_5b0d4 : fetch_word AsanUbsan.M.loaded_segments (0x5b11c : word) = Some W_5b0d4.
Proof. vm_refl. Qed.
Lemma D_5b0d4 : decode_any W_5b0d4 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0d8 : bv 32 := 0x03813823.
Lemma F_5b0d8 : fetch_word AsanUbsan.M.loaded_segments (0x5b120 : word) = Some W_5b0d8.
Proof. vm_refl. Qed.
Lemma D_5b0d8 : decode_any W_5b0d8 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0dc : bv 32 := 0x03913423.
Lemma F_5b0dc : fetch_word AsanUbsan.M.loaded_segments (0x5b124 : word) = Some W_5b0dc.
Proof. vm_refl. Qed.
Lemma D_5b0dc : decode_any W_5b0dc = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0e0 : bv 32 := 0x03a13023.
Lemma F_5b0e0 : fetch_word AsanUbsan.M.loaded_segments (0x5b128 : word) = Some W_5b0e0.
Proof. vm_refl. Qed.
Lemma D_5b0e0 : decode_any W_5b0e0 = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0e4 : bv 32 := 0x01b13c23.
Lemma F_5b0e4 : fetch_word AsanUbsan.M.loaded_segments (0x5b12c : word) = Some W_5b0e4.
Proof. vm_refl. Qed.
Lemma D_5b0e4 : decode_any W_5b0e4 = Some (Store SZ8 2 27 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0e8 : bv 32 := 0x00078493.
Lemma F_5b0e8 : fetch_word AsanUbsan.M.loaded_segments (0x5b130 : word) = Some W_5b0e8.
Proof. vm_refl. Qed.
Lemma D_5b0e8 : decode_any W_5b0e8 = Some (OpImm ALU_ADD 9 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0ec : bv 32 := 0x00070d93.
Lemma F_5b0ec : fetch_word AsanUbsan.M.loaded_segments (0x5b134 : word) = Some W_5b0ec.
Proof. vm_refl. Qed.
Lemma D_5b0ec : decode_any W_5b0ec = Some (OpImm ALU_ADD 27 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0f0 : bv 32 := 0x00068b93.
Lemma F_5b0f0 : fetch_word AsanUbsan.M.loaded_segments (0x5b138 : word) = Some W_5b0f0.
Proof. vm_refl. Qed.
Lemma D_5b0f0 : decode_any W_5b0f0 = Some (OpImm ALU_ADD 23 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0f4 : bv 32 := 0x00060913.
Lemma F_5b0f4 : fetch_word AsanUbsan.M.loaded_segments (0x5b13c : word) = Some W_5b0f4.
Proof. vm_refl. Qed.
Lemma D_5b0f4 : decode_any W_5b0f4 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0f8 : bv 32 := 0x00058a93.
Lemma F_5b0f8 : fetch_word AsanUbsan.M.loaded_segments (0x5b140 : word) = Some W_5b0f8.
Proof. vm_refl. Qed.
Lemma D_5b0f8 : decode_any W_5b0f8 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b0fc : bv 32 := 0x00050b13.
Lemma F_5b0fc : fetch_word AsanUbsan.M.loaded_segments (0x5b144 : word) = Some W_5b0fc.
Proof. vm_refl. Qed.
Lemma D_5b0fc : decode_any W_5b0fc = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b100 : bv 32 := 0x7092d0ef.
Lemma F_5b100 : fetch_word AsanUbsan.M.loaded_segments (0x5b148 : word) = Some W_5b100.
Proof. vm_refl. Qed.
Lemma D_5b100 : decode_any W_5b100 = Some (Jal 1 188168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b104 : bv 32 := 0x7e050463.
Lemma F_5b104 : fetch_word AsanUbsan.M.loaded_segments (0x5b14c : word) = Some W_5b104.
Proof. vm_refl. Qed.
Lemma D_5b104 : decode_any W_5b104 = Some (Branch BC_EQ 10 0 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b108 : bv 32 := 0x3c9330ef.
Lemma F_5b108 : fetch_word AsanUbsan.M.loaded_segments (0x5b150 : word) = Some W_5b108.
Proof. vm_refl. Qed.
Lemma D_5b108 : decode_any W_5b108 = Some (Jal 1 211912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b10c : bv 32 := 0x7e051663.
Lemma F_5b10c : fetch_word AsanUbsan.M.loaded_segments (0x5b154 : word) = Some W_5b10c.
Proof. vm_refl. Qed.
Lemma D_5b10c : decode_any W_5b10c = Some (Branch BC_NE 10 0 2028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b110 : bv 32 := 0x080b86e3.
Lemma F_5b110 : fetch_word AsanUbsan.M.loaded_segments (0x5b158 : word) = Some W_5b110.
Proof. vm_refl. Qed.
Lemma D_5b110 : decode_any W_5b110 = Some (Branch BC_EQ 23 0 2188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b114 : bv 32 := 0x00800513.
Lemma F_5b114 : fetch_word AsanUbsan.M.loaded_segments (0x5b15c : word) = Some W_5b114.
Proof. vm_refl. Qed.
Lemma D_5b114 : decode_any W_5b114 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b118 : bv 32 := 0x02a97e63.
Lemma F_5b118 : fetch_word AsanUbsan.M.loaded_segments (0x5b160 : word) = Some W_5b118.
Proof. vm_refl. Qed.
Lemma D_5b118 : decode_any W_5b118 = Some (Branch BC_GEU 18 10 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b128 : bv 32 := 0x00800413.
Lemma F_5b128 : fetch_word AsanUbsan.M.loaded_segments (0x5b170 : word) = Some W_5b128.
Proof. vm_refl. Qed.
Lemma D_5b128 : decode_any W_5b128 = Some (OpImm ALU_ADD 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b12c : bv 32 := 0xfff40c93.
Lemma F_5b12c : fetch_word AsanUbsan.M.loaded_segments (0x5b174 : word) = Some W_5b12c.
Proof. vm_refl. Qed.
Lemma D_5b12c : decode_any W_5b12c = Some (OpImm ALU_ADD 25 8 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b130 : bv 32 := 0x01947533.
Lemma F_5b130 : fetch_word AsanUbsan.M.loaded_segments (0x5b178 : word) = Some W_5b130.
Proof. vm_refl. Qed.
Lemma D_5b130 : decode_any W_5b130 = Some (Op ALU_AND 10 8 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b134 : bv 32 := 0x7c051a63.
Lemma F_5b134 : fetch_word AsanUbsan.M.loaded_segments (0x5b17c : word) = Some W_5b134.
Proof. vm_refl. Qed.
Lemma D_5b134 : decode_any W_5b134 = Some (Branch BC_NE 10 0 2004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b138 : bv 32 := 0x03100513.
Lemma F_5b138 : fetch_word AsanUbsan.M.loaded_segments (0x5b180 : word) = Some W_5b138.
Proof. vm_refl. Qed.
Lemma D_5b138 : decode_any W_5b138 = Some (OpImm ALU_ADD 10 0 49, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b13c : bv 32 := 0x7ffb0d13.
Lemma F_5b13c : fetch_word AsanUbsan.M.loaded_segments (0x5b184 : word) = Some W_5b13c.
Proof. vm_refl. Qed.
Lemma D_5b13c : decode_any W_5b13c = Some (OpImm ALU_ADD 26 22 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b140 : bv 32 := 0x00913423.
Lemma F_5b140 : fetch_word AsanUbsan.M.loaded_segments (0x5b188 : word) = Some W_5b140.
Proof. vm_refl. Qed.
Lemma D_5b140 : decode_any W_5b140 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b144 : bv 32 := 0x00b13823.
Lemma F_5b144 : fetch_word AsanUbsan.M.loaded_segments (0x5b18c : word) = Some W_5b144.
Proof. vm_refl. Qed.
Lemma D_5b144 : decode_any W_5b144 = Some (Store SZ8 2 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b148 : bv 32 := 0x06aaf463.
Lemma F_5b148 : fetch_word AsanUbsan.M.loaded_segments (0x5b190 : word) = Some W_5b148.
Proof. vm_refl. Qed.
Lemma D_5b148 : decode_any W_5b148 = Some (Branch BC_GEU 21 10 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b14c : bv 32 := 0x00000993.
Lemma F_5b14c : fetch_word AsanUbsan.M.loaded_segments (0x5b194 : word) = Some W_5b14c.
Proof. vm_refl. Qed.
Lemma D_5b14c : decode_any W_5b14c = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b150 : bv 32 := 0x0cc0006f.
Lemma F_5b150 : fetch_word AsanUbsan.M.loaded_segments (0x5b198 : word) = Some W_5b150.
Proof. vm_refl. Qed.
Lemma D_5b150 : decode_any W_5b150 = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b154 : bv 32 := 0x20000613.
Lemma F_5b154 : fetch_word AsanUbsan.M.loaded_segments (0x5b19c : word) = Some W_5b154.
Proof. vm_refl. Qed.
Lemma D_5b154 : decode_any W_5b154 = Some (OpImm ALU_ADD 12 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b158 : bv 32 := 0x00090593.
Lemma F_5b158 : fetch_word AsanUbsan.M.loaded_segments (0x5b1a0 : word) = Some W_5b158.
Proof. vm_refl. Qed.
Lemma D_5b158 : decode_any W_5b158 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b15c : bv 32 := 0x00c96463.
Lemma F_5b15c : fetch_word AsanUbsan.M.loaded_segments (0x5b1a4 : word) = Some W_5b15c.
Proof. vm_refl. Qed.
Lemma D_5b15c : decode_any W_5b15c = Some (Branch BC_LTU 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b164 : bv 32 := 0xfff58613.
Lemma F_5b164 : fetch_word AsanUbsan.M.loaded_segments (0x5b1ac : word) = Some W_5b164.
Proof. vm_refl. Qed.
Lemma D_5b164 : decode_any W_5b164 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b168 : bv 32 := 0x00c5f633.
Lemma F_5b168 : fetch_word AsanUbsan.M.loaded_segments (0x5b1b0 : word) = Some W_5b168.
Proof. vm_refl. Qed.
Lemma D_5b168 : decode_any W_5b168 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b16c : bv 32 := 0x040618e3.
Lemma F_5b16c : fetch_word AsanUbsan.M.loaded_segments (0x5b1b4 : word) = Some W_5b16c.
Proof. vm_refl. Qed.
Lemma D_5b16c : decode_any W_5b16c = Some (Branch BC_NE 12 0 2128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b170 : bv 32 := 0xfffb5617.
Lemma F_5b170 : fetch_word AsanUbsan.M.loaded_segments (0x5b1b8 : word) = Some W_5b170.
Proof. vm_refl. Qed.
Lemma D_5b170 : decode_any W_5b170 = Some (Auipc 12 1048501, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b174 : bv 32 := 0x2c063603.
Lemma F_5b174 : fetch_word AsanUbsan.M.loaded_segments (0x5b1bc : word) = Some W_5b174.
Proof. vm_refl. Qed.
Lemma D_5b174 : decode_any W_5b174 = Some (Load SZ8 true 12 12 704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b178 : bv 32 := 0x40b006b3.
Lemma F_5b178 : fetch_word AsanUbsan.M.loaded_segments (0x5b1c0 : word) = Some W_5b178.
Proof. vm_refl. Qed.
Lemma D_5b178 : decode_any W_5b178 = Some (Op ALU_SUB 13 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b17c : bv 32 := 0x00d5f5b3.
Lemma F_5b17c : fetch_word AsanUbsan.M.loaded_segments (0x5b1c4 : word) = Some W_5b17c.
Proof. vm_refl. Qed.
Lemma D_5b17c : decode_any W_5b17c = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b180 : bv 32 := 0x02c585b3.
Lemma F_5b180 : fetch_word AsanUbsan.M.loaded_segments (0x5b1c8 : word) = Some W_5b180.
Proof. vm_refl. Qed.
Lemma D_5b180 : decode_any W_5b180 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b184 : bv 32 := 0xfffb5617.
Lemma F_5b184 : fetch_word AsanUbsan.M.loaded_segments (0x5b1cc : word) = Some W_5b184.
Proof. vm_refl. Qed.
Lemma D_5b184 : decode_any W_5b184 = Some (Auipc 12 1048501, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b188 : bv 32 := 0x03a5d593.
Lemma F_5b188 : fetch_word AsanUbsan.M.loaded_segments (0x5b1d0 : word) = Some W_5b188.
Proof. vm_refl. Qed.
Lemma D_5b188 : decode_any W_5b188 = Some (ShiftImm ALU_SRL 11 11 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b18c : bv 32 := 0x32460613.
Lemma F_5b18c : fetch_word AsanUbsan.M.loaded_segments (0x5b1d4 : word) = Some W_5b18c.
Proof. vm_refl. Qed.
Lemma D_5b18c : decode_any W_5b18c = Some (OpImm ALU_ADD 12 12 804, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b190 : bv 32 := 0x00b605b3.
Lemma F_5b190 : fetch_word AsanUbsan.M.loaded_segments (0x5b1d8 : word) = Some W_5b190.
Proof. vm_refl. Qed.
Lemma D_5b190 : decode_any W_5b190 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b194 : bv 32 := 0x0005c583.
Lemma F_5b194 : fetch_word AsanUbsan.M.loaded_segments (0x5b1dc : word) = Some W_5b194.
Proof. vm_refl. Qed.
Lemma D_5b194 : decode_any W_5b194 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b198 : bv 32 := 0x00459593.
Lemma F_5b198 : fetch_word AsanUbsan.M.loaded_segments (0x5b1e0 : word) = Some W_5b198.
Proof. vm_refl. Qed.
Lemma D_5b198 : decode_any W_5b198 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b19c : bv 32 := 0x06058593.
Lemma F_5b19c : fetch_word AsanUbsan.M.loaded_segments (0x5b1e4 : word) = Some W_5b19c.
Proof. vm_refl. Qed.
Lemma D_5b19c : decode_any W_5b19c = Some (OpImm ALU_ADD 11 11 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1a0 : bv 32 := 0x0705f593.
Lemma F_5b1a0 : fetch_word AsanUbsan.M.loaded_segments (0x5b1e8 : word) = Some W_5b1a0.
Proof. vm_refl. Qed.
Lemma D_5b1a0 : decode_any W_5b1a0 = Some (OpImm ALU_AND 11 11 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1a4 : bv 32 := 0x00090413.
Lemma F_5b1a4 : fetch_word AsanUbsan.M.loaded_segments (0x5b1ec : word) = Some W_5b1a4.
Proof. vm_refl. Qed.
Lemma D_5b1a4 : decode_any W_5b1a4 = Some (OpImm ALU_ADD 8 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1a8 : bv 32 := 0xf92570e3.
Lemma F_5b1a8 : fetch_word AsanUbsan.M.loaded_segments (0x5b1f0 : word) = Some W_5b1a8.
Proof. vm_refl. Qed.
Lemma D_5b1a8 : decode_any W_5b1a8 = Some (Branch BC_GEU 10 18 8064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1ac : bv 32 := 0xf81ff06f.
Lemma F_5b1ac : fetch_word AsanUbsan.M.loaded_segments (0x5b1f4 : word) = Some W_5b1ac.
Proof. vm_refl. Qed.
Lemma D_5b1ac : decode_any W_5b1ac = Some (Jal 0 2097024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1b0 : bv 32 := 0x06100513.
Lemma F_5b1b0 : fetch_word AsanUbsan.M.loaded_segments (0x5b1f8 : word) = Some W_5b1b0.
Proof. vm_refl. Qed.
Lemma D_5b1b0 : decode_any W_5b1b0 = Some (OpImm ALU_ADD 10 0 97, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1b4 : bv 32 := 0x00aaf663.
Lemma F_5b1b4 : fetch_word AsanUbsan.M.loaded_segments (0x5b1fc : word) = Some W_5b1b4.
Proof. vm_refl. Qed.
Lemma D_5b1b4 : decode_any W_5b1b4 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1b8 : bv 32 := 0x00100993.
Lemma F_5b1b8 : fetch_word AsanUbsan.M.loaded_segments (0x5b200 : word) = Some W_5b1b8.
Proof. vm_refl. Qed.
Lemma D_5b1b8 : decode_any W_5b1b8 = Some (OpImm ALU_ADD 19 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1bc : bv 32 := 0x0600006f.
Lemma F_5b1bc : fetch_word AsanUbsan.M.loaded_segments (0x5b204 : word) = Some W_5b1bc.
Proof. vm_refl. Qed.
Lemma D_5b1bc : decode_any W_5b1bc = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1c0 : bv 32 := 0x1c100513.
Lemma F_5b1c0 : fetch_word AsanUbsan.M.loaded_segments (0x5b208 : word) = Some W_5b1c0.
Proof. vm_refl. Qed.
Lemma D_5b1c0 : decode_any W_5b1c0 = Some (OpImm ALU_ADD 10 0 449, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1c4 : bv 32 := 0x00aaf663.
Lemma F_5b1c4 : fetch_word AsanUbsan.M.loaded_segments (0x5b20c : word) = Some W_5b1c4.
Proof. vm_refl. Qed.
Lemma D_5b1c4 : decode_any W_5b1c4 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1c8 : bv 32 := 0x00200993.
Lemma F_5b1c8 : fetch_word AsanUbsan.M.loaded_segments (0x5b210 : word) = Some W_5b1c8.
Proof. vm_refl. Qed.
Lemma D_5b1c8 : decode_any W_5b1c8 = Some (OpImm ALU_ADD 19 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1cc : bv 32 := 0x0500006f.
Lemma F_5b1cc : fetch_word AsanUbsan.M.loaded_segments (0x5b214 : word) = Some W_5b1cc.
Proof. vm_refl. Qed.
Lemma D_5b1cc : decode_any W_5b1cc = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1d0 : bv 32 := 0x00001537.
Lemma F_5b1d0 : fetch_word AsanUbsan.M.loaded_segments (0x5b218 : word) = Some W_5b1d0.
Proof. vm_refl. Qed.
Lemma D_5b1d0 : decode_any W_5b1d0 = Some (Lui 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1d4 : bv 32 := 0xf815051b.
Lemma F_5b1d4 : fetch_word AsanUbsan.M.loaded_segments (0x5b21c : word) = Some W_5b1d4.
Proof. vm_refl. Qed.
Lemma D_5b1d4 : decode_any W_5b1d4 = Some (OpImm32 10 10 3969, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1d8 : bv 32 := 0x00aaf663.
Lemma F_5b1d8 : fetch_word AsanUbsan.M.loaded_segments (0x5b220 : word) = Some W_5b1d8.
Proof. vm_refl. Qed.
Lemma D_5b1d8 : decode_any W_5b1d8 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1dc : bv 32 := 0x00300993.
Lemma F_5b1dc : fetch_word AsanUbsan.M.loaded_segments (0x5b224 : word) = Some W_5b1dc.
Proof. vm_refl. Qed.
Lemma D_5b1dc : decode_any W_5b1dc = Some (OpImm ALU_ADD 19 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1e0 : bv 32 := 0x03c0006f.
Lemma F_5b1e0 : fetch_word AsanUbsan.M.loaded_segments (0x5b228 : word) = Some W_5b1e0.
Proof. vm_refl. Qed.
Lemma D_5b1e0 : decode_any W_5b1e0 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1e4 : bv 32 := 0x00004537.
Lemma F_5b1e4 : fetch_word AsanUbsan.M.loaded_segments (0x5b22c : word) = Some W_5b1e4.
Proof. vm_refl. Qed.
Lemma D_5b1e4 : decode_any W_5b1e4 = Some (Lui 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1e8 : bv 32 := 0xf015051b.
Lemma F_5b1e8 : fetch_word AsanUbsan.M.loaded_segments (0x5b230 : word) = Some W_5b1e8.
Proof. vm_refl. Qed.
Lemma D_5b1e8 : decode_any W_5b1e8 = Some (OpImm32 10 10 3841, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1ec : bv 32 := 0x00aaf663.
Lemma F_5b1ec : fetch_word AsanUbsan.M.loaded_segments (0x5b234 : word) = Some W_5b1ec.
Proof. vm_refl. Qed.
Lemma D_5b1ec : decode_any W_5b1ec = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1f0 : bv 32 := 0x00400993.
Lemma F_5b1f0 : fetch_word AsanUbsan.M.loaded_segments (0x5b238 : word) = Some W_5b1f0.
Proof. vm_refl. Qed.
Lemma D_5b1f0 : decode_any W_5b1f0 = Some (OpImm ALU_ADD 19 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1f4 : bv 32 := 0x0280006f.
Lemma F_5b1f4 : fetch_word AsanUbsan.M.loaded_segments (0x5b23c : word) = Some W_5b1f4.
Proof. vm_refl. Qed.
Lemma D_5b1f4 : decode_any W_5b1f4 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1f8 : bv 32 := 0x00008537.
Lemma F_5b1f8 : fetch_word AsanUbsan.M.loaded_segments (0x5b240 : word) = Some W_5b1f8.
Proof. vm_refl. Qed.
Lemma D_5b1f8 : decode_any W_5b1f8 = Some (Lui 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b1fc : bv 32 := 0xe015051b.
Lemma F_5b1fc : fetch_word AsanUbsan.M.loaded_segments (0x5b244 : word) = Some W_5b1fc.
Proof. vm_refl. Qed.
Lemma D_5b1fc : decode_any W_5b1fc = Some (OpImm32 10 10 3585, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b200 : bv 32 := 0x00aaf663.
Lemma F_5b200 : fetch_word AsanUbsan.M.loaded_segments (0x5b248 : word) = Some W_5b200.
Proof. vm_refl. Qed.
Lemma D_5b200 : decode_any W_5b200 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b204 : bv 32 := 0x00500993.
Lemma F_5b204 : fetch_word AsanUbsan.M.loaded_segments (0x5b24c : word) = Some W_5b204.
Proof. vm_refl. Qed.
Lemma D_5b204 : decode_any W_5b204 = Some (OpImm ALU_ADD 19 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b208 : bv 32 := 0x0140006f.
Lemma F_5b208 : fetch_word AsanUbsan.M.loaded_segments (0x5b250 : word) = Some W_5b208.
Proof. vm_refl. Qed.
Lemma D_5b208 : decode_any W_5b208 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b20c : bv 32 := 0x00010537.
Lemma F_5b20c : fetch_word AsanUbsan.M.loaded_segments (0x5b254 : word) = Some W_5b20c.
Proof. vm_refl. Qed.
Lemma D_5b20c : decode_any W_5b20c = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b210 : bv 32 := 0xc015051b.
Lemma F_5b210 : fetch_word AsanUbsan.M.loaded_segments (0x5b258 : word) = Some W_5b210.
Proof. vm_refl. Qed.
Lemma D_5b210 : decode_any W_5b210 = Some (OpImm32 10 10 3073, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b214 : bv 32 := 0x00aab533.
Lemma F_5b214 : fetch_word AsanUbsan.M.loaded_segments (0x5b25c : word) = Some W_5b214.
Proof. vm_refl. Qed.
Lemma D_5b214 : decode_any W_5b214 = Some (Op ALU_SLTU 10 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b218 : bv 32 := 0x00754993.
Lemma F_5b218 : fetch_word AsanUbsan.M.loaded_segments (0x5b260 : word) = Some W_5b218.
Proof. vm_refl. Qed.
Lemma D_5b218 : decode_any W_5b218 = Some (OpImm ALU_XOR 19 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b21c : bv 32 := 0x629d1503.
Lemma F_5b21c : fetch_word AsanUbsan.M.loaded_segments (0x5b264 : word) = Some W_5b21c.
Proof. vm_refl. Qed.
Lemma D_5b21c : decode_any W_5b21c = Some (Load SZ2 true 10 26 1577, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b220 : bv 32 := 0x0230000f.
Lemma F_5b220 : fetch_word AsanUbsan.M.loaded_segments (0x5b268 : word) = Some W_5b220.
Proof. vm_refl. Qed.
Lemma D_5b220 : decode_any W_5b220 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b224 : bv 32 := 0x00010a37.
Lemma F_5b224 : fetch_word AsanUbsan.M.loaded_segments (0x5b26c : word) = Some W_5b224.
Proof. vm_refl. Qed.
Lemma D_5b224 : decode_any W_5b224 = Some (Lui 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b228 : bv 32 := 0xfffa0c1b.
Lemma F_5b228 : fetch_word AsanUbsan.M.loaded_segments (0x5b270 : word) = Some W_5b228.
Proof. vm_refl. Qed.
Lemma D_5b228 : decode_any W_5b228 = Some (OpImm32 24 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b22c : bv 32 := 0x01857533.
Lemma F_5b22c : fetch_word AsanUbsan.M.loaded_segments (0x5b274 : word) = Some W_5b22c.
Proof. vm_refl. Qed.
Lemma D_5b22c : decode_any W_5b22c = Some (Op ALU_AND 10 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b230 : bv 32 := 0x4a0050ef.
Lemma F_5b230 : fetch_word AsanUbsan.M.loaded_segments (0x5b278 : word) = Some W_5b230.
Proof. vm_refl. Qed.
Lemma D_5b230 : decode_any W_5b230 = Some (Jal 1 21664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b234 : bv 32 := 0x00050493.
Lemma F_5b234 : fetch_word AsanUbsan.M.loaded_segments (0x5b27c : word) = Some W_5b234.
Proof. vm_refl. Qed.
Lemma D_5b234 : decode_any W_5b234 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b238 : bv 32 := 0x62bd1503.
Lemma F_5b238 : fetch_word AsanUbsan.M.loaded_segments (0x5b280 : word) = Some W_5b238.
Proof. vm_refl. Qed.
Lemma D_5b238 : decode_any W_5b238 = Some (Load SZ2 true 10 26 1579, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b23c : bv 32 := 0x0230000f.
Lemma F_5b23c : fetch_word AsanUbsan.M.loaded_segments (0x5b284 : word) = Some W_5b23c.
Proof. vm_refl. Qed.
Lemma D_5b23c : decode_any W_5b23c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b240 : bv 32 := 0x01857533.
Lemma F_5b240 : fetch_word AsanUbsan.M.loaded_segments (0x5b288 : word) = Some W_5b240.
Proof. vm_refl. Qed.
Lemma D_5b240 : decode_any W_5b240 = Some (Op ALU_AND 10 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b244 : bv 32 := 0x48c050ef.
Lemma F_5b244 : fetch_word AsanUbsan.M.loaded_segments (0x5b28c : word) = Some W_5b244.
Proof. vm_refl. Qed.
Lemma D_5b244 : decode_any W_5b244 = Some (Jal 1 21644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b248 : bv 32 := 0x0b34e663.
Lemma F_5b248 : fetch_word AsanUbsan.M.loaded_segments (0x5b290 : word) = Some W_5b248.
Proof. vm_refl. Qed.
Lemma D_5b248 : decode_any W_5b248 = Some (Branch BC_LTU 9 19 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b24c : bv 32 := 0x00048993.
Lemma F_5b24c : fetch_word AsanUbsan.M.loaded_segments (0x5b294 : word) = Some W_5b24c.
Proof. vm_refl. Qed.
Lemma D_5b24c : decode_any W_5b24c = Some (OpImm ALU_ADD 19 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b250 : bv 32 := 0x0aa4f463.
Lemma F_5b250 : fetch_word AsanUbsan.M.loaded_segments (0x5b298 : word) = Some W_5b250.
Proof. vm_refl. Qed.
Lemma D_5b250 : decode_any W_5b250 = Some (Branch BC_GEU 9 10 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b254 : bv 32 := 0x00800593.
Lemma F_5b254 : fetch_word AsanUbsan.M.loaded_segments (0x5b29c : word) = Some W_5b254.
Proof. vm_refl. Qed.
Lemma D_5b254 : decode_any W_5b254 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b258 : bv 32 := 0x000a8513.
Lemma F_5b258 : fetch_word AsanUbsan.M.loaded_segments (0x5b2a0 : word) = Some W_5b258.
Proof. vm_refl. Qed.
Lemma D_5b258 : decode_any W_5b258 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b25c : bv 32 := 0x0155e463.
Lemma F_5b25c : fetch_word AsanUbsan.M.loaded_segments (0x5b2a4 : word) = Some W_5b25c.
Proof. vm_refl. Qed.
Lemma D_5b25c : decode_any W_5b25c = Some (Branch BC_LTU 11 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b260 : bv 32 := 0x00800513.
Lemma F_5b260 : fetch_word AsanUbsan.M.loaded_segments (0x5b2a8 : word) = Some W_5b260.
Proof. vm_refl. Qed.
Lemma D_5b260 : decode_any W_5b260 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b264 : bv 32 := 0x00850533.
Lemma F_5b264 : fetch_word AsanUbsan.M.loaded_segments (0x5b2ac : word) = Some W_5b264.
Proof. vm_refl. Qed.
Lemma D_5b264 : decode_any W_5b264 = Some (Op ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b268 : bv 32 := 0x40800c33.
Lemma F_5b268 : fetch_word AsanUbsan.M.loaded_segments (0x5b2b0 : word) = Some W_5b268.
Proof. vm_refl. Qed.
Lemma D_5b268 : decode_any W_5b268 = Some (Op ALU_SUB 24 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b26c : bv 32 := 0x00993593.
Lemma F_5b26c : fetch_word AsanUbsan.M.loaded_segments (0x5b2b4 : word) = Some W_5b26c.
Proof. vm_refl. Qed.
Lemma D_5b26c : decode_any W_5b26c = Some (OpImm ALU_SLTU 11 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b270 : bv 32 := 0xfff50513.
Lemma F_5b270 : fetch_word AsanUbsan.M.loaded_segments (0x5b2b8 : word) = Some W_5b270.
Proof. vm_refl. Qed.
Lemma D_5b270 : decode_any W_5b270 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b274 : bv 32 := 0xfff58593.
Lemma F_5b274 : fetch_word AsanUbsan.M.loaded_segments (0x5b2bc : word) = Some W_5b274.
Proof. vm_refl. Qed.
Lemma D_5b274 : decode_any W_5b274 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b278 : bv 32 := 0x01857533.
Lemma F_5b278 : fetch_word AsanUbsan.M.loaded_segments (0x5b2c0 : word) = Some W_5b278.
Proof. vm_refl. Qed.
Lemma D_5b278 : decode_any W_5b278 = Some (Op ALU_AND 10 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b27c : bv 32 := 0x0085f5b3.
Lemma F_5b27c : fetch_word AsanUbsan.M.loaded_segments (0x5b2c4 : word) = Some W_5b27c.
Proof. vm_refl. Qed.
Lemma D_5b27c : decode_any W_5b27c = Some (Op ALU_AND 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b280 : bv 32 := 0x00b50533.
Lemma F_5b280 : fetch_word AsanUbsan.M.loaded_segments (0x5b2c8 : word) = Some W_5b280.
Proof. vm_refl. Qed.
Lemma D_5b280 : decode_any W_5b280 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b284 : bv 32 := 0x00757593.
Lemma F_5b284 : fetch_word AsanUbsan.M.loaded_segments (0x5b2cc : word) = Some W_5b284.
Proof. vm_refl. Qed.
Lemma D_5b284 : decode_any W_5b284 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b288 : bv 32 := 0x6a059063.
Lemma F_5b288 : fetch_word AsanUbsan.M.loaded_segments (0x5b2d0 : word) = Some W_5b288.
Proof. vm_refl. Qed.
Lemma D_5b288 : decode_any W_5b288 = Some (Branch BC_NE 11 0 1696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b28c : bv 32 := 0x01000593.
Lemma F_5b28c : fetch_word AsanUbsan.M.loaded_segments (0x5b2d4 : word) = Some W_5b28c.
Proof. vm_refl. Qed.
Lemma D_5b28c : decode_any W_5b28c = Some (OpImm ALU_ADD 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b290 : bv 32 := 0x001ab493.
Lemma F_5b290 : fetch_word AsanUbsan.M.loaded_segments (0x5b2d8 : word) = Some W_5b290.
Proof. vm_refl. Qed.
Lemma D_5b290 : decode_any W_5b290 = Some (OpImm ALU_SLTU 9 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b294 : bv 32 := 0x001a061b.
Lemma F_5b294 : fetch_word AsanUbsan.M.loaded_segments (0x5b2dc : word) = Some W_5b294.
Proof. vm_refl. Qed.
Lemma D_5b294 : decode_any W_5b294 = Some (OpImm32 12 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b298 : bv 32 := 0x01359a3b.
Lemma F_5b298 : fetch_word AsanUbsan.M.loaded_segments (0x5b2e0 : word) = Some W_5b298.
Proof. vm_refl. Qed.
Lemma D_5b298 : decode_any W_5b298 = Some (Op32 ALU_SLL 20 11 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b29c : bv 32 := 0x00100593.
Lemma F_5b29c : fetch_word AsanUbsan.M.loaded_segments (0x5b2e4 : word) = Some W_5b29c.
Proof. vm_refl. Qed.
Lemma D_5b29c : decode_any W_5b29c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b2a0 : bv 32 := 0x009a84b3.
Lemma F_5b2a0 : fetch_word AsanUbsan.M.loaded_segments (0x5b2e8 : word) = Some W_5b2a0.
Proof. vm_refl. Qed.
Lemma D_5b2a0 : decode_any W_5b2a0 = Some (Op ALU_ADD 9 21 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b2a4 : bv 32 := 0x00c936b3.
Lemma F_5b2a4 : fetch_word AsanUbsan.M.loaded_segments (0x5b2ec : word) = Some W_5b2a4.
Proof. vm_refl. Qed.
Lemma D_5b2a4 : decode_any W_5b2a4 = Some (Op ALU_SLTU 13 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b2a8 : bv 32 := 0x014509b3.
Lemma F_5b2a8 : fetch_word AsanUbsan.M.loaded_segments (0x5b2f0 : word) = Some W_5b2a8.
Proof. vm_refl. Qed.
Lemma D_5b2a8 : decode_any W_5b2a8 = Some (Op ALU_ADD 19 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b2ac : bv 32 := 0x00c9b433.
Lemma F_5b2ac : fetch_word AsanUbsan.M.loaded_segments (0x5b2f4 : word) = Some W_5b2ac.
Proof. vm_refl. Qed.
Lemma D_5b2ac : decode_any W_5b2ac = Some (Op ALU_SLTU 8 19 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b2b0 : bv 32 := 0x0086f433.
Lemma F_5b2b0 : fetch_word AsanUbsan.M.loaded_segments (0x5b2f8 : word) = Some W_5b2b0.
Proof. vm_refl. Qed.
Lemma D_5b2b0 : decode_any W_5b2b0 = Some (Op ALU_AND 8 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b2b4 : bv 32 := 0xfff40513.
Lemma F_5b2b4 : fetch_word AsanUbsan.M.loaded_segments (0x5b2fc : word) = Some W_5b2b4.
Proof. vm_refl. Qed.
Lemma D_5b2b4 : decode_any W_5b2b4 = Some (OpImm ALU_ADD 10 8 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b2b8 : bv 32 := 0x01457633.
Lemma F_5b2b8 : fetch_word AsanUbsan.M.loaded_segments (0x5b300 : word) = Some W_5b2b8.
Proof. vm_refl. Qed.
Lemma D_5b2b8 : decode_any W_5b2b8 = Some (Op ALU_AND 12 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b2bc : bv 32 := 0x02859513.
Lemma F_5b2bc : fetch_word AsanUbsan.M.loaded_segments (0x5b304 : word) = Some W_5b2bc.
Proof. vm_refl. Qed.
Lemma D_5b2bc : decode_any W_5b2bc = Some (ShiftImm ALU_SLL 10 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b2c0 : bv 32 := 0x013609b3.
Lemma F_5b2c0 : fetch_word AsanUbsan.M.loaded_segments (0x5b308 : word) = Some W_5b2c0.
Proof. vm_refl. Qed.
Lemma D_5b2c0 : decode_any W_5b2c0 = Some (Op ALU_ADD 19 12 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b2c4 : bv 32 := 0x01556863.
Lemma F_5b2c4 : fetch_word AsanUbsan.M.loaded_segments (0x5b30c : word) = Some W_5b2c4.
Proof. vm_refl. Qed.
Lemma D_5b2c4 : decode_any W_5b2c4 = Some (Branch BC_LTU 10 21 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b2c8 : bv 32 := 0x01356663.
Lemma F_5b2c8 : fetch_word AsanUbsan.M.loaded_segments (0x5b310 : word) = Some W_5b2c8.
Proof. vm_refl. Qed.
Lemma D_5b2c8 : decode_any W_5b2c8 = Some (Branch BC_LTU 10 19 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b2cc : bv 32 := 0x621d3503.
Lemma F_5b2cc : fetch_word AsanUbsan.M.loaded_segments (0x5b314 : word) = Some W_5b2cc.
Proof. vm_refl. Qed.
Lemma D_5b2cc : decode_any W_5b2cc = Some (Load SZ8 true 10 26 1569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b2d0 : bv 32 := 0x06957063.
Lemma F_5b2d0 : fetch_word AsanUbsan.M.loaded_segments (0x5b318 : word) = Some W_5b2d0.
Proof. vm_refl. Qed.
Lemma D_5b2d0 : decode_any W_5b2d0 = Some (Branch BC_GEU 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b2f4 : bv 32 := 0xf6a9e0e3.
Lemma F_5b2f4 : fetch_word AsanUbsan.M.loaded_segments (0x5b33c : word) = Some W_5b2f4.
Proof. vm_refl. Qed.
Lemma D_5b2f4 : decode_any W_5b2f4 = Some (Branch BC_LTU 19 10 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b2f8 : bv 32 := 0x00050993.
Lemma F_5b2f8 : fetch_word AsanUbsan.M.loaded_segments (0x5b340 : word) = Some W_5b2f8.
Proof. vm_refl. Qed.
Lemma D_5b2f8 : decode_any W_5b2f8 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b2fc : bv 32 := 0x00800593.
Lemma F_5b2fc : fetch_word AsanUbsan.M.loaded_segments (0x5b344 : word) = Some W_5b2fc.
Proof. vm_refl. Qed.
Lemma D_5b2fc : decode_any W_5b2fc = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b300 : bv 32 := 0x000a8513.
Lemma F_5b300 : fetch_word AsanUbsan.M.loaded_segments (0x5b348 : word) = Some W_5b300.
Proof. vm_refl. Qed.
Lemma D_5b300 : decode_any W_5b300 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b304 : bv 32 := 0xf555fee3.
Lemma F_5b304 : fetch_word AsanUbsan.M.loaded_segments (0x5b34c : word) = Some W_5b304.
Proof. vm_refl. Qed.
Lemma D_5b304 : decode_any W_5b304 = Some (Branch BC_GEU 11 21 8028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b308 : bv 32 := 0xf5dff06f.
Lemma F_5b308 : fetch_word AsanUbsan.M.loaded_segments (0x5b350 : word) = Some W_5b308.
Proof. vm_refl. Qed.
Lemma D_5b308 : decode_any W_5b308 = Some (Jal 0 2096988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b330 : bv 32 := 0x3e8310ef.
Lemma F_5b330 : fetch_word AsanUbsan.M.loaded_segments (0x5b378 : word) = Some W_5b330.
Proof. vm_refl. Qed.
Lemma D_5b330 : decode_any W_5b330 = Some (Jal 1 201704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b334 : bv 32 := 0x00050d13.
Lemma F_5b334 : fetch_word AsanUbsan.M.loaded_segments (0x5b37c : word) = Some W_5b334.
Proof. vm_refl. Qed.
Lemma D_5b334 : decode_any W_5b334 = Some (OpImm ALU_ADD 26 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b338 : bv 32 := 0x08050863.
Lemma F_5b338 : fetch_word AsanUbsan.M.loaded_segments (0x5b380 : word) = Some W_5b338.
Proof. vm_refl. Qed.
Lemma D_5b338 : decode_any W_5b338 = Some (Branch BC_EQ 10 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b33c : bv 32 := 0x0d0d0593.
Lemma F_5b33c : fetch_word AsanUbsan.M.loaded_segments (0x5b384 : word) = Some W_5b33c.
Proof. vm_refl. Qed.
Lemma D_5b33c : decode_any W_5b33c = Some (OpImm ALU_ADD 11 26 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b340 : bv 32 := 0x00800693.
Lemma F_5b340 : fetch_word AsanUbsan.M.loaded_segments (0x5b388 : word) = Some W_5b340.
Proof. vm_refl. Qed.
Lemma D_5b340 : decode_any W_5b340 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b344 : bv 32 := 0x000b0513.
Lemma F_5b344 : fetch_word AsanUbsan.M.loaded_segments (0x5b38c : word) = Some W_5b344.
Proof. vm_refl. Qed.
Lemma D_5b344 : decode_any W_5b344 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b348 : bv 32 := 0x00098613.
Lemma F_5b348 : fetch_word AsanUbsan.M.loaded_segments (0x5b390 : word) = Some W_5b348.
Proof. vm_refl. Qed.
Lemma D_5b348 : decode_any W_5b348 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b34c : bv 32 := 0x4bc040ef.
Lemma F_5b34c : fetch_word AsanUbsan.M.loaded_segments (0x5b394 : word) = Some W_5b34c.
Proof. vm_refl. Qed.
Lemma D_5b34c : decode_any W_5b34c = Some (Jal 1 17596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b350 : bv 32 := 0x00050913.
Lemma F_5b350 : fetch_word AsanUbsan.M.loaded_segments (0x5b398 : word) = Some W_5b350.
Proof. vm_refl. Qed.
Lemma D_5b350 : decode_any W_5b350 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b354 : bv 32 := 0x0c050663.
Lemma F_5b354 : fetch_word AsanUbsan.M.loaded_segments (0x5b39c : word) = Some W_5b354.
Proof. vm_refl. Qed.
Lemma D_5b354 : decode_any W_5b354 = Some (Branch BC_EQ 10 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b358 : bv 32 := 0x01490a33.
Lemma F_5b358 : fetch_word AsanUbsan.M.loaded_segments (0x5b3a0 : word) = Some W_5b358.
Proof. vm_refl. Qed.
Lemma D_5b358 : decode_any W_5b358 = Some (Op ALU_ADD 20 18 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b35c : bv 32 := 0x019a7533.
Lemma F_5b35c : fetch_word AsanUbsan.M.loaded_segments (0x5b3a4 : word) = Some W_5b35c.
Proof. vm_refl. Qed.
Lemma D_5b35c : decode_any W_5b35c = Some (Op ALU_AND 10 20 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b360 : bv 32 := 0x01298733.
Lemma F_5b360 : fetch_word AsanUbsan.M.loaded_segments (0x5b3a8 : word) = Some W_5b360.
Proof. vm_refl. Qed.
Lemma D_5b360 : decode_any W_5b360 = Some (Op ALU_ADD 14 19 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b364 : bv 32 := 0x00050663.
Lemma F_5b364 : fetch_word AsanUbsan.M.loaded_segments (0x5b3ac : word) = Some W_5b364.
Proof. vm_refl. Qed.
Lemma D_5b364 : decode_any W_5b364 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b370 : bv 32 := 0x009a0cb3.
Lemma F_5b370 : fetch_word AsanUbsan.M.loaded_segments (0x5b3b8 : word) = Some W_5b370.
Proof. vm_refl. Qed.
Lemma D_5b370 : decode_any W_5b370 = Some (Op ALU_ADD 25 20 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b374 : bv 32 := 0x5d976a63.
Lemma F_5b374 : fetch_word AsanUbsan.M.loaded_segments (0x5b3bc : word) = Some W_5b374.
Proof. vm_refl. Qed.
Lemma D_5b374 : decode_any W_5b374 = Some (Branch BC_LTU 14 25 1492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b378 : bv 32 := 0xff1a4503.
Lemma F_5b378 : fetch_word AsanUbsan.M.loaded_segments (0x5b3c0 : word) = Some W_5b378.
Proof. vm_refl. Qed.
Lemma D_5b378 : decode_any W_5b378 = Some (Load SZ1 false 10 20 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b37c : bv 32 := 0x003df593.
Lemma F_5b37c : fetch_word AsanUbsan.M.loaded_segments (0x5b3c4 : word) = Some W_5b37c.
Proof. vm_refl. Qed.
Lemma D_5b37c : decode_any W_5b37c = Some (OpImm ALU_AND 11 27 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b380 : bv 32 := 0xffc57513.
Lemma F_5b380 : fetch_word AsanUbsan.M.loaded_segments (0x5b3c8 : word) = Some W_5b380.
Proof. vm_refl. Qed.
Lemma D_5b380 : decode_any W_5b380 = Some (OpImm ALU_AND 10 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b384 : bv 32 := 0x00b56533.
Lemma F_5b384 : fetch_word AsanUbsan.M.loaded_segments (0x5b3cc : word) = Some W_5b384.
Proof. vm_refl. Qed.
Lemma D_5b384 : decode_any W_5b384 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b388 : bv 32 := 0x0204d593.
Lemma F_5b388 : fetch_word AsanUbsan.M.loaded_segments (0x5b3d0 : word) = Some W_5b388.
Proof. vm_refl. Qed.
Lemma D_5b388 : decode_any W_5b388 = Some (ShiftImm ALU_SRL 11 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b38c : bv 32 := 0x030ad613.
Lemma F_5b38c : fetch_word AsanUbsan.M.loaded_segments (0x5b3d4 : word) = Some W_5b38c.
Proof. vm_refl. Qed.
Lemma D_5b38c : decode_any W_5b38c = Some (ShiftImm ALU_SRL 12 21 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b390 : bv 32 := 0xfeaa08a3.
Lemma F_5b390 : fetch_word AsanUbsan.M.loaded_segments (0x5b3d8 : word) = Some W_5b390.
Proof. vm_refl. Qed.
Lemma D_5b390 : decode_any W_5b390 = Some (Store SZ1 20 10 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b394 : bv 32 := 0xfeba1923.
Lemma F_5b394 : fetch_word AsanUbsan.M.loaded_segments (0x5b3dc : word) = Some W_5b394.
Proof. vm_refl. Qed.
Lemma D_5b394 : decode_any W_5b394 = Some (Store SZ2 20 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b398 : bv 32 := 0xfe9a2a23.
Lemma F_5b398 : fetch_word AsanUbsan.M.loaded_segments (0x5b3e0 : word) = Some W_5b398.
Proof. vm_refl. Qed.
Lemma D_5b398 : decode_any W_5b398 = Some (Store SZ4 20 9 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b39c : bv 32 := 0x5c061463.
Lemma F_5b39c : fetch_word AsanUbsan.M.loaded_segments (0x5b3e4 : word) = Some W_5b39c.
Proof. vm_refl. Qed.
Lemma D_5b39c : decode_any W_5b39c = Some (Branch BC_NE 12 0 1480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3a0 : bv 32 := 0xff0a0a93.
Lemma F_5b3a0 : fetch_word AsanUbsan.M.loaded_segments (0x5b3e8 : word) = Some W_5b3a0.
Proof. vm_refl. Qed.
Lemma D_5b3a0 : decode_any W_5b3a0 = Some (OpImm ALU_ADD 21 20 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3a4 : bv 32 := 0x08f57513.
Lemma F_5b3a4 : fetch_word AsanUbsan.M.loaded_segments (0x5b3ec : word) = Some W_5b3a4.
Proof. vm_refl. Qed.
Lemma D_5b3a4 : decode_any W_5b3a4 = Some (OpImm ALU_AND 10 10 143, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3a8 : bv 32 := 0x01013583.
Lemma F_5b3a8 : fetch_word AsanUbsan.M.loaded_segments (0x5b3f0 : word) = Some W_5b3a8.
Proof. vm_refl. Qed.
Lemma D_5b3a8 : decode_any W_5b3a8 = Some (Load SZ8 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3ac : bv 32 := 0x00b56533.
Lemma F_5b3ac : fetch_word AsanUbsan.M.loaded_segments (0x5b3f4 : word) = Some W_5b3ac.
Proof. vm_refl. Qed.
Lemma D_5b3ac : decode_any W_5b3ac = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3b0 : bv 32 := 0x00aa80a3.
Lemma F_5b3b0 : fetch_word AsanUbsan.M.loaded_segments (0x5b3f8 : word) = Some W_5b3b0.
Proof. vm_refl. Qed.
Lemma D_5b3b0 : decode_any W_5b3b0 = Some (Store SZ1 21 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3b4 : bv 32 := 0x080d0c63.
Lemma F_5b3b4 : fetch_word AsanUbsan.M.loaded_segments (0x5b3fc : word) = Some W_5b3b4.
Proof. vm_refl. Qed.
Lemma D_5b3b4 : decode_any W_5b3b4 = Some (Branch BC_EQ 26 0 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3b8 : bv 32 := 0x000d3503.
Lemma F_5b3b8 : fetch_word AsanUbsan.M.loaded_segments (0x5b400 : word) = Some W_5b3b8.
Proof. vm_refl. Qed.
Lemma D_5b3b8 : decode_any W_5b3b8 = Some (Load SZ8 true 10 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3bc : bv 32 := 0x00852c03.
Lemma F_5b3bc : fetch_word AsanUbsan.M.loaded_segments (0x5b404 : word) = Some W_5b3bc.
Proof. vm_refl. Qed.
Lemma D_5b3bc : decode_any W_5b3bc = Some (Load SZ4 true 24 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3c0 : bv 32 := 0x020c1c13.
Lemma F_5b3c0 : fetch_word AsanUbsan.M.loaded_segments (0x5b408 : word) = Some W_5b3c0.
Proof. vm_refl. Qed.
Lemma D_5b3c0 : decode_any W_5b3c0 = Some (ShiftImm ALU_SLL 24 24 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3c4 : bv 32 := 0x08c0006f.
Lemma F_5b3c4 : fetch_word AsanUbsan.M.loaded_segments (0x5b40c : word) = Some W_5b3c4.
Proof. vm_refl. Qed.
Lemma D_5b3c4 : decode_any W_5b3c4 = Some (Jal 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b450 : bv 32 := 0x000bb503.
Lemma F_5b450 : fetch_word AsanUbsan.M.loaded_segments (0x5b498 : word) = Some W_5b450.
Proof. vm_refl. Qed.
Lemma D_5b450 : decode_any W_5b450 = Some (Load SZ8 true 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b454 : bv 32 := 0x008bb583.
Lemma F_5b454 : fetch_word AsanUbsan.M.loaded_segments (0x5b49c : word) = Some W_5b454.
Proof. vm_refl. Qed.
Lemma D_5b454 : decode_any W_5b454 = Some (Load SZ8 true 11 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b458 : bv 32 := 0x1a1470ef.
Lemma F_5b458 : fetch_word AsanUbsan.M.loaded_segments (0x5b4a0 : word) = Some W_5b458.
Proof. vm_refl. Qed.
Lemma D_5b458 : decode_any W_5b458 = Some (Jal 1 293280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b45c : bv 32 := 0x02051513.
Lemma F_5b45c : fetch_word AsanUbsan.M.loaded_segments (0x5b4a4 : word) = Some W_5b45c.
Proof. vm_refl. Qed.
Lemma D_5b45c : decode_any W_5b45c = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b460 : bv 32 := 0x02055513.
Lemma F_5b460 : fetch_word AsanUbsan.M.loaded_segments (0x5b4a8 : word) = Some W_5b460.
Proof. vm_refl. Qed.
Lemma D_5b460 : decode_any W_5b460 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b464 : bv 32 := 0x00ac6533.
Lemma F_5b464 : fetch_word AsanUbsan.M.loaded_segments (0x5b4ac : word) = Some W_5b464.
Proof. vm_refl. Qed.
Lemma D_5b464 : decode_any W_5b464 = Some (Op ALU_OR 10 24 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b468 : bv 32 := 0x00aab423.
Lemma F_5b468 : fetch_word AsanUbsan.M.loaded_segments (0x5b4b0 : word) = Some W_5b468.
Proof. vm_refl. Qed.
Lemma D_5b468 : decode_any W_5b468 = Some (Store SZ8 21 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b46c : bv 32 := 0x02040063.
Lemma F_5b46c : fetch_word AsanUbsan.M.loaded_segments (0x5b4b4 : word) = Some W_5b46c.
Proof. vm_refl. Qed.
Lemma D_5b46c : decode_any W_5b46c = Some (Branch BC_EQ 8 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b470 : bv 32 := 0x00109517.
Lemma F_5b470 : fetch_word AsanUbsan.M.loaded_segments (0x5b4b8 : word) = Some W_5b470.
Proof. vm_refl. Qed.
Lemma D_5b470 : decode_any W_5b470 = Some (Auipc 10 265, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b474 : bv 32 := 0x06053503.
Lemma F_5b474 : fetch_word AsanUbsan.M.loaded_segments (0x5b4bc : word) = Some W_5b474.
Proof. vm_refl. Qed.
Lemma D_5b474 : decode_any W_5b474 = Some (Load SZ8 true 10 10 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b478 : bv 32 := 0x00053503.
Lemma F_5b478 : fetch_word AsanUbsan.M.loaded_segments (0x5b4c0 : word) = Some W_5b478.
Proof. vm_refl. Qed.
Lemma D_5b478 : decode_any W_5b478 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b47c : bv 32 := 0x00395593.
Lemma F_5b47c : fetch_word AsanUbsan.M.loaded_segments (0x5b4c4 : word) = Some W_5b47c.
Proof. vm_refl. Qed.
Lemma D_5b47c : decode_any W_5b47c = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b480 : bv 32 := 0x00b50533.
Lemma F_5b480 : fetch_word AsanUbsan.M.loaded_segments (0x5b4c8 : word) = Some W_5b480.
Proof. vm_refl. Qed.
Lemma D_5b480 : decode_any W_5b480 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b484 : bv 32 := 0x00054503.
Lemma F_5b484 : fetch_word AsanUbsan.M.loaded_segments (0x5b4cc : word) = Some W_5b484.
Proof. vm_refl. Qed.
Lemma D_5b484 : decode_any W_5b484 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b488 : bv 32 := 0x0c051063.
Lemma F_5b488 : fetch_word AsanUbsan.M.loaded_segments (0x5b4d0 : word) = Some W_5b488.
Proof. vm_refl. Qed.
Lemma D_5b488 : decode_any W_5b488 = Some (Branch BC_NE 10 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b48c : bv 32 := 0x020b3503.
Lemma F_5b48c : fetch_word AsanUbsan.M.loaded_segments (0x5b4d4 : word) = Some W_5b48c.
Proof. vm_refl. Qed.
Lemma D_5b48c : decode_any W_5b48c = Some (Load SZ8 true 10 22 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b490 : bv 32 := 0x02a96c63.
Lemma F_5b490 : fetch_word AsanUbsan.M.loaded_segments (0x5b4d8 : word) = Some W_5b490.
Proof. vm_refl. Qed.
Lemma D_5b490 : decode_any W_5b490 = Some (Branch BC_LTU 18 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b494 : bv 32 := 0x00100593.
Lemma F_5b494 : fetch_word AsanUbsan.M.loaded_segments (0x5b4dc : word) = Some W_5b494.
Proof. vm_refl. Qed.
Lemma D_5b494 : decode_any W_5b494 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b498 : bv 32 := 0x02559593.
Lemma F_5b498 : fetch_word AsanUbsan.M.loaded_segments (0x5b4e0 : word) = Some W_5b498.
Proof. vm_refl. Qed.
Lemma D_5b498 : decode_any W_5b498 = Some (ShiftImm ALU_SLL 11 11 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b49c : bv 32 := 0x00b505b3.
Lemma F_5b49c : fetch_word AsanUbsan.M.loaded_segments (0x5b4e4 : word) = Some W_5b49c.
Proof. vm_refl. Qed.
Lemma D_5b49c : decode_any W_5b49c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b4a0 : bv 32 := 0x02b97463.
Lemma F_5b4a0 : fetch_word AsanUbsan.M.loaded_segments (0x5b4e8 : word) = Some W_5b4a0.
Proof. vm_refl. Qed.
Lemma D_5b4a0 : decode_any W_5b4a0 = Some (Branch BC_GEU 18 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b4c8 : bv 32 := 0x040b3503.
Lemma F_5b4c8 : fetch_word AsanUbsan.M.loaded_segments (0x5b510 : word) = Some W_5b4c8.
Proof. vm_refl. Qed.
Lemma D_5b4c8 : decode_any W_5b4c8 = Some (Load SZ8 true 10 22 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b4cc : bv 32 := 0xfff50593.
Lemma F_5b4cc : fetch_word AsanUbsan.M.loaded_segments (0x5b514 : word) = Some W_5b4cc.
Proof. vm_refl. Qed.
Lemma D_5b4cc : decode_any W_5b4cc = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b4d0 : bv 32 := 0x0125f633.
Lemma F_5b4d0 : fetch_word AsanUbsan.M.loaded_segments (0x5b518 : word) = Some W_5b4d0.
Proof. vm_refl. Qed.
Lemma D_5b4d0 : decode_any W_5b4d0 = Some (Op ALU_AND 12 11 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b4d4 : bv 32 := 0x52061663.
Lemma F_5b4d4 : fetch_word AsanUbsan.M.loaded_segments (0x5b51c : word) = Some W_5b4d4.
Proof. vm_refl. Qed.
Lemma D_5b4d4 : decode_any W_5b4d4 = Some (Branch BC_NE 12 0 1324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b4d8 : bv 32 := 0x00b57633.
Lemma F_5b4d8 : fetch_word AsanUbsan.M.loaded_segments (0x5b520 : word) = Some W_5b4d8.
Proof. vm_refl. Qed.
Lemma D_5b4d8 : decode_any W_5b4d8 = Some (Op ALU_AND 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b4dc : bv 32 := 0x54061663.
Lemma F_5b4dc : fetch_word AsanUbsan.M.loaded_segments (0x5b524 : word) = Some W_5b4dc.
Proof. vm_refl. Qed.
Lemma D_5b4dc : decode_any W_5b4dc = Some (Branch BC_NE 12 0 1356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b4e0 : bv 32 := 0x40a90633.
Lemma F_5b4e0 : fetch_word AsanUbsan.M.loaded_segments (0x5b528 : word) = Some W_5b4e0.
Proof. vm_refl. Qed.
Lemma D_5b4e0 : decode_any W_5b4e0 = Some (Op ALU_SUB 12 18 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b4e4 : bv 32 := 0x01063603.
Lemma F_5b4e4 : fetch_word AsanUbsan.M.loaded_segments (0x5b52c : word) = Some W_5b4e4.
Proof. vm_refl. Qed.
Lemma D_5b4e4 : decode_any W_5b4e4 = Some (Load SZ8 true 12 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b4e8 : bv 32 := 0x00b605b3.
Lemma F_5b4e8 : fetch_word AsanUbsan.M.loaded_segments (0x5b530 : word) = Some W_5b4e8.
Proof. vm_refl. Qed.
Lemma D_5b4e8 : decode_any W_5b4e8 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b4ec : bv 32 := 0x40a00433.
Lemma F_5b4ec : fetch_word AsanUbsan.M.loaded_segments (0x5b534 : word) = Some W_5b4ec.
Proof. vm_refl. Qed.
Lemma D_5b4ec : decode_any W_5b4ec = Some (Op ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b4f0 : bv 32 := 0x0085f433.
Lemma F_5b4f0 : fetch_word AsanUbsan.M.loaded_segments (0x5b538 : word) = Some W_5b4f0.
Proof. vm_refl. Qed.
Lemma D_5b4f0 : decode_any W_5b4f0 = Some (Op ALU_AND 8 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b4f4 : bv 32 := 0x0280006f.
Lemma F_5b4f4 : fetch_word AsanUbsan.M.loaded_segments (0x5b53c : word) = Some W_5b4f4.
Proof. vm_refl. Qed.
Lemma D_5b4f4 : decode_any W_5b4f4 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b51c : bv 32 := 0x007c8c93.
Lemma F_5b51c : fetch_word AsanUbsan.M.loaded_segments (0x5b564 : word) = Some W_5b51c.
Proof. vm_refl. Qed.
Lemma D_5b51c : decode_any W_5b51c = Some (OpImm ALU_ADD 25 25 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b520 : bv 32 := 0xff8cfb13.
Lemma F_5b520 : fetch_word AsanUbsan.M.loaded_segments (0x5b568 : word) = Some W_5b520.
Proof. vm_refl. Qed.
Lemma D_5b520 : decode_any W_5b520 = Some (OpImm ALU_AND 22 25 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b524 : bv 32 := 0x412a05b3.
Lemma F_5b524 : fetch_word AsanUbsan.M.loaded_segments (0x5b56c : word) = Some W_5b524.
Proof. vm_refl. Qed.
Lemma D_5b524 : decode_any W_5b524 = Some (Op ALU_SUB 11 20 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b528 : bv 32 := 0x0fa00613.
Lemma F_5b528 : fetch_word AsanUbsan.M.loaded_segments (0x5b570 : word) = Some W_5b528.
Proof. vm_refl. Qed.
Lemma D_5b528 : decode_any W_5b528 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b52c : bv 32 := 0x00090513.
Lemma F_5b52c : fetch_word AsanUbsan.M.loaded_segments (0x5b574 : word) = Some W_5b52c.
Proof. vm_refl. Qed.
Lemma D_5b52c : decode_any W_5b52c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b530 : bv 32 := 0x43c280ef.
Lemma F_5b530 : fetch_word AsanUbsan.M.loaded_segments (0x5b578 : word) = Some W_5b530.
Proof. vm_refl. Qed.
Lemma D_5b530 : decode_any W_5b530 = Some (Jal 1 164924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b534 : bv 32 := 0x416905b3.
Lemma F_5b534 : fetch_word AsanUbsan.M.loaded_segments (0x5b57c : word) = Some W_5b534.
Proof. vm_refl. Qed.
Lemma D_5b534 : decode_any W_5b534 = Some (Op ALU_SUB 11 18 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b538 : bv 32 := 0x008585b3.
Lemma F_5b538 : fetch_word AsanUbsan.M.loaded_segments (0x5b580 : word) = Some W_5b538.
Proof. vm_refl. Qed.
Lemma D_5b538 : decode_any W_5b538 = Some (Op ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b53c : bv 32 := 0x0fa00613.
Lemma F_5b53c : fetch_word AsanUbsan.M.loaded_segments (0x5b584 : word) = Some W_5b53c.
Proof. vm_refl. Qed.
Lemma D_5b53c : decode_any W_5b53c = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b540 : bv 32 := 0x000b0513.
Lemma F_5b540 : fetch_word AsanUbsan.M.loaded_segments (0x5b588 : word) = Some W_5b540.
Proof. vm_refl. Qed.
Lemma D_5b540 : decode_any W_5b540 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b544 : bv 32 := 0x428280ef.
Lemma F_5b544 : fetch_word AsanUbsan.M.loaded_segments (0x5b58c : word) = Some W_5b544.
Proof. vm_refl. Qed.
Lemma D_5b544 : decode_any W_5b544 = Some (Jal 1 164904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b548 : bv 32 := 0xfff80537.
Lemma F_5b548 : fetch_word AsanUbsan.M.loaded_segments (0x5b590 : word) = Some W_5b548.
Proof. vm_refl. Qed.
Lemma D_5b548 : decode_any W_5b548 = Some (Lui 10 1048448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b54c : bv 32 := 0x01055513.
Lemma F_5b54c : fetch_word AsanUbsan.M.loaded_segments (0x5b594 : word) = Some W_5b54c.
Proof. vm_refl. Qed.
Lemma D_5b54c : decode_any W_5b54c = Some (ShiftImm ALU_SRL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b550 : bv 32 := 0x00a4fb33.
Lemma F_5b550 : fetch_word AsanUbsan.M.loaded_segments (0x5b598 : word) = Some W_5b550.
Proof. vm_refl. Qed.
Lemma D_5b550 : decode_any W_5b550 = Some (Op ALU_AND 22 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b554 : bv 32 := 0x000b0a63.
Lemma F_5b554 : fetch_word AsanUbsan.M.loaded_segments (0x5b59c : word) = Some W_5b554.
Proof. vm_refl. Qed.
Lemma D_5b554 : decode_any W_5b554 = Some (Branch BC_EQ 22 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b558 : bv 32 := 0x000a0513.
Lemma F_5b558 : fetch_word AsanUbsan.M.loaded_segments (0x5b5a0 : word) = Some W_5b558.
Proof. vm_refl. Qed.
Lemma D_5b558 : decode_any W_5b558 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b55c : bv 32 := 0x000b0593.
Lemma F_5b55c : fetch_word AsanUbsan.M.loaded_segments (0x5b5a4 : word) = Some W_5b55c.
Proof. vm_refl. Qed.
Lemma D_5b55c : decode_any W_5b55c = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b560 : bv 32 := 0x00000613.
Lemma F_5b560 : fetch_word AsanUbsan.M.loaded_segments (0x5b5a8 : word) = Some W_5b560.
Proof. vm_refl. Qed.
Lemma D_5b560 : decode_any W_5b560 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b564 : bv 32 := 0x408280ef.
Lemma F_5b564 : fetch_word AsanUbsan.M.loaded_segments (0x5b5ac : word) = Some W_5b564.
Proof. vm_refl. Qed.
Lemma D_5b564 : decode_any W_5b564 = Some (Jal 1 164872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b568 : bv 32 := 0x09648a63.
Lemma F_5b568 : fetch_word AsanUbsan.M.loaded_segments (0x5b5b0 : word) = Some W_5b568.
Proof. vm_refl. Qed.
Lemma D_5b568 : decode_any W_5b568 = Some (Branch BC_EQ 9 22 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b56c : bv 32 := 0x3ec280ef.
Lemma F_5b56c : fetch_word AsanUbsan.M.loaded_segments (0x5b5b4 : word) = Some W_5b56c.
Proof. vm_refl. Qed.
Lemma D_5b56c : decode_any W_5b56c = Some (Jal 1 164844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b570 : bv 32 := 0x08050663.
Lemma F_5b570 : fetch_word AsanUbsan.M.loaded_segments (0x5b5b8 : word) = Some W_5b570.
Proof. vm_refl. Qed.
Lemma D_5b570 : decode_any W_5b570 = Some (Branch BC_EQ 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b574 : bv 32 := 0x00109517.
Lemma F_5b574 : fetch_word AsanUbsan.M.loaded_segments (0x5b5bc : word) = Some W_5b574.
Proof. vm_refl. Qed.
Lemma D_5b574 : decode_any W_5b574 = Some (Auipc 10 265, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b578 : bv 32 := 0xf5c53503.
Lemma F_5b578 : fetch_word AsanUbsan.M.loaded_segments (0x5b5c0 : word) = Some W_5b578.
Proof. vm_refl. Qed.
Lemma D_5b578 : decode_any W_5b578 = Some (Load SZ8 true 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b57c : bv 32 := 0x00053503.
Lemma F_5b57c : fetch_word AsanUbsan.M.loaded_segments (0x5b5c4 : word) = Some W_5b57c.
Proof. vm_refl. Qed.
Lemma D_5b57c : decode_any W_5b57c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b580 : bv 32 := 0x016a0b33.
Lemma F_5b580 : fetch_word AsanUbsan.M.loaded_segments (0x5b5c8 : word) = Some W_5b580.
Proof. vm_refl. Qed.
Lemma D_5b580 : decode_any W_5b580 = Some (Op ALU_ADD 22 20 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b584 : bv 32 := 0xfff50593.
Lemma F_5b584 : fetch_word AsanUbsan.M.loaded_segments (0x5b5cc : word) = Some W_5b584.
Proof. vm_refl. Qed.
Lemma D_5b584 : decode_any W_5b584 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b588 : bv 32 := 0x00b53633.
Lemma F_5b588 : fetch_word AsanUbsan.M.loaded_segments (0x5b5d0 : word) = Some W_5b588.
Proof. vm_refl. Qed.
Lemma D_5b588 : decode_any W_5b588 = Some (Op ALU_SLTU 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b58c : bv 32 := 0xfff60613.
Lemma F_5b58c : fetch_word AsanUbsan.M.loaded_segments (0x5b5d4 : word) = Some W_5b58c.
Proof. vm_refl. Qed.
Lemma D_5b58c : decode_any W_5b58c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b590 : bv 32 := 0x00b67633.
Lemma F_5b590 : fetch_word AsanUbsan.M.loaded_segments (0x5b5d8 : word) = Some W_5b590.
Proof. vm_refl. Qed.
Lemma D_5b590 : decode_any W_5b590 = Some (Op ALU_AND 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b594 : bv 32 := 0x05667263.
Lemma F_5b594 : fetch_word AsanUbsan.M.loaded_segments (0x5b5dc : word) = Some W_5b594.
Proof. vm_refl. Qed.
Lemma D_5b594 : decode_any W_5b594 = Some (Branch BC_GEU 12 22 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b598 : bv 32 := 0x00109617.
Lemma F_5b598 : fetch_word AsanUbsan.M.loaded_segments (0x5b5e0 : word) = Some W_5b598.
Proof. vm_refl. Qed.
Lemma D_5b598 : decode_any W_5b598 = Some (Auipc 12 265, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b59c : bv 32 := 0xf4063603.
Lemma F_5b59c : fetch_word AsanUbsan.M.loaded_segments (0x5b5e4 : word) = Some W_5b59c.
Proof. vm_refl. Qed.
Lemma D_5b59c : decode_any W_5b59c = Some (Load SZ8 true 12 12 3904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5a0 : bv 32 := 0x00109697.
Lemma F_5b5a0 : fetch_word AsanUbsan.M.loaded_segments (0x5b5e8 : word) = Some W_5b5a0.
Proof. vm_refl. Qed.
Lemma D_5b5a0 : decode_any W_5b5a0 = Some (Auipc 13 265, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5a4 : bv 32 := 0xf406b683.
Lemma F_5b5a4 : fetch_word AsanUbsan.M.loaded_segments (0x5b5ec : word) = Some W_5b5a4.
Proof. vm_refl. Qed.
Lemma D_5b5a4 : decode_any W_5b5a4 = Some (Load SZ8 true 13 13 3904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5a8 : bv 32 := 0x00063783.
Lemma F_5b5a8 : fetch_word AsanUbsan.M.loaded_segments (0x5b5f0 : word) = Some W_5b5a8.
Proof. vm_refl. Qed.
Lemma D_5b5a8 : decode_any W_5b5a8 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5ac : bv 32 := 0x0006b603.
Lemma F_5b5ac : fetch_word AsanUbsan.M.loaded_segments (0x5b5f4 : word) = Some W_5b5ac.
Proof. vm_refl. Qed.
Lemma D_5b5ac : decode_any W_5b5ac = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5b0 : bv 32 := 0xfff78713.
Lemma F_5b5b0 : fetch_word AsanUbsan.M.loaded_segments (0x5b5f8 : word) = Some W_5b5b0.
Proof. vm_refl. Qed.
Lemma D_5b5b0 : decode_any W_5b5b0 = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5b4 : bv 32 := 0x01677463.
Lemma F_5b5b4 : fetch_word AsanUbsan.M.loaded_segments (0x5b5fc : word) = Some W_5b5b4.
Proof. vm_refl. Qed.
Lemma D_5b5b4 : decode_any W_5b5b4 = Some (Branch BC_GEU 14 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5bc : bv 32 := 0x00109697.
Lemma F_5b5bc : fetch_word AsanUbsan.M.loaded_segments (0x5b604 : word) = Some W_5b5bc.
Proof. vm_refl. Qed.
Lemma D_5b5bc : decode_any W_5b5bc = Some (Auipc 13 265, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5c0 : bv 32 := 0xf2c6b683.
Lemma F_5b5c0 : fetch_word AsanUbsan.M.loaded_segments (0x5b608 : word) = Some W_5b5c0.
Proof. vm_refl. Qed.
Lemma D_5b5c0 : decode_any W_5b5c0 = Some (Load SZ8 true 13 13 3884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5c4 : bv 32 := 0x0006b883.
Lemma F_5b5c4 : fetch_word AsanUbsan.M.loaded_segments (0x5b60c : word) = Some W_5b5c4.
Proof. vm_refl. Qed.
Lemma D_5b5c4 : decode_any W_5b5c4 = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5c8 : bv 32 := 0x0038d693.
Lemma F_5b5c8 : fetch_word AsanUbsan.M.loaded_segments (0x5b610 : word) = Some W_5b5c8.
Proof. vm_refl. Qed.
Lemma D_5b5c8 : decode_any W_5b5c8 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5cc : bv 32 := 0x00a68833.
Lemma F_5b5cc : fetch_word AsanUbsan.M.loaded_segments (0x5b614 : word) = Some W_5b5cc.
Proof. vm_refl. Qed.
Lemma D_5b5cc : decode_any W_5b5cc = Some (Op ALU_ADD 16 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5d0 : bv 32 := 0x2568ea63.
Lemma F_5b5d0 : fetch_word AsanUbsan.M.loaded_segments (0x5b618 : word) = Some W_5b5d0.
Proof. vm_refl. Qed.
Lemma D_5b5d0 : decode_any W_5b5d0 = Some (Branch BC_LTU 17 22 596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5d4 : bv 32 := 0x25687863.
Lemma F_5b5d4 : fetch_word AsanUbsan.M.loaded_segments (0x5b61c : word) = Some W_5b5d4.
Proof. vm_refl. Qed.
Lemma D_5b5d4 : decode_any W_5b5d4 = Some (Branch BC_GEU 16 22 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5d8 : bv 32 := 0x00109597.
Lemma F_5b5d8 : fetch_word AsanUbsan.M.loaded_segments (0x5b620 : word) = Some W_5b5d8.
Proof. vm_refl. Qed.
Lemma D_5b5d8 : decode_any W_5b5d8 = Some (Auipc 11 265, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5dc : bv 32 := 0xef05b583.
Lemma F_5b5dc : fetch_word AsanUbsan.M.loaded_segments (0x5b624 : word) = Some W_5b5dc.
Proof. vm_refl. Qed.
Lemma D_5b5dc : decode_any W_5b5dc = Some (Load SZ8 true 11 11 3824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5e0 : bv 32 := 0x0555c583.
Lemma F_5b5e0 : fetch_word AsanUbsan.M.loaded_segments (0x5b628 : word) = Some W_5b5e0.
Proof. vm_refl. Qed.
Lemma D_5b5e0 : decode_any W_5b5e0 = Some (Load SZ1 false 11 11 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5e4 : bv 32 := 0x003b5613.
Lemma F_5b5e4 : fetch_word AsanUbsan.M.loaded_segments (0x5b62c : word) = Some W_5b5e4.
Proof. vm_refl. Qed.
Lemma D_5b5e4 : decode_any W_5b5e4 = Some (ShiftImm ALU_SRL 12 22 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5e8 : bv 32 := 0x00c50533.
Lemma F_5b5e8 : fetch_word AsanUbsan.M.loaded_segments (0x5b630 : word) = Some W_5b5e8.
Proof. vm_refl. Qed.
Lemma D_5b5e8 : decode_any W_5b5e8 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5ec : bv 32 := 0x40b005bb.
Lemma F_5b5ec : fetch_word AsanUbsan.M.loaded_segments (0x5b634 : word) = Some W_5b5ec.
Proof. vm_refl. Qed.
Lemma D_5b5ec : decode_any W_5b5ec = Some (Op32 ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5f0 : bv 32 := 0x00b4f5b3.
Lemma F_5b5f0 : fetch_word AsanUbsan.M.loaded_segments (0x5b638 : word) = Some W_5b5f0.
Proof. vm_refl. Qed.
Lemma D_5b5f0 : decode_any W_5b5f0 = Some (Op ALU_AND 11 9 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5f4 : bv 32 := 0x0075f593.
Lemma F_5b5f4 : fetch_word AsanUbsan.M.loaded_segments (0x5b63c : word) = Some W_5b5f4.
Proof. vm_refl. Qed.
Lemma D_5b5f4 : decode_any W_5b5f4 = Some (OpImm ALU_AND 11 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5f8 : bv 32 := 0x00b50023.
Lemma F_5b5f8 : fetch_word AsanUbsan.M.loaded_segments (0x5b640 : word) = Some W_5b5f8.
Proof. vm_refl. Qed.
Lemma D_5b5f8 : decode_any W_5b5f8 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b5fc : bv 32 := 0x2e8300ef.
Lemma F_5b5fc : fetch_word AsanUbsan.M.loaded_segments (0x5b644 : word) = Some W_5b5fc.
Proof. vm_refl. Qed.
Lemma D_5b5fc : decode_any W_5b5fc = Some (Jal 1 197352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b600 : bv 32 := 0x01053583.
Lemma F_5b600 : fetch_word AsanUbsan.M.loaded_segments (0x5b648 : word) = Some W_5b600.
Proof. vm_refl. Qed.
Lemma D_5b600 : decode_any W_5b600 = Some (Load SZ8 true 11 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b604 : bv 32 := 0x00053603.
Lemma F_5b604 : fetch_word AsanUbsan.M.loaded_segments (0x5b64c : word) = Some W_5b604.
Proof. vm_refl. Qed.
Lemma D_5b604 : decode_any W_5b604 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b608 : bv 32 := 0x00853683.
Lemma F_5b608 : fetch_word AsanUbsan.M.loaded_segments (0x5b650 : word) = Some W_5b608.
Proof. vm_refl. Qed.
Lemma D_5b608 : decode_any W_5b608 = Some (Load SZ8 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b60c : bv 32 := 0x40998733.
Lemma F_5b60c : fetch_word AsanUbsan.M.loaded_segments (0x5b654 : word) = Some W_5b60c.
Proof. vm_refl. Qed.
Lemma D_5b60c : decode_any W_5b60c = Some (Op ALU_SUB 14 19 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b610 : bv 32 := 0x00b705b3.
Lemma F_5b610 : fetch_word AsanUbsan.M.loaded_segments (0x5b658 : word) = Some W_5b610.
Proof. vm_refl. Qed.
Lemma D_5b610 : decode_any W_5b610 = Some (Op ALU_ADD 11 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b614 : bv 32 := 0x00010737.
Lemma F_5b614 : fetch_word AsanUbsan.M.loaded_segments (0x5b65c : word) = Some W_5b614.
Proof. vm_refl. Qed.
Lemma D_5b614 : decode_any W_5b614 = Some (Lui 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b618 : bv 32 := 0x0017071b.
Lemma F_5b618 : fetch_word AsanUbsan.M.loaded_segments (0x5b660 : word) = Some W_5b618.
Proof. vm_refl. Qed.
Lemma D_5b618 : decode_any W_5b618 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b61c : bv 32 := 0x00160613.
Lemma F_5b61c : fetch_word AsanUbsan.M.loaded_segments (0x5b664 : word) = Some W_5b61c.
Proof. vm_refl. Qed.
Lemma D_5b61c : decode_any W_5b61c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b620 : bv 32 := 0x009686b3.
Lemma F_5b620 : fetch_word AsanUbsan.M.loaded_segments (0x5b668 : word) = Some W_5b620.
Proof. vm_refl. Qed.
Lemma D_5b620 : decode_any W_5b620 = Some (Op ALU_ADD 13 13 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b624 : bv 32 := 0x00c53023.
Lemma F_5b624 : fetch_word AsanUbsan.M.loaded_segments (0x5b66c : word) = Some W_5b624.
Proof. vm_refl. Qed.
Lemma D_5b624 : decode_any W_5b624 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b628 : bv 32 := 0x00d53423.
Lemma F_5b628 : fetch_word AsanUbsan.M.loaded_segments (0x5b670 : word) = Some W_5b628.
Proof. vm_refl. Qed.
Lemma D_5b628 : decode_any W_5b628 = Some (Store SZ8 10 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b62c : bv 32 := 0x00b53823.
Lemma F_5b62c : fetch_word AsanUbsan.M.loaded_segments (0x5b674 : word) = Some W_5b62c.
Proof. vm_refl. Qed.
Lemma D_5b62c : decode_any W_5b62c = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b630 : bv 32 := 0x00e9ee63.
Lemma F_5b630 : fetch_word AsanUbsan.M.loaded_segments (0x5b678 : word) = Some W_5b630.
Proof. vm_refl. Qed.
Lemma D_5b630 : decode_any W_5b630 = Some (Branch BC_LTU 19 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b634 : bv 32 := 0x06853583.
Lemma F_5b634 : fetch_word AsanUbsan.M.loaded_segments (0x5b67c : word) = Some W_5b634.
Proof. vm_refl. Qed.
Lemma D_5b634 : decode_any W_5b634 = Some (Load SZ8 true 11 10 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b638 : bv 32 := 0x00158593.
Lemma F_5b638 : fetch_word AsanUbsan.M.loaded_segments (0x5b680 : word) = Some W_5b638.
Proof. vm_refl. Qed.
Lemma D_5b638 : decode_any W_5b638 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b63c : bv 32 := 0x06b53423.
Lemma F_5b63c : fetch_word AsanUbsan.M.loaded_segments (0x5b684 : word) = Some W_5b63c.
Proof. vm_refl. Qed.
Lemma D_5b63c : decode_any W_5b63c = Some (Store SZ8 10 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b640 : bv 32 := 0x00813503.
Lemma F_5b640 : fetch_word AsanUbsan.M.loaded_segments (0x5b688 : word) = Some W_5b640.
Proof. vm_refl. Qed.
Lemma D_5b640 : decode_any W_5b640 = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b644 : bv 32 := 0x10051c63.
Lemma F_5b644 : fetch_word AsanUbsan.M.loaded_segments (0x5b68c : word) = Some W_5b644.
Proof. vm_refl. Qed.
Lemma D_5b644 : decode_any W_5b644 = Some (Branch BC_NE 10 0 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b64c : bv 32 := 0x20000593.
Lemma F_5b64c : fetch_word AsanUbsan.M.loaded_segments (0x5b694 : word) = Some W_5b64c.
Proof. vm_refl. Qed.
Lemma D_5b64c : decode_any W_5b64c = Some (OpImm ALU_ADD 11 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b650 : bv 32 := 0x07050513.
Lemma F_5b650 : fetch_word AsanUbsan.M.loaded_segments (0x5b698 : word) = Some W_5b650.
Proof. vm_refl. Qed.
Lemma D_5b650 : decode_any W_5b650 = Some (OpImm ALU_ADD 10 10 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b654 : bv 32 := 0x0135e863.
Lemma F_5b654 : fetch_word AsanUbsan.M.loaded_segments (0x5b69c : word) = Some W_5b654.
Proof. vm_refl. Qed.
Lemma D_5b654 : decode_any W_5b654 = Some (Branch BC_LTU 11 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b658 : bv 32 := 0x01f98593.
Lemma F_5b658 : fetch_word AsanUbsan.M.loaded_segments (0x5b6a0 : word) = Some W_5b658.
Proof. vm_refl. Qed.
Lemma D_5b658 : decode_any W_5b658 = Some (OpImm ALU_ADD 11 19 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b65c : bv 32 := 0x0055d593.
Lemma F_5b65c : fetch_word AsanUbsan.M.loaded_segments (0x5b6a4 : word) = Some W_5b65c.
Proof. vm_refl. Qed.
Lemma D_5b65c : decode_any W_5b65c = Some (ShiftImm ALU_SRL 11 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b660 : bv 32 := 0x0e00006f.
Lemma F_5b660 : fetch_word AsanUbsan.M.loaded_segments (0x5b6a8 : word) = Some W_5b660.
Proof. vm_refl. Qed.
Lemma D_5b660 : decode_any W_5b660 = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b664 : bv 32 := 0x0019d593.
Lemma F_5b664 : fetch_word AsanUbsan.M.loaded_segments (0x5b6ac : word) = Some W_5b664.
Proof. vm_refl. Qed.
Lemma D_5b664 : decode_any W_5b664 = Some (ShiftImm ALU_SRL 11 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b668 : bv 32 := 0x55555637.
Lemma F_5b668 : fetch_word AsanUbsan.M.loaded_segments (0x5b6b0 : word) = Some W_5b668.
Proof. vm_refl. Qed.
Lemma D_5b668 : decode_any W_5b668 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b66c : bv 32 := 0x333336b7.
Lemma F_5b66c : fetch_word AsanUbsan.M.loaded_segments (0x5b6b4 : word) = Some W_5b66c.
Proof. vm_refl. Qed.
Lemma D_5b66c : decode_any W_5b66c = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b670 : bv 32 := 0x0f0f1737.
Lemma F_5b670 : fetch_word AsanUbsan.M.loaded_segments (0x5b6b8 : word) = Some W_5b670.
Proof. vm_refl. Qed.
Lemma D_5b670 : decode_any W_5b670 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b674 : bv 32 := 0x010107b7.
Lemma F_5b674 : fetch_word AsanUbsan.M.loaded_segments (0x5b6bc : word) = Some W_5b674.
Proof. vm_refl. Qed.
Lemma D_5b674 : decode_any W_5b674 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b678 : bv 32 := 0x00b9e5b3.
Lemma F_5b678 : fetch_word AsanUbsan.M.loaded_segments (0x5b6c0 : word) = Some W_5b678.
Proof. vm_refl. Qed.
Lemma D_5b678 : decode_any W_5b678 = Some (Op ALU_OR 11 19 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b67c : bv 32 := 0x5556061b.
Lemma F_5b67c : fetch_word AsanUbsan.M.loaded_segments (0x5b6c4 : word) = Some W_5b67c.
Proof. vm_refl. Qed.
Lemma D_5b67c : decode_any W_5b67c = Some (OpImm32 12 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b680 : bv 32 := 0x3336869b.
Lemma F_5b680 : fetch_word AsanUbsan.M.loaded_segments (0x5b6c8 : word) = Some W_5b680.
Proof. vm_refl. Qed.
Lemma D_5b680 : decode_any W_5b680 = Some (OpImm32 13 13 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b684 : bv 32 := 0xf0f7071b.
Lemma F_5b684 : fetch_word AsanUbsan.M.loaded_segments (0x5b6cc : word) = Some W_5b684.
Proof. vm_refl. Qed.
Lemma D_5b684 : decode_any W_5b684 = Some (OpImm32 14 14 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b688 : bv 32 := 0x1017879b.
Lemma F_5b688 : fetch_word AsanUbsan.M.loaded_segments (0x5b6d0 : word) = Some W_5b688.
Proof. vm_refl. Qed.
Lemma D_5b688 : decode_any W_5b688 = Some (OpImm32 15 15 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b68c : bv 32 := 0x0025d813.
Lemma F_5b68c : fetch_word AsanUbsan.M.loaded_segments (0x5b6d4 : word) = Some W_5b68c.
Proof. vm_refl. Qed.
Lemma D_5b68c : decode_any W_5b68c = Some (ShiftImm ALU_SRL 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b690 : bv 32 := 0x0105e5b3.
Lemma F_5b690 : fetch_word AsanUbsan.M.loaded_segments (0x5b6d8 : word) = Some W_5b690.
Proof. vm_refl. Qed.
Lemma D_5b690 : decode_any W_5b690 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b694 : bv 32 := 0x02061813.
Lemma F_5b694 : fetch_word AsanUbsan.M.loaded_segments (0x5b6dc : word) = Some W_5b694.
Proof. vm_refl. Qed.
Lemma D_5b694 : decode_any W_5b694 = Some (ShiftImm ALU_SLL 16 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b698 : bv 32 := 0x01060633.
Lemma F_5b698 : fetch_word AsanUbsan.M.loaded_segments (0x5b6e0 : word) = Some W_5b698.
Proof. vm_refl. Qed.
Lemma D_5b698 : decode_any W_5b698 = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b69c : bv 32 := 0x02069813.
Lemma F_5b69c : fetch_word AsanUbsan.M.loaded_segments (0x5b6e4 : word) = Some W_5b69c.
Proof. vm_refl. Qed.
Lemma D_5b69c : decode_any W_5b69c = Some (ShiftImm ALU_SLL 16 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6a0 : bv 32 := 0x010686b3.
Lemma F_5b6a0 : fetch_word AsanUbsan.M.loaded_segments (0x5b6e8 : word) = Some W_5b6a0.
Proof. vm_refl. Qed.
Lemma D_5b6a0 : decode_any W_5b6a0 = Some (Op ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6a4 : bv 32 := 0x02071813.
Lemma F_5b6a4 : fetch_word AsanUbsan.M.loaded_segments (0x5b6ec : word) = Some W_5b6a4.
Proof. vm_refl. Qed.
Lemma D_5b6a4 : decode_any W_5b6a4 = Some (ShiftImm ALU_SLL 16 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6a8 : bv 32 := 0x01070733.
Lemma F_5b6a8 : fetch_word AsanUbsan.M.loaded_segments (0x5b6f0 : word) = Some W_5b6a8.
Proof. vm_refl. Qed.
Lemma D_5b6a8 : decode_any W_5b6a8 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6ac : bv 32 := 0x02079813.
Lemma F_5b6ac : fetch_word AsanUbsan.M.loaded_segments (0x5b6f4 : word) = Some W_5b6ac.
Proof. vm_refl. Qed.
Lemma D_5b6ac : decode_any W_5b6ac = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6b0 : bv 32 := 0x010787b3.
Lemma F_5b6b0 : fetch_word AsanUbsan.M.loaded_segments (0x5b6f8 : word) = Some W_5b6b0.
Proof. vm_refl. Qed.
Lemma D_5b6b0 : decode_any W_5b6b0 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6b4 : bv 32 := 0x0045d813.
Lemma F_5b6b4 : fetch_word AsanUbsan.M.loaded_segments (0x5b6fc : word) = Some W_5b6b4.
Proof. vm_refl. Qed.
Lemma D_5b6b4 : decode_any W_5b6b4 = Some (ShiftImm ALU_SRL 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6b8 : bv 32 := 0x0105e5b3.
Lemma F_5b6b8 : fetch_word AsanUbsan.M.loaded_segments (0x5b700 : word) = Some W_5b6b8.
Proof. vm_refl. Qed.
Lemma D_5b6b8 : decode_any W_5b6b8 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6bc : bv 32 := 0x0085d813.
Lemma F_5b6bc : fetch_word AsanUbsan.M.loaded_segments (0x5b704 : word) = Some W_5b6bc.
Proof. vm_refl. Qed.
Lemma D_5b6bc : decode_any W_5b6bc = Some (ShiftImm ALU_SRL 16 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6c0 : bv 32 := 0x0105e5b3.
Lemma F_5b6c0 : fetch_word AsanUbsan.M.loaded_segments (0x5b708 : word) = Some W_5b6c0.
Proof. vm_refl. Qed.
Lemma D_5b6c0 : decode_any W_5b6c0 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6c4 : bv 32 := 0x0105d813.
Lemma F_5b6c4 : fetch_word AsanUbsan.M.loaded_segments (0x5b70c : word) = Some W_5b6c4.
Proof. vm_refl. Qed.
Lemma D_5b6c4 : decode_any W_5b6c4 = Some (ShiftImm ALU_SRL 16 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6c8 : bv 32 := 0x0105e5b3.
Lemma F_5b6c8 : fetch_word AsanUbsan.M.loaded_segments (0x5b710 : word) = Some W_5b6c8.
Proof. vm_refl. Qed.
Lemma D_5b6c8 : decode_any W_5b6c8 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6cc : bv 32 := 0x0205d813.
Lemma F_5b6cc : fetch_word AsanUbsan.M.loaded_segments (0x5b714 : word) = Some W_5b6cc.
Proof. vm_refl. Qed.
Lemma D_5b6cc : decode_any W_5b6cc = Some (ShiftImm ALU_SRL 16 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6d0 : bv 32 := 0x0105e5b3.
Lemma F_5b6d0 : fetch_word AsanUbsan.M.loaded_segments (0x5b718 : word) = Some W_5b6d0.
Proof. vm_refl. Qed.
Lemma D_5b6d0 : decode_any W_5b6d0 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6d4 : bv 32 := 0xfff5c593.
Lemma F_5b6d4 : fetch_word AsanUbsan.M.loaded_segments (0x5b71c : word) = Some W_5b6d4.
Proof. vm_refl. Qed.
Lemma D_5b6d4 : decode_any W_5b6d4 = Some (OpImm ALU_XOR 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6d8 : bv 32 := 0x0015d813.
Lemma F_5b6d8 : fetch_word AsanUbsan.M.loaded_segments (0x5b720 : word) = Some W_5b6d8.
Proof. vm_refl. Qed.
Lemma D_5b6d8 : decode_any W_5b6d8 = Some (ShiftImm ALU_SRL 16 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6dc : bv 32 := 0x00c87633.
Lemma F_5b6dc : fetch_word AsanUbsan.M.loaded_segments (0x5b724 : word) = Some W_5b6dc.
Proof. vm_refl. Qed.
Lemma D_5b6dc : decode_any W_5b6dc = Some (Op ALU_AND 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6e0 : bv 32 := 0x40c585b3.
Lemma F_5b6e0 : fetch_word AsanUbsan.M.loaded_segments (0x5b728 : word) = Some W_5b6e0.
Proof. vm_refl. Qed.
Lemma D_5b6e0 : decode_any W_5b6e0 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6e4 : bv 32 := 0x00d5f633.
Lemma F_5b6e4 : fetch_word AsanUbsan.M.loaded_segments (0x5b72c : word) = Some W_5b6e4.
Proof. vm_refl. Qed.
Lemma D_5b6e4 : decode_any W_5b6e4 = Some (Op ALU_AND 12 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6e8 : bv 32 := 0x0025d593.
Lemma F_5b6e8 : fetch_word AsanUbsan.M.loaded_segments (0x5b730 : word) = Some W_5b6e8.
Proof. vm_refl. Qed.
Lemma D_5b6e8 : decode_any W_5b6e8 = Some (ShiftImm ALU_SRL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6ec : bv 32 := 0x00d5f5b3.
Lemma F_5b6ec : fetch_word AsanUbsan.M.loaded_segments (0x5b734 : word) = Some W_5b6ec.
Proof. vm_refl. Qed.
Lemma D_5b6ec : decode_any W_5b6ec = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6f0 : bv 32 := 0x00b605b3.
Lemma F_5b6f0 : fetch_word AsanUbsan.M.loaded_segments (0x5b738 : word) = Some W_5b6f0.
Proof. vm_refl. Qed.
Lemma D_5b6f0 : decode_any W_5b6f0 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6f4 : bv 32 := 0x0045d613.
Lemma F_5b6f4 : fetch_word AsanUbsan.M.loaded_segments (0x5b73c : word) = Some W_5b6f4.
Proof. vm_refl. Qed.
Lemma D_5b6f4 : decode_any W_5b6f4 = Some (ShiftImm ALU_SRL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6f8 : bv 32 := 0x00c585b3.
Lemma F_5b6f8 : fetch_word AsanUbsan.M.loaded_segments (0x5b740 : word) = Some W_5b6f8.
Proof. vm_refl. Qed.
Lemma D_5b6f8 : decode_any W_5b6f8 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b6fc : bv 32 := 0x03e00613.
Lemma F_5b6fc : fetch_word AsanUbsan.M.loaded_segments (0x5b744 : word) = Some W_5b6fc.
Proof. vm_refl. Qed.
Lemma D_5b6fc : decode_any W_5b6fc = Some (OpImm ALU_ADD 12 0 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b700 : bv 32 := 0x00e5f5b3.
Lemma F_5b700 : fetch_word AsanUbsan.M.loaded_segments (0x5b748 : word) = Some W_5b700.
Proof. vm_refl. Qed.
Lemma D_5b700 : decode_any W_5b700 = Some (Op ALU_AND 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b704 : bv 32 := 0xfff00693.
Lemma F_5b704 : fetch_word AsanUbsan.M.loaded_segments (0x5b74c : word) = Some W_5b704.
Proof. vm_refl. Qed.
Lemma D_5b704 : decode_any W_5b704 = Some (OpImm ALU_ADD 13 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b708 : bv 32 := 0x02f585b3.
Lemma F_5b708 : fetch_word AsanUbsan.M.loaded_segments (0x5b750 : word) = Some W_5b708.
Proof. vm_refl. Qed.
Lemma D_5b708 : decode_any W_5b708 = Some (Mul M_MUL 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b70c : bv 32 := 0x0385d593.
Lemma F_5b70c : fetch_word AsanUbsan.M.loaded_segments (0x5b754 : word) = Some W_5b70c.
Proof. vm_refl. Qed.
Lemma D_5b70c : decode_any W_5b70c = Some (ShiftImm ALU_SRL 11 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b710 : bv 32 := 0x40b6063b.
Lemma F_5b710 : fetch_word AsanUbsan.M.loaded_segments (0x5b758 : word) = Some W_5b710.
Proof. vm_refl. Qed.
Lemma D_5b710 : decode_any W_5b710 = Some (Op32 ALU_SUB 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b714 : bv 32 := 0x00159593.
Lemma F_5b714 : fetch_word AsanUbsan.M.loaded_segments (0x5b75c : word) = Some W_5b714.
Proof. vm_refl. Qed.
Lemma D_5b714 : decode_any W_5b714 = Some (ShiftImm ALU_SLL 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b718 : bv 32 := 0x00c9d733.
Lemma F_5b718 : fetch_word AsanUbsan.M.loaded_segments (0x5b760 : word) = Some W_5b718.
Proof. vm_refl. Qed.
Lemma D_5b718 : decode_any W_5b718 = Some (Op ALU_SRL 14 19 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b71c : bv 32 := 0x00c6963b.
Lemma F_5b71c : fetch_word AsanUbsan.M.loaded_segments (0x5b764 : word) = Some W_5b71c.
Proof. vm_refl. Qed.
Lemma D_5b71c : decode_any W_5b71c = Some (Op32 ALU_SLL 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b720 : bv 32 := 0x07e5c593.
Lemma F_5b720 : fetch_word AsanUbsan.M.loaded_segments (0x5b768 : word) = Some W_5b720.
Proof. vm_refl. Qed.
Lemma D_5b720 : decode_any W_5b720 = Some (OpImm ALU_XOR 11 11 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b724 : bv 32 := 0x00177713.
Lemma F_5b724 : fetch_word AsanUbsan.M.loaded_segments (0x5b76c : word) = Some W_5b724.
Proof. vm_refl. Qed.
Lemma D_5b724 : decode_any W_5b724 = Some (OpImm ALU_AND 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b728 : bv 32 := 0xfff64613.
Lemma F_5b728 : fetch_word AsanUbsan.M.loaded_segments (0x5b770 : word) = Some W_5b728.
Proof. vm_refl. Qed.
Lemma D_5b728 : decode_any W_5b728 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b72c : bv 32 := 0x00c9f633.
Lemma F_5b72c : fetch_word AsanUbsan.M.loaded_segments (0x5b774 : word) = Some W_5b72c.
Proof. vm_refl. Qed.
Lemma D_5b72c : decode_any W_5b72c = Some (Op ALU_AND 12 19 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b730 : bv 32 := 0x00e5e5b3.
Lemma F_5b730 : fetch_word AsanUbsan.M.loaded_segments (0x5b778 : word) = Some W_5b730.
Proof. vm_refl. Qed.
Lemma D_5b730 : decode_any W_5b730 = Some (Op ALU_OR 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b734 : bv 32 := 0x00c03633.
Lemma F_5b734 : fetch_word AsanUbsan.M.loaded_segments (0x5b77c : word) = Some W_5b734.
Proof. vm_refl. Qed.
Lemma D_5b734 : decode_any W_5b734 = Some (Op ALU_SLTU 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b738 : bv 32 := 0x00c585b3.
Lemma F_5b738 : fetch_word AsanUbsan.M.loaded_segments (0x5b780 : word) = Some W_5b738.
Proof. vm_refl. Qed.
Lemma D_5b738 : decode_any W_5b738 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b73c : bv 32 := 0xffe58593.
Lemma F_5b73c : fetch_word AsanUbsan.M.loaded_segments (0x5b784 : word) = Some W_5b73c.
Proof. vm_refl. Qed.
Lemma D_5b73c : decode_any W_5b73c = Some (OpImm ALU_ADD 11 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b740 : bv 32 := 0x00359593.
Lemma F_5b740 : fetch_word AsanUbsan.M.loaded_segments (0x5b788 : word) = Some W_5b740.
Proof. vm_refl. Qed.
Lemma D_5b740 : decode_any W_5b740 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b744 : bv 32 := 0x00b50533.
Lemma F_5b744 : fetch_word AsanUbsan.M.loaded_segments (0x5b78c : word) = Some W_5b744.
Proof. vm_refl. Qed.
Lemma D_5b744 : decode_any W_5b744 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b748 : bv 32 := 0x00053583.
Lemma F_5b748 : fetch_word AsanUbsan.M.loaded_segments (0x5b790 : word) = Some W_5b748.
Proof. vm_refl. Qed.
Lemma D_5b748 : decode_any W_5b748 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b74c : bv 32 := 0x00158593.
Lemma F_5b74c : fetch_word AsanUbsan.M.loaded_segments (0x5b794 : word) = Some W_5b74c.
Proof. vm_refl. Qed.
Lemma D_5b74c : decode_any W_5b74c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b750 : bv 32 := 0x00b53023.
Lemma F_5b750 : fetch_word AsanUbsan.M.loaded_segments (0x5b798 : word) = Some W_5b750.
Proof. vm_refl. Qed.
Lemma D_5b750 : decode_any W_5b750 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b754 : bv 32 := 0x00813503.
Lemma F_5b754 : fetch_word AsanUbsan.M.loaded_segments (0x5b79c : word) = Some W_5b754.
Proof. vm_refl. Qed.
Lemma D_5b754 : decode_any W_5b754 = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b758 : bv 32 := 0x02050c63.
Lemma F_5b758 : fetch_word AsanUbsan.M.loaded_segments (0x5b7a0 : word) = Some W_5b758.
Proof. vm_refl. Qed.
Lemma D_5b758 : decode_any W_5b758 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b75c : bv 32 := 0x00109517.
Lemma F_5b75c : fetch_word AsanUbsan.M.loaded_segments (0x5b7a4 : word) = Some W_5b75c.
Proof. vm_refl. Qed.
Lemma D_5b75c : decode_any W_5b75c = Some (Auipc 10 265, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b760 : bv 32 := 0xd6c53503.
Lemma F_5b760 : fetch_word AsanUbsan.M.loaded_segments (0x5b7a8 : word) = Some W_5b760.
Proof. vm_refl. Qed.
Lemma D_5b760 : decode_any W_5b760 = Some (Load SZ8 true 10 10 3436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b764 : bv 32 := 0x02c52583.
Lemma F_5b764 : fetch_word AsanUbsan.M.loaded_segments (0x5b7ac : word) = Some W_5b764.
Proof. vm_refl. Qed.
Lemma D_5b764 : decode_any W_5b764 = Some (Load SZ4 true 11 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b768 : bv 32 := 0x02058463.
Lemma F_5b768 : fetch_word AsanUbsan.M.loaded_segments (0x5b7b0 : word) = Some W_5b768.
Proof. vm_refl. Qed.
Lemma D_5b768 : decode_any W_5b768 = Some (Branch BC_EQ 11 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b76c : bv 32 := 0x00048613.
Lemma F_5b76c : fetch_word AsanUbsan.M.loaded_segments (0x5b7b4 : word) = Some W_5b76c.
Proof. vm_refl. Qed.
Lemma D_5b76c : decode_any W_5b76c = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b770 : bv 32 := 0x00b4e463.
Lemma F_5b770 : fetch_word AsanUbsan.M.loaded_segments (0x5b7b8 : word) = Some W_5b770.
Proof. vm_refl. Qed.
Lemma D_5b770 : decode_any W_5b770 = Some (Branch BC_LTU 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b774 : bv 32 := 0x00058613.
Lemma F_5b774 : fetch_word AsanUbsan.M.loaded_segments (0x5b7bc : word) = Some W_5b774.
Proof. vm_refl. Qed.
Lemma D_5b774 : decode_any W_5b774 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b778 : bv 32 := 0x00109597.
Lemma F_5b778 : fetch_word AsanUbsan.M.loaded_segments (0x5b7c0 : word) = Some W_5b778.
Proof. vm_refl. Qed.
Lemma D_5b778 : decode_any W_5b778 = Some (Auipc 11 265, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b77c : bv 32 := 0xd785b583.
Lemma F_5b77c : fetch_word AsanUbsan.M.loaded_segments (0x5b7c4 : word) = Some W_5b77c.
Proof. vm_refl. Qed.
Lemma D_5b77c : decode_any W_5b77c = Some (Load SZ8 true 11 11 3448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b780 : bv 32 := 0x0005b683.
Lemma F_5b780 : fetch_word AsanUbsan.M.loaded_segments (0x5b7c8 : word) = Some W_5b780.
Proof. vm_refl. Qed.
Lemma D_5b780 : decode_any W_5b780 = Some (Load SZ8 true 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b784 : bv 32 := 0x03452583.
Lemma F_5b784 : fetch_word AsanUbsan.M.loaded_segments (0x5b7cc : word) = Some W_5b784.
Proof. vm_refl. Qed.
Lemma D_5b784 : decode_any W_5b784 = Some (Load SZ4 true 11 10 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b788 : bv 32 := 0x000a0513.
Lemma F_5b788 : fetch_word AsanUbsan.M.loaded_segments (0x5b7d0 : word) = Some W_5b788.
Proof. vm_refl. Qed.
Lemma D_5b788 : decode_any W_5b788 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b78c : bv 32 := 0x000680e7.
Lemma F_5b78c : fetch_word AsanUbsan.M.loaded_segments (0x5b7d4 : word) = Some W_5b78c.
Proof. vm_refl. Qed.
Lemma D_5b78c : decode_any W_5b78c = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b790 : bv 32 := 0x369540ef.
Lemma F_5b790 : fetch_word AsanUbsan.M.loaded_segments (0x5b7d8 : word) = Some W_5b790.
Proof. vm_refl. Qed.
Lemma D_5b790 : decode_any W_5b790 = Some (Jal 1 346984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b794 : bv 32 := 0x001ac583.
Lemma F_5b794 : fetch_word AsanUbsan.M.loaded_segments (0x5b7dc : word) = Some W_5b794.
Proof. vm_refl. Qed.
Lemma D_5b794 : decode_any W_5b794 = Some (Load SZ1 false 11 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b798 : bv 32 := 0x40a0053b.
Lemma F_5b798 : fetch_word AsanUbsan.M.loaded_segments (0x5b7e0 : word) = Some W_5b798.
Proof. vm_refl. Qed.
Lemma D_5b798 : decode_any W_5b798 = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b79c : bv 32 := 0x00c57513.
Lemma F_5b79c : fetch_word AsanUbsan.M.loaded_segments (0x5b7e4 : word) = Some W_5b79c.
Proof. vm_refl. Qed.
Lemma D_5b79c : decode_any W_5b79c = Some (OpImm ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7a0 : bv 32 := 0x0f35f593.
Lemma F_5b7a0 : fetch_word AsanUbsan.M.loaded_segments (0x5b7e8 : word) = Some W_5b7a0.
Proof. vm_refl. Qed.
Lemma D_5b7a0 : decode_any W_5b7a0 = Some (OpImm ALU_AND 11 11 243, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7a4 : bv 32 := 0x00a5e533.
Lemma F_5b7a4 : fetch_word AsanUbsan.M.loaded_segments (0x5b7ec : word) = Some W_5b7a4.
Proof. vm_refl. Qed.
Lemma D_5b7a4 : decode_any W_5b7a4 = Some (Op ALU_OR 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7a8 : bv 32 := 0x00200593.
Lemma F_5b7a8 : fetch_word AsanUbsan.M.loaded_segments (0x5b7f0 : word) = Some W_5b7a8.
Proof. vm_refl. Qed.
Lemma D_5b7a8 : decode_any W_5b7a8 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7ac : bv 32 := 0x00aa80a3.
Lemma F_5b7ac : fetch_word AsanUbsan.M.loaded_segments (0x5b7f4 : word) = Some W_5b7ac.
Proof. vm_refl. Qed.
Lemma D_5b7ac : decode_any W_5b7ac = Some (Store SZ1 21 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7b0 : bv 32 := 0x0310000f.
Lemma F_5b7b0 : fetch_word AsanUbsan.M.loaded_segments (0x5b7f8 : word) = Some W_5b7b0.
Proof. vm_refl. Qed.
Lemma D_5b7b0 : decode_any W_5b7b0 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7b4 : bv 32 := 0x00ba8023.
Lemma F_5b7b4 : fetch_word AsanUbsan.M.loaded_segments (0x5b7fc : word) = Some W_5b7b4.
Proof. vm_refl. Qed.
Lemma D_5b7b4 : decode_any W_5b7b4 = Some (Store SZ1 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7b8 : bv 32 := 0x032a8063.
Lemma F_5b7b8 : fetch_word AsanUbsan.M.loaded_segments (0x5b800 : word) = Some W_5b7b8.
Proof. vm_refl. Qed.
Lemma D_5b7b8 : decode_any W_5b7b8 = Some (Branch BC_EQ 21 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7bc : bv 32 := 0x01090693.
Lemma F_5b7bc : fetch_word AsanUbsan.M.loaded_segments (0x5b804 : word) = Some W_5b7bc.
Proof. vm_refl. Qed.
Lemma D_5b7bc : decode_any W_5b7bc = Some (OpImm ALU_ADD 13 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7c0 : bv 32 := 0x20daee63.
Lemma F_5b7c0 : fetch_word AsanUbsan.M.loaded_segments (0x5b808 : word) = Some W_5b7c0.
Proof. vm_refl. Qed.
Lemma D_5b7c0 : decode_any W_5b7c0 = Some (Branch BC_LTU 21 13 540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7c4 : bv 32 := 0xfffb5517.
Lemma F_5b7c4 : fetch_word AsanUbsan.M.loaded_segments (0x5b80c : word) = Some W_5b7c4.
Proof. vm_refl. Qed.
Lemma D_5b7c4 : decode_any W_5b7c4 = Some (Auipc 10 1048501, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7c8 : bv 32 := 0xb7c53503.
Lemma F_5b7c8 : fetch_word AsanUbsan.M.loaded_segments (0x5b810 : word) = Some W_5b7c8.
Proof. vm_refl. Qed.
Lemma D_5b7c8 : decode_any W_5b7c8 = Some (Load SZ8 true 10 10 2940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7cc : bv 32 := 0x01593423.
Lemma F_5b7cc : fetch_word AsanUbsan.M.loaded_segments (0x5b814 : word) = Some W_5b7cc.
Proof. vm_refl. Qed.
Lemma D_5b7cc : decode_any W_5b7cc = Some (Store SZ8 18 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7d0 : bv 32 := 0x0310000f.
Lemma F_5b7d0 : fetch_word AsanUbsan.M.loaded_segments (0x5b818 : word) = Some W_5b7d0.
Proof. vm_refl. Qed.
Lemma D_5b7d0 : decode_any W_5b7d0 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7d4 : bv 32 := 0x00a93023.
Lemma F_5b7d4 : fetch_word AsanUbsan.M.loaded_segments (0x5b81c : word) = Some W_5b7d4.
Proof. vm_refl. Qed.
Lemma D_5b7d4 : decode_any W_5b7d4 = Some (Store SZ8 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7d8 : bv 32 := 0x000a0513.
Lemma F_5b7d8 : fetch_word AsanUbsan.M.loaded_segments (0x5b820 : word) = Some W_5b7d8.
Proof. vm_refl. Qed.
Lemma D_5b7d8 : decode_any W_5b7d8 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7dc : bv 32 := 0x00048593.
Lemma F_5b7dc : fetch_word AsanUbsan.M.loaded_segments (0x5b824 : word) = Some W_5b7dc.
Proof. vm_refl. Qed.
Lemma D_5b7dc : decode_any W_5b7dc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7e0 : bv 32 := 0x70c350ef.
Lemma F_5b7e0 : fetch_word AsanUbsan.M.loaded_segments (0x5b828 : word) = Some W_5b7e0.
Proof. vm_refl. Qed.
Lemma D_5b7e0 : decode_any W_5b7e0 = Some (Jal 1 218892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7e4 : bv 32 := 0x000a0513.
Lemma F_5b7e4 : fetch_word AsanUbsan.M.loaded_segments (0x5b82c : word) = Some W_5b7e4.
Proof. vm_refl. Qed.
Lemma D_5b7e4 : decode_any W_5b7e4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7e8 : bv 32 := 0x07813083.
Lemma F_5b7e8 : fetch_word AsanUbsan.M.loaded_segments (0x5b830 : word) = Some W_5b7e8.
Proof. vm_refl. Qed.
Lemma D_5b7e8 : decode_any W_5b7e8 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7ec : bv 32 := 0x07013403.
Lemma F_5b7ec : fetch_word AsanUbsan.M.loaded_segments (0x5b834 : word) = Some W_5b7ec.
Proof. vm_refl. Qed.
Lemma D_5b7ec : decode_any W_5b7ec = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7f0 : bv 32 := 0x06813483.
Lemma F_5b7f0 : fetch_word AsanUbsan.M.loaded_segments (0x5b838 : word) = Some W_5b7f0.
Proof. vm_refl. Qed.
Lemma D_5b7f0 : decode_any W_5b7f0 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7f4 : bv 32 := 0x06013903.
Lemma F_5b7f4 : fetch_word AsanUbsan.M.loaded_segments (0x5b83c : word) = Some W_5b7f4.
Proof. vm_refl. Qed.
Lemma D_5b7f4 : decode_any W_5b7f4 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7f8 : bv 32 := 0x05813983.
Lemma F_5b7f8 : fetch_word AsanUbsan.M.loaded_segments (0x5b840 : word) = Some W_5b7f8.
Proof. vm_refl. Qed.
Lemma D_5b7f8 : decode_any W_5b7f8 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b7fc : bv 32 := 0x05013a03.
Lemma F_5b7fc : fetch_word AsanUbsan.M.loaded_segments (0x5b844 : word) = Some W_5b7fc.
Proof. vm_refl. Qed.
Lemma D_5b7fc : decode_any W_5b7fc = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b800 : bv 32 := 0x04813a83.
Lemma F_5b800 : fetch_word AsanUbsan.M.loaded_segments (0x5b848 : word) = Some W_5b800.
Proof. vm_refl. Qed.
Lemma D_5b800 : decode_any W_5b800 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b804 : bv 32 := 0x04013b03.
Lemma F_5b804 : fetch_word AsanUbsan.M.loaded_segments (0x5b84c : word) = Some W_5b804.
Proof. vm_refl. Qed.
Lemma D_5b804 : decode_any W_5b804 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b808 : bv 32 := 0x03813b83.
Lemma F_5b808 : fetch_word AsanUbsan.M.loaded_segments (0x5b850 : word) = Some W_5b808.
Proof. vm_refl. Qed.
Lemma D_5b808 : decode_any W_5b808 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b80c : bv 32 := 0x03013c03.
Lemma F_5b80c : fetch_word AsanUbsan.M.loaded_segments (0x5b854 : word) = Some W_5b80c.
Proof. vm_refl. Qed.
Lemma D_5b80c : decode_any W_5b80c = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b810 : bv 32 := 0x02813c83.
Lemma F_5b810 : fetch_word AsanUbsan.M.loaded_segments (0x5b858 : word) = Some W_5b810.
Proof. vm_refl. Qed.
Lemma D_5b810 : decode_any W_5b810 = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b814 : bv 32 := 0x02013d03.
Lemma F_5b814 : fetch_word AsanUbsan.M.loaded_segments (0x5b85c : word) = Some W_5b814.
Proof. vm_refl. Qed.
Lemma D_5b814 : decode_any W_5b814 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b818 : bv 32 := 0x01813d83.
Lemma F_5b818 : fetch_word AsanUbsan.M.loaded_segments (0x5b860 : word) = Some W_5b818.
Proof. vm_refl. Qed.
Lemma D_5b818 : decode_any W_5b818 = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b81c : bv 32 := 0x08010113.
Lemma F_5b81c : fetch_word AsanUbsan.M.loaded_segments (0x5b864 : word) = Some W_5b81c.
Proof. vm_refl. Qed.
Lemma D_5b81c : decode_any W_5b81c = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b820 : bv 32 := 0x00008067.
Lemma F_5b820 : fetch_word AsanUbsan.M.loaded_segments (0x5b868 : word) = Some W_5b820.
Proof. vm_refl. Qed.
Lemma D_5b820 : decode_any W_5b820 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc44 : bv 32 := 0xfe010113.
Lemma F_5bc44 : fetch_word AsanUbsan.M.loaded_segments (0x5bc8c : word) = Some W_5bc44.
Proof. vm_refl. Qed.
Lemma D_5bc44 : decode_any W_5bc44 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc48 : bv 32 := 0x00113c23.
Lemma F_5bc48 : fetch_word AsanUbsan.M.loaded_segments (0x5bc90 : word) = Some W_5bc48.
Proof. vm_refl. Qed.
Lemma D_5bc48 : decode_any W_5bc48 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc4c : bv 32 := 0x00813823.
Lemma F_5bc4c : fetch_word AsanUbsan.M.loaded_segments (0x5bc94 : word) = Some W_5bc4c.
Proof. vm_refl. Qed.
Lemma D_5bc4c : decode_any W_5bc4c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc50 : bv 32 := 0x00913423.
Lemma F_5bc50 : fetch_word AsanUbsan.M.loaded_segments (0x5bc98 : word) = Some W_5bc50.
Proof. vm_refl. Qed.
Lemma D_5bc50 : decode_any W_5bc50 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc54 : bv 32 := 0x01213023.
Lemma F_5bc54 : fetch_word AsanUbsan.M.loaded_segments (0x5bc9c : word) = Some W_5bc54.
Proof. vm_refl. Qed.
Lemma D_5bc54 : decode_any W_5bc54 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc58 : bv 32 := 0x00060413.
Lemma F_5bc58 : fetch_word AsanUbsan.M.loaded_segments (0x5bca0 : word) = Some W_5bc58.
Proof. vm_refl. Qed.
Lemma D_5bc58 : decode_any W_5bc58 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc5c : bv 32 := 0x00050493.
Lemma F_5bc5c : fetch_word AsanUbsan.M.loaded_segments (0x5bca4 : word) = Some W_5bc5c.
Proof. vm_refl. Qed.
Lemma D_5bc5c : decode_any W_5bc5c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc60 : bv 32 := 0xfff50513.
Lemma F_5bc60 : fetch_word AsanUbsan.M.loaded_segments (0x5bca8 : word) = Some W_5bc60.
Proof. vm_refl. Qed.
Lemma D_5bc60 : decode_any W_5bc60 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc64 : bv 32 := 0x00a4c633.
Lemma F_5bc64 : fetch_word AsanUbsan.M.loaded_segments (0x5bcac : word) = Some W_5bc64.
Proof. vm_refl. Qed.
Lemma D_5bc64 : decode_any W_5bc64 = Some (Op ALU_XOR 12 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc68 : bv 32 := 0x04c57263.
Lemma F_5bc68 : fetch_word AsanUbsan.M.loaded_segments (0x5bcb0 : word) = Some W_5bc68.
Proof. vm_refl. Qed.
Lemma D_5bc68 : decode_any W_5bc68 = Some (Branch BC_GEU 10 12 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc6c : bv 32 := 0x00a5f533.
Lemma F_5bc6c : fetch_word AsanUbsan.M.loaded_segments (0x5bcb4 : word) = Some W_5bc6c.
Proof. vm_refl. Qed.
Lemma D_5bc6c : decode_any W_5bc6c = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc70 : bv 32 := 0x02051e63.
Lemma F_5bc70 : fetch_word AsanUbsan.M.loaded_segments (0x5bcb8 : word) = Some W_5bc70.
Proof. vm_refl. Qed.
Lemma D_5bc70 : decode_any W_5bc70 = Some (Branch BC_NE 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc74 : bv 32 := 0x0010e517.
Lemma F_5bc74 : fetch_word AsanUbsan.M.loaded_segments (0x5bcbc : word) = Some W_5bc74.
Proof. vm_refl. Qed.
Lemma D_5bc74 : decode_any W_5bc74 = Some (Auipc 10 270, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc78 : bv 32 := 0x00100713.
Lemma F_5bc78 : fetch_word AsanUbsan.M.loaded_segments (0x5bcc0 : word) = Some W_5bc78.
Proof. vm_refl. Qed.
Lemma D_5bc78 : decode_any W_5bc78 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc7c : bv 32 := 0x49c50513.
Lemma F_5bc7c : fetch_word AsanUbsan.M.loaded_segments (0x5bcc4 : word) = Some W_5bc7c.
Proof. vm_refl. Qed.
Lemma D_5bc7c : decode_any W_5bc7c = Some (OpImm ALU_ADD 10 10 1180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc80 : bv 32 := 0x00100793.
Lemma F_5bc80 : fetch_word AsanUbsan.M.loaded_segments (0x5bcc8 : word) = Some W_5bc80.
Proof. vm_refl. Qed.
Lemma D_5bc80 : decode_any W_5bc80 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc84 : bv 32 := 0x00048613.
Lemma F_5bc84 : fetch_word AsanUbsan.M.loaded_segments (0x5bccc : word) = Some W_5bc84.
Proof. vm_refl. Qed.
Lemma D_5bc84 : decode_any W_5bc84 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc88 : bv 32 := 0x00040693.
Lemma F_5bc88 : fetch_word AsanUbsan.M.loaded_segments (0x5bcd0 : word) = Some W_5bc88.
Proof. vm_refl. Qed.
Lemma D_5bc88 : decode_any W_5bc88 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc8c : bv 32 := 0xc24ff0ef.
Lemma F_5bc8c : fetch_word AsanUbsan.M.loaded_segments (0x5bcd4 : word) = Some W_5bc8c.
Proof. vm_refl. Qed.
Lemma D_5bc8c : decode_any W_5bc8c = Some (Jal 1 2094116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc90 : bv 32 := 0x04050663.
Lemma F_5bc90 : fetch_word AsanUbsan.M.loaded_segments (0x5bcd8 : word) = Some W_5bc90.
Proof. vm_refl. Qed.
Lemma D_5bc90 : decode_any W_5bc90 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc94 : bv 32 := 0x01813083.
Lemma F_5bc94 : fetch_word AsanUbsan.M.loaded_segments (0x5bcdc : word) = Some W_5bc94.
Proof. vm_refl. Qed.
Lemma D_5bc94 : decode_any W_5bc94 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc98 : bv 32 := 0x01013403.
Lemma F_5bc98 : fetch_word AsanUbsan.M.loaded_segments (0x5bce0 : word) = Some W_5bc98.
Proof. vm_refl. Qed.
Lemma D_5bc98 : decode_any W_5bc98 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bc9c : bv 32 := 0x00813483.
Lemma F_5bc9c : fetch_word AsanUbsan.M.loaded_segments (0x5bce4 : word) = Some W_5bc9c.
Proof. vm_refl. Qed.
Lemma D_5bc9c : decode_any W_5bc9c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bca0 : bv 32 := 0x00013903.
Lemma F_5bca0 : fetch_word AsanUbsan.M.loaded_segments (0x5bce8 : word) = Some W_5bca0.
Proof. vm_refl. Qed.
Lemma D_5bca0 : decode_any W_5bca0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bca4 : bv 32 := 0x02010113.
Lemma F_5bca4 : fetch_word AsanUbsan.M.loaded_segments (0x5bcec : word) = Some W_5bca4.
Proof. vm_refl. Qed.
Lemma D_5bca4 : decode_any W_5bca4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5bca8 : bv 32 := 0x00008067.
Lemma F_5bca8 : fetch_word AsanUbsan.M.loaded_segments (0x5bcf0 : word) = Some W_5bca8.
Proof. vm_refl. Qed.
Lemma D_5bca8 : decode_any W_5bca8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

