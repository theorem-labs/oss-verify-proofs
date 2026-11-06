(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_53e20 : bv 32 := 0x81010113.
Lemma F_53e20 : fetch_word AsanUbsan.M.loaded_segments (0x53e20 : word) = Some W_53e20.
Proof. vm_refl. Qed.
Lemma D_53e20 : decode_any W_53e20 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e24 : bv 32 := 0x7e113423.
Lemma F_53e24 : fetch_word AsanUbsan.M.loaded_segments (0x53e24 : word) = Some W_53e24.
Proof. vm_refl. Qed.
Lemma D_53e24 : decode_any W_53e24 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e28 : bv 32 := 0x7e813023.
Lemma F_53e28 : fetch_word AsanUbsan.M.loaded_segments (0x53e28 : word) = Some W_53e28.
Proof. vm_refl. Qed.
Lemma D_53e28 : decode_any W_53e28 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e2c : bv 32 := 0x7c913c23.
Lemma F_53e2c : fetch_word AsanUbsan.M.loaded_segments (0x53e2c : word) = Some W_53e2c.
Proof. vm_refl. Qed.
Lemma D_53e2c : decode_any W_53e2c = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e30 : bv 32 := 0x7d213823.
Lemma F_53e30 : fetch_word AsanUbsan.M.loaded_segments (0x53e30 : word) = Some W_53e30.
Proof. vm_refl. Qed.
Lemma D_53e30 : decode_any W_53e30 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e34 : bv 32 := 0x7d313423.
Lemma F_53e34 : fetch_word AsanUbsan.M.loaded_segments (0x53e34 : word) = Some W_53e34.
Proof. vm_refl. Qed.
Lemma D_53e34 : decode_any W_53e34 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e38 : bv 32 := 0x7d413023.
Lemma F_53e38 : fetch_word AsanUbsan.M.loaded_segments (0x53e38 : word) = Some W_53e38.
Proof. vm_refl. Qed.
Lemma D_53e38 : decode_any W_53e38 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e3c : bv 32 := 0x7b513c23.
Lemma F_53e3c : fetch_word AsanUbsan.M.loaded_segments (0x53e3c : word) = Some W_53e3c.
Proof. vm_refl. Qed.
Lemma D_53e3c : decode_any W_53e3c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e40 : bv 32 := 0x7b613823.
Lemma F_53e40 : fetch_word AsanUbsan.M.loaded_segments (0x53e40 : word) = Some W_53e40.
Proof. vm_refl. Qed.
Lemma D_53e40 : decode_any W_53e40 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e44 : bv 32 := 0x7b713423.
Lemma F_53e44 : fetch_word AsanUbsan.M.loaded_segments (0x53e44 : word) = Some W_53e44.
Proof. vm_refl. Qed.
Lemma D_53e44 : decode_any W_53e44 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e48 : bv 32 := 0x7f010413.
Lemma F_53e48 : fetch_word AsanUbsan.M.loaded_segments (0x53e48 : word) = Some W_53e48.
Proof. vm_refl. Qed.
Lemma D_53e48 : decode_any W_53e48 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e4c : bv 32 := 0xf9010113.
Lemma F_53e4c : fetch_word AsanUbsan.M.loaded_segments (0x53e4c : word) = Some W_53e4c.
Proof. vm_refl. Qed.
Lemma D_53e4c : decode_any W_53e4c = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e50 : bv 32 := 0x00056697.
Lemma F_53e50 : fetch_word AsanUbsan.M.loaded_segments (0x53e50 : word) = Some W_53e50.
Proof. vm_refl. Qed.
Lemma D_53e50 : decode_any W_53e50 = Some (Auipc 13 86, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e54 : bv 32 := 0x1d06b683.
Lemma F_53e54 : fetch_word AsanUbsan.M.loaded_segments (0x53e54 : word) = Some W_53e54.
Proof. vm_refl. Qed.
Lemma D_53e54 : decode_any W_53e54 = Some (Load SZ8 true 13 13 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e58 : bv 32 := 0x0006c683.
Lemma F_53e58 : fetch_word AsanUbsan.M.loaded_segments (0x53e58 : word) = Some W_53e58.
Proof. vm_refl. Qed.
Lemma D_53e58 : decode_any W_53e58 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e5c : bv 32 := 0x0e068863.
Lemma F_53e5c : fetch_word AsanUbsan.M.loaded_segments (0x53e5c : word) = Some W_53e5c.
Proof. vm_refl. Qed.
Lemma D_53e5c : decode_any W_53e5c = Some (Branch BC_EQ 13 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e60 : bv 32 := 0x80040a13.
Lemma F_53e60 : fetch_word AsanUbsan.M.loaded_segments (0x53e60 : word) = Some W_53e60.
Proof. vm_refl. Qed.
Lemma D_53e60 : decode_any W_53e60 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e64 : bv 32 := 0xfa0a0a13.
Lemma F_53e64 : fetch_word AsanUbsan.M.loaded_segments (0x53e64 : word) = Some W_53e64.
Proof. vm_refl. Qed.
Lemma D_53e64 : decode_any W_53e64 = Some (OpImm ALU_ADD 20 20 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e68 : bv 32 := 0x00c58ab3.
Lemma F_53e68 : fetch_word AsanUbsan.M.loaded_segments (0x53e68 : word) = Some W_53e68.
Proof. vm_refl. Qed.
Lemma D_53e68 : decode_any W_53e68 = Some (Op ALU_ADD 21 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e6c : bv 32 := 0x00c509b3.
Lemma F_53e6c : fetch_word AsanUbsan.M.loaded_segments (0x53e6c : word) = Some W_53e6c.
Proof. vm_refl. Qed.
Lemma D_53e6c : decode_any W_53e6c = Some (Op ALU_ADD 19 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e70 : bv 32 := 0x00b50663.
Lemma F_53e70 : fetch_word AsanUbsan.M.loaded_segments (0x53e70 : word) = Some W_53e70.
Proof. vm_refl. Qed.
Lemma D_53e70 : decode_any W_53e70 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e74 : bv 32 := 0x0135f463.
Lemma F_53e74 : fetch_word AsanUbsan.M.loaded_segments (0x53e74 : word) = Some W_53e74.
Proof. vm_refl. Qed.
Lemma D_53e74 : decode_any W_53e74 = Some (Branch BC_GEU 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e78 : bv 32 := 0x1b556a63.
Lemma F_53e78 : fetch_word AsanUbsan.M.loaded_segments (0x53e78 : word) = Some W_53e78.
Proof. vm_refl. Qed.
Lemma D_53e78 : decode_any W_53e78 = Some (Branch BC_LTU 10 21 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e7c : bv 32 := 0xfff5c693.
Lemma F_53e7c : fetch_word AsanUbsan.M.loaded_segments (0x53e7c : word) = Some W_53e7c.
Proof. vm_refl. Qed.
Lemma D_53e7c : decode_any W_53e7c = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e80 : bv 32 := 0x26c6e463.
Lemma F_53e80 : fetch_word AsanUbsan.M.loaded_segments (0x53e80 : word) = Some W_53e80.
Proof. vm_refl. Qed.
Lemma D_53e80 : decode_any W_53e80 = Some (Branch BC_LTU 13 12 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e84 : bv 32 := 0xfbf60b13.
Lemma F_53e84 : fetch_word AsanUbsan.M.loaded_segments (0x53e84 : word) = Some W_53e84.
Proof. vm_refl. Qed.
Lemma D_53e84 : decode_any W_53e84 = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e88 : bv 32 := 0xfbf00693.
Lemma F_53e88 : fetch_word AsanUbsan.M.loaded_segments (0x53e88 : word) = Some W_53e88.
Proof. vm_refl. Qed.
Lemma D_53e88 : decode_any W_53e88 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e8c : bv 32 := 0x2f66f263.
Lemma F_53e8c : fetch_word AsanUbsan.M.loaded_segments (0x53e8c : word) = Some W_53e8c.
Proof. vm_refl. Qed.
Lemma D_53e8c : decode_any W_53e8c = Some (Branch BC_GEU 13 22 740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e90 : bv 32 := 0x00055697.
Lemma F_53e90 : fetch_word AsanUbsan.M.loaded_segments (0x53e90 : word) = Some W_53e90.
Proof. vm_refl. Qed.
Lemma D_53e90 : decode_any W_53e90 = Some (Auipc 13 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e94 : bv 32 := 0x6286b683.
Lemma F_53e94 : fetch_word AsanUbsan.M.loaded_segments (0x53e94 : word) = Some W_53e94.
Proof. vm_refl. Qed.
Lemma D_53e94 : decode_any W_53e94 = Some (Load SZ8 true 13 13 1576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e98 : bv 32 := 0x0006b703.
Lemma F_53e98 : fetch_word AsanUbsan.M.loaded_segments (0x53e98 : word) = Some W_53e98.
Proof. vm_refl. Qed.
Lemma D_53e98 : decode_any W_53e98 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e9c : bv 32 := 0xfffa8a93.
Lemma F_53e9c : fetch_word AsanUbsan.M.loaded_segments (0x53e9c : word) = Some W_53e9c.
Proof. vm_refl. Qed.
Lemma D_53e9c : decode_any W_53e9c = Some (OpImm ALU_ADD 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ea0 : bv 32 := 0x0035d693.
Lemma F_53ea0 : fetch_word AsanUbsan.M.loaded_segments (0x53ea0 : word) = Some W_53ea0.
Proof. vm_refl. Qed.
Lemma D_53ea0 : decode_any W_53ea0 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ea4 : bv 32 := 0x003ad793.
Lemma F_53ea4 : fetch_word AsanUbsan.M.loaded_segments (0x53ea4 : word) = Some W_53ea4.
Proof. vm_refl. Qed.
Lemma D_53ea4 : decode_any W_53ea4 = Some (ShiftImm ALU_SRL 15 21 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ea8 : bv 32 := 0x00d706b3.
Lemma F_53ea8 : fetch_word AsanUbsan.M.loaded_segments (0x53ea8 : word) = Some W_53ea8.
Proof. vm_refl. Qed.
Lemma D_53ea8 : decode_any W_53ea8 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53eac : bv 32 := 0x00f70733.
Lemma F_53eac : fetch_word AsanUbsan.M.loaded_segments (0x53eac : word) = Some W_53eac.
Proof. vm_refl. Qed.
Lemma D_53eac : decode_any W_53eac = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53eb0 : bv 32 := 0xff86f793.
Lemma F_53eb0 : fetch_word AsanUbsan.M.loaded_segments (0x53eb0 : word) = Some W_53eb0.
Proof. vm_refl. Qed.
Lemma D_53eb0 : decode_any W_53eb0 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53eb4 : bv 32 := 0xff877813.
Lemma F_53eb4 : fetch_word AsanUbsan.M.loaded_segments (0x53eb4 : word) = Some W_53eb4.
Proof. vm_refl. Qed.
Lemma D_53eb4 : decode_any W_53eb4 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53eb8 : bv 32 := 0x0007b783.
Lemma F_53eb8 : fetch_word AsanUbsan.M.loaded_segments (0x53eb8 : word) = Some W_53eb8.
Proof. vm_refl. Qed.
Lemma D_53eb8 : decode_any W_53eb8 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ebc : bv 32 := 0x00083803.
Lemma F_53ebc : fetch_word AsanUbsan.M.loaded_segments (0x53ebc : word) = Some W_53ebc.
Proof. vm_refl. Qed.
Lemma D_53ebc : decode_any W_53ebc = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ec0 : bv 32 := 0x00f867b3.
Lemma F_53ec0 : fetch_word AsanUbsan.M.loaded_segments (0x53ec0 : word) = Some W_53ec0.
Proof. vm_refl. Qed.
Lemma D_53ec0 : decode_any W_53ec0 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ec4 : bv 32 := 0x2a079a63.
Lemma F_53ec4 : fetch_word AsanUbsan.M.loaded_segments (0x53ec4 : word) = Some W_53ec4.
Proof. vm_refl. Qed.
Lemma D_53ec4 : decode_any W_53ec4 = Some (Branch BC_NE 15 0 692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ec8 : bv 32 := 0xfff54693.
Lemma F_53ec8 : fetch_word AsanUbsan.M.loaded_segments (0x53ec8 : word) = Some W_53ec8.
Proof. vm_refl. Qed.
Lemma D_53ec8 : decode_any W_53ec8 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ecc : bv 32 := 0x0cc6ea63.
Lemma F_53ecc : fetch_word AsanUbsan.M.loaded_segments (0x53ecc : word) = Some W_53ecc.
Proof. vm_refl. Qed.
Lemma D_53ecc : decode_any W_53ecc = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ed0 : bv 32 := 0xfbf00693.
Lemma F_53ed0 : fetch_word AsanUbsan.M.loaded_segments (0x53ed0 : word) = Some W_53ed0.
Proof. vm_refl. Qed.
Lemma D_53ed0 : decode_any W_53ed0 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ed4 : bv 32 := 0x1566f863.
Lemma F_53ed4 : fetch_word AsanUbsan.M.loaded_segments (0x53ed4 : word) = Some W_53ed4.
Proof. vm_refl. Qed.
Lemma D_53ed4 : decode_any W_53ed4 = Some (Branch BC_GEU 13 22 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ed8 : bv 32 := 0x00055697.
Lemma F_53ed8 : fetch_word AsanUbsan.M.loaded_segments (0x53ed8 : word) = Some W_53ed8.
Proof. vm_refl. Qed.
Lemma D_53ed8 : decode_any W_53ed8 = Some (Auipc 13 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53edc : bv 32 := 0x5e06b683.
Lemma F_53edc : fetch_word AsanUbsan.M.loaded_segments (0x53edc : word) = Some W_53edc.
Proof. vm_refl. Qed.
Lemma D_53edc : decode_any W_53edc = Some (Load SZ8 true 13 13 1504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ee0 : bv 32 := 0x0006b703.
Lemma F_53ee0 : fetch_word AsanUbsan.M.loaded_segments (0x53ee0 : word) = Some W_53ee0.
Proof. vm_refl. Qed.
Lemma D_53ee0 : decode_any W_53ee0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ee4 : bv 32 := 0xfff98993.
Lemma F_53ee4 : fetch_word AsanUbsan.M.loaded_segments (0x53ee4 : word) = Some W_53ee4.
Proof. vm_refl. Qed.
Lemma D_53ee4 : decode_any W_53ee4 = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ee8 : bv 32 := 0x00355693.
Lemma F_53ee8 : fetch_word AsanUbsan.M.loaded_segments (0x53ee8 : word) = Some W_53ee8.
Proof. vm_refl. Qed.
Lemma D_53ee8 : decode_any W_53ee8 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53eec : bv 32 := 0x0039d793.
Lemma F_53eec : fetch_word AsanUbsan.M.loaded_segments (0x53eec : word) = Some W_53eec.
Proof. vm_refl. Qed.
Lemma D_53eec : decode_any W_53eec = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ef0 : bv 32 := 0x00d706b3.
Lemma F_53ef0 : fetch_word AsanUbsan.M.loaded_segments (0x53ef0 : word) = Some W_53ef0.
Proof. vm_refl. Qed.
Lemma D_53ef0 : decode_any W_53ef0 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ef4 : bv 32 := 0x00f70733.
Lemma F_53ef4 : fetch_word AsanUbsan.M.loaded_segments (0x53ef4 : word) = Some W_53ef4.
Proof. vm_refl. Qed.
Lemma D_53ef4 : decode_any W_53ef4 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ef8 : bv 32 := 0xff86f793.
Lemma F_53ef8 : fetch_word AsanUbsan.M.loaded_segments (0x53ef8 : word) = Some W_53ef8.
Proof. vm_refl. Qed.
Lemma D_53ef8 : decode_any W_53ef8 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53efc : bv 32 := 0xff877813.
Lemma F_53efc : fetch_word AsanUbsan.M.loaded_segments (0x53efc : word) = Some W_53efc.
Proof. vm_refl. Qed.
Lemma D_53efc : decode_any W_53efc = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f00 : bv 32 := 0x0007b783.
Lemma F_53f00 : fetch_word AsanUbsan.M.loaded_segments (0x53f00 : word) = Some W_53f00.
Proof. vm_refl. Qed.
Lemma D_53f00 : decode_any W_53f00 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f04 : bv 32 := 0x00083803.
Lemma F_53f04 : fetch_word AsanUbsan.M.loaded_segments (0x53f04 : word) = Some W_53f04.
Proof. vm_refl. Qed.
Lemma D_53f04 : decode_any W_53f04 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f08 : bv 32 := 0x00f867b3.
Lemma F_53f08 : fetch_word AsanUbsan.M.loaded_segments (0x53f08 : word) = Some W_53f08.
Proof. vm_refl. Qed.
Lemma D_53f08 : decode_any W_53f08 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f0c : bv 32 := 0x30079863.
Lemma F_53f0c : fetch_word AsanUbsan.M.loaded_segments (0x53f0c : word) = Some W_53f0c.
Proof. vm_refl. Qed.
Lemma D_53f0c : decode_any W_53f0c = Some (Branch BC_NE 15 0 784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f10 : bv 32 := 0x00057697.
Lemma F_53f10 : fetch_word AsanUbsan.M.loaded_segments (0x53f10 : word) = Some W_53f10.
Proof. vm_refl. Qed.
Lemma D_53f10 : decode_any W_53f10 = Some (Auipc 13 87, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f14 : bv 32 := 0x4186b683.
Lemma F_53f14 : fetch_word AsanUbsan.M.loaded_segments (0x53f14 : word) = Some W_53f14.
Proof. vm_refl. Qed.
Lemma D_53f14 : decode_any W_53f14 = Some (Load SZ8 true 13 13 1048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f18 : bv 32 := 0x000680e7.
Lemma F_53f18 : fetch_word AsanUbsan.M.loaded_segments (0x53f18 : word) = Some W_53f18.
Proof. vm_refl. Qed.
Lemma D_53f18 : decode_any W_53f18 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f1c : bv 32 := 0x07010113.
Lemma F_53f1c : fetch_word AsanUbsan.M.loaded_segments (0x53f1c : word) = Some W_53f1c.
Proof. vm_refl. Qed.
Lemma D_53f1c : decode_any W_53f1c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f20 : bv 32 := 0x7e813083.
Lemma F_53f20 : fetch_word AsanUbsan.M.loaded_segments (0x53f20 : word) = Some W_53f20.
Proof. vm_refl. Qed.
Lemma D_53f20 : decode_any W_53f20 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f24 : bv 32 := 0x7e013403.
Lemma F_53f24 : fetch_word AsanUbsan.M.loaded_segments (0x53f24 : word) = Some W_53f24.
Proof. vm_refl. Qed.
Lemma D_53f24 : decode_any W_53f24 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f28 : bv 32 := 0x7d813483.
Lemma F_53f28 : fetch_word AsanUbsan.M.loaded_segments (0x53f28 : word) = Some W_53f28.
Proof. vm_refl. Qed.
Lemma D_53f28 : decode_any W_53f28 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f2c : bv 32 := 0x7d013903.
Lemma F_53f2c : fetch_word AsanUbsan.M.loaded_segments (0x53f2c : word) = Some W_53f2c.
Proof. vm_refl. Qed.
Lemma D_53f2c : decode_any W_53f2c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f30 : bv 32 := 0x7c813983.
Lemma F_53f30 : fetch_word AsanUbsan.M.loaded_segments (0x53f30 : word) = Some W_53f30.
Proof. vm_refl. Qed.
Lemma D_53f30 : decode_any W_53f30 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f34 : bv 32 := 0x7c013a03.
Lemma F_53f34 : fetch_word AsanUbsan.M.loaded_segments (0x53f34 : word) = Some W_53f34.
Proof. vm_refl. Qed.
Lemma D_53f34 : decode_any W_53f34 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f38 : bv 32 := 0x7b813a83.
Lemma F_53f38 : fetch_word AsanUbsan.M.loaded_segments (0x53f38 : word) = Some W_53f38.
Proof. vm_refl. Qed.
Lemma D_53f38 : decode_any W_53f38 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f3c : bv 32 := 0x7b013b03.
Lemma F_53f3c : fetch_word AsanUbsan.M.loaded_segments (0x53f3c : word) = Some W_53f3c.
Proof. vm_refl. Qed.
Lemma D_53f3c : decode_any W_53f3c = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f40 : bv 32 := 0x7a813b83.
Lemma F_53f40 : fetch_word AsanUbsan.M.loaded_segments (0x53f40 : word) = Some W_53f40.
Proof. vm_refl. Qed.
Lemma D_53f40 : decode_any W_53f40 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f44 : bv 32 := 0x7f010113.
Lemma F_53f44 : fetch_word AsanUbsan.M.loaded_segments (0x53f44 : word) = Some W_53f44.
Proof. vm_refl. Qed.
Lemma D_53f44 : decode_any W_53f44 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f48 : bv 32 := 0x00008067.
Lemma F_53f48 : fetch_word AsanUbsan.M.loaded_segments (0x53f48 : word) = Some W_53f48.
Proof. vm_refl. Qed.
Lemma D_53f48 : decode_any W_53f48 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f4c : bv 32 := 0x00060913.
Lemma F_53f4c : fetch_word AsanUbsan.M.loaded_segments (0x53f4c : word) = Some W_53f4c.
Proof. vm_refl. Qed.
Lemma D_53f4c : decode_any W_53f4c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f50 : bv 32 := 0x00058993.
Lemma F_53f50 : fetch_word AsanUbsan.M.loaded_segments (0x53f50 : word) = Some W_53f50.
Proof. vm_refl. Qed.
Lemma D_53f50 : decode_any W_53f50 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f54 : bv 32 := 0x00050493.
Lemma F_53f54 : fetch_word AsanUbsan.M.loaded_segments (0x53f54 : word) = Some W_53f54.
Proof. vm_refl. Qed.
Lemma D_53f54 : decode_any W_53f54 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f58 : bv 32 := 0x7c9060ef.
Lemma F_53f58 : fetch_word AsanUbsan.M.loaded_segments (0x53f58 : word) = Some W_53f58.
Proof. vm_refl. Qed.
Lemma D_53f58 : decode_any W_53f58 = Some (Jal 1 28616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f5c : bv 32 := 0x00098593.
Lemma F_53f5c : fetch_word AsanUbsan.M.loaded_segments (0x53f5c : word) = Some W_53f5c.
Proof. vm_refl. Qed.
Lemma D_53f5c : decode_any W_53f5c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f60 : bv 32 := 0x00090613.
Lemma F_53f60 : fetch_word AsanUbsan.M.loaded_segments (0x53f60 : word) = Some W_53f60.
Proof. vm_refl. Qed.
Lemma D_53f60 : decode_any W_53f60 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f64 : bv 32 := 0x00050693.
Lemma F_53f64 : fetch_word AsanUbsan.M.loaded_segments (0x53f64 : word) = Some W_53f64.
Proof. vm_refl. Qed.
Lemma D_53f64 : decode_any W_53f64 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f68 : bv 32 := 0x00048513.
Lemma F_53f68 : fetch_word AsanUbsan.M.loaded_segments (0x53f68 : word) = Some W_53f68.
Proof. vm_refl. Qed.
Lemma D_53f68 : decode_any W_53f68 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f6c : bv 32 := 0xfa0692e3.
Lemma F_53f6c : fetch_word AsanUbsan.M.loaded_segments (0x53f6c : word) = Some W_53f6c.
Proof. vm_refl. Qed.
Lemma D_53f6c : decode_any W_53f6c = Some (Branch BC_NE 13 0 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f70 : bv 32 := 0x07010113.
Lemma F_53f70 : fetch_word AsanUbsan.M.loaded_segments (0x53f70 : word) = Some W_53f70.
Proof. vm_refl. Qed.
Lemma D_53f70 : decode_any W_53f70 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f74 : bv 32 := 0x7e813083.
Lemma F_53f74 : fetch_word AsanUbsan.M.loaded_segments (0x53f74 : word) = Some W_53f74.
Proof. vm_refl. Qed.
Lemma D_53f74 : decode_any W_53f74 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f78 : bv 32 := 0x7e013403.
Lemma F_53f78 : fetch_word AsanUbsan.M.loaded_segments (0x53f78 : word) = Some W_53f78.
Proof. vm_refl. Qed.
Lemma D_53f78 : decode_any W_53f78 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f7c : bv 32 := 0x7d813483.
Lemma F_53f7c : fetch_word AsanUbsan.M.loaded_segments (0x53f7c : word) = Some W_53f7c.
Proof. vm_refl. Qed.
Lemma D_53f7c : decode_any W_53f7c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f80 : bv 32 := 0x7d013903.
Lemma F_53f80 : fetch_word AsanUbsan.M.loaded_segments (0x53f80 : word) = Some W_53f80.
Proof. vm_refl. Qed.
Lemma D_53f80 : decode_any W_53f80 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f84 : bv 32 := 0x7c813983.
Lemma F_53f84 : fetch_word AsanUbsan.M.loaded_segments (0x53f84 : word) = Some W_53f84.
Proof. vm_refl. Qed.
Lemma D_53f84 : decode_any W_53f84 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f88 : bv 32 := 0x7c013a03.
Lemma F_53f88 : fetch_word AsanUbsan.M.loaded_segments (0x53f88 : word) = Some W_53f88.
Proof. vm_refl. Qed.
Lemma D_53f88 : decode_any W_53f88 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f8c : bv 32 := 0x7b813a83.
Lemma F_53f8c : fetch_word AsanUbsan.M.loaded_segments (0x53f8c : word) = Some W_53f8c.
Proof. vm_refl. Qed.
Lemma D_53f8c : decode_any W_53f8c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f90 : bv 32 := 0x7b013b03.
Lemma F_53f90 : fetch_word AsanUbsan.M.loaded_segments (0x53f90 : word) = Some W_53f90.
Proof. vm_refl. Qed.
Lemma D_53f90 : decode_any W_53f90 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f94 : bv 32 := 0x7a813b83.
Lemma F_53f94 : fetch_word AsanUbsan.M.loaded_segments (0x53f94 : word) = Some W_53f94.
Proof. vm_refl. Qed.
Lemma D_53f94 : decode_any W_53f94 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f98 : bv 32 := 0x7f010113.
Lemma F_53f98 : fetch_word AsanUbsan.M.loaded_segments (0x53f98 : word) = Some W_53f98.
Proof. vm_refl. Qed.
Lemma D_53f98 : decode_any W_53f98 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53f9c : bv 32 := 0x1941206f.
Lemma F_53f9c : fetch_word AsanUbsan.M.loaded_segments (0x53f9c : word) = Some W_53f9c.
Proof. vm_refl. Qed.
Lemma D_53f9c : decode_any W_53f9c = Some (Jal 0 74132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fa0 : bv 32 := 0x80040693.
Lemma F_53fa0 : fetch_word AsanUbsan.M.loaded_segments (0x53fa0 : word) = Some W_53fa0.
Proof. vm_refl. Qed.
Lemma D_53fa0 : decode_any W_53fa0 = Some (OpImm ALU_ADD 13 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fa4 : bv 32 := 0xfb068693.
Lemma F_53fa4 : fetch_word AsanUbsan.M.loaded_segments (0x53fa4 : word) = Some W_53fa4.
Proof. vm_refl. Qed.
Lemma D_53fa4 : decode_any W_53fa4 = Some (OpImm ALU_ADD 13 13 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fa8 : bv 32 := 0x80040713.
Lemma F_53fa8 : fetch_word AsanUbsan.M.loaded_segments (0x53fa8 : word) = Some W_53fa8.
Proof. vm_refl. Qed.
Lemma D_53fa8 : decode_any W_53fa8 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fac : bv 32 := 0xfa070713.
Lemma F_53fac : fetch_word AsanUbsan.M.loaded_segments (0x53fac : word) = Some W_53fac.
Proof. vm_refl. Qed.
Lemma D_53fac : decode_any W_53fac = Some (OpImm ALU_ADD 14 14 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fb0 : bv 32 := 0x7ff70b93.
Lemma F_53fb0 : fetch_word AsanUbsan.M.loaded_segments (0x53fb0 : word) = Some W_53fb0.
Proof. vm_refl. Qed.
Lemma D_53fb0 : decode_any W_53fb0 = Some (OpImm ALU_ADD 23 14 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fb4 : bv 32 := 0x000bb4a3.
Lemma F_53fb4 : fetch_word AsanUbsan.M.loaded_segments (0x53fb4 : word) = Some W_53fb4.
Proof. vm_refl. Qed.
Lemma D_53fb4 : decode_any W_53fb4 = Some (Store SZ8 23 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fb8 : bv 32 := 0x00da3023.
Lemma F_53fb8 : fetch_word AsanUbsan.M.loaded_segments (0x53fb8 : word) = Some W_53fb8.
Proof. vm_refl. Qed.
Lemma D_53fb8 : decode_any W_53fb8 = Some (Store SZ8 20 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fbc : bv 32 := 0x000a3423.
Lemma F_53fbc : fetch_word AsanUbsan.M.loaded_segments (0x53fbc : word) = Some W_53fbc.
Proof. vm_refl. Qed.
Lemma D_53fbc : decode_any W_53fbc = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fc0 : bv 32 := 0x00060493.
Lemma F_53fc0 : fetch_word AsanUbsan.M.loaded_segments (0x53fc0 : word) = Some W_53fc0.
Proof. vm_refl. Qed.
Lemma D_53fc0 : decode_any W_53fc0 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fc4 : bv 32 := 0x00058a93.
Lemma F_53fc4 : fetch_word AsanUbsan.M.loaded_segments (0x53fc4 : word) = Some W_53fc4.
Proof. vm_refl. Qed.
Lemma D_53fc4 : decode_any W_53fc4 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fc8 : bv 32 := 0x00050913.
Lemma F_53fc8 : fetch_word AsanUbsan.M.loaded_segments (0x53fc8 : word) = Some W_53fc8.
Proof. vm_refl. Qed.
Lemma D_53fc8 : decode_any W_53fc8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fcc : bv 32 := 0x6ac210ef.
Lemma F_53fcc : fetch_word AsanUbsan.M.loaded_segments (0x53fcc : word) = Some W_53fcc.
Proof. vm_refl. Qed.
Lemma D_53fcc : decode_any W_53fcc = Some (Jal 1 136876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fd0 : bv 32 := 0x00050593.
Lemma F_53fd0 : fetch_word AsanUbsan.M.loaded_segments (0x53fd0 : word) = Some W_53fd0.
Proof. vm_refl. Qed.
Lemma D_53fd0 : decode_any W_53fd0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fd4 : bv 32 := 0x00055517.
Lemma F_53fd4 : fetch_word AsanUbsan.M.loaded_segments (0x53fd4 : word) = Some W_53fd4.
Proof. vm_refl. Qed.
Lemma D_53fd4 : decode_any W_53fd4 = Some (Auipc 10 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fd8 : bv 32 := 0x4d453503.
Lemma F_53fd8 : fetch_word AsanUbsan.M.loaded_segments (0x53fd8 : word) = Some W_53fd8.
Proof. vm_refl. Qed.
Lemma D_53fd8 : decode_any W_53fd8 = Some (Load SZ8 true 10 10 1236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fdc : bv 32 := 0x02154703.
Lemma F_53fdc : fetch_word AsanUbsan.M.loaded_segments (0x53fdc : word) = Some W_53fdc.
Proof. vm_refl. Qed.
Lemma D_53fdc : decode_any W_53fdc = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fe0 : bv 32 := 0x008bb4a3.
Lemma F_53fe0 : fetch_word AsanUbsan.M.loaded_segments (0x53fe0 : word) = Some W_53fe0.
Proof. vm_refl. Qed.
Lemma D_53fe0 : decode_any W_53fe0 = Some (Store SZ8 23 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fe4 : bv 32 := 0x80040513.
Lemma F_53fe4 : fetch_word AsanUbsan.M.loaded_segments (0x53fe4 : word) = Some W_53fe4.
Proof. vm_refl. Qed.
Lemma D_53fe4 : decode_any W_53fe4 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fe8 : bv 32 := 0xfa050513.
Lemma F_53fe8 : fetch_word AsanUbsan.M.loaded_segments (0x53fe8 : word) = Some W_53fe8.
Proof. vm_refl. Qed.
Lemma D_53fe8 : decode_any W_53fe8 = Some (OpImm ALU_ADD 10 10 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53fec : bv 32 := 0x0ff00793.
Lemma F_53fec : fetch_word AsanUbsan.M.loaded_segments (0x53fec : word) = Some W_53fec.
Proof. vm_refl. Qed.
Lemma D_53fec : decode_any W_53fec = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ff0 : bv 32 := 0x00040613.
Lemma F_53ff0 : fetch_word AsanUbsan.M.loaded_segments (0x53ff0 : word) = Some W_53ff0.
Proof. vm_refl. Qed.
Lemma D_53ff0 : decode_any W_53ff0 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ff4 : bv 32 := 0x00000693.
Lemma F_53ff4 : fetch_word AsanUbsan.M.loaded_segments (0x53ff4 : word) = Some W_53ff4.
Proof. vm_refl. Qed.
Lemma D_53ff4 : decode_any W_53ff4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ff8 : bv 32 := 0x3d1080ef.
Lemma F_53ff8 : fetch_word AsanUbsan.M.loaded_segments (0x53ff8 : word) = Some W_53ff8.
Proof. vm_refl. Qed.
Lemma D_53ff8 : decode_any W_53ff8 = Some (Jal 1 35792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ffc : bv 32 := 0x80040613.
Lemma F_53ffc : fetch_word AsanUbsan.M.loaded_segments (0x53ffc : word) = Some W_53ffc.
Proof. vm_refl. Qed.
Lemma D_53ffc : decode_any W_53ffc = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54000 : bv 32 := 0xfa060613.
Lemma F_54000 : fetch_word AsanUbsan.M.loaded_segments (0x54000 : word) = Some W_54000.
Proof. vm_refl. Qed.
Lemma D_54000 : decode_any W_54000 = Some (OpImm ALU_ADD 12 12 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54004 : bv 32 := 0x00090513.
Lemma F_54004 : fetch_word AsanUbsan.M.loaded_segments (0x54004 : word) = Some W_54004.
Proof. vm_refl. Qed.
Lemma D_54004 : decode_any W_54004 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54008 : bv 32 := 0x00048593.
Lemma F_54008 : fetch_word AsanUbsan.M.loaded_segments (0x54008 : word) = Some W_54008.
Proof. vm_refl. Qed.
Lemma D_54008 : decode_any W_54008 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5400c : bv 32 := 0x175050ef.
Lemma F_5400c : fetch_word AsanUbsan.M.loaded_segments (0x5400c : word) = Some W_5400c.
Proof. vm_refl. Qed.
Lemma D_5400c : decode_any W_5400c = Some (Jal 1 22900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54010 : bv 32 := 0x00090513.
Lemma F_54010 : fetch_word AsanUbsan.M.loaded_segments (0x54010 : word) = Some W_54010.
Proof. vm_refl. Qed.
Lemma D_54010 : decode_any W_54010 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54014 : bv 32 := 0x000a8593.
Lemma F_54014 : fetch_word AsanUbsan.M.loaded_segments (0x54014 : word) = Some W_54014.
Proof. vm_refl. Qed.
Lemma D_54014 : decode_any W_54014 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54018 : bv 32 := 0x00048613.
Lemma F_54018 : fetch_word AsanUbsan.M.loaded_segments (0x54018 : word) = Some W_54018.
Proof. vm_refl. Qed.
Lemma D_54018 : decode_any W_54018 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5401c : bv 32 := 0xfbf00693.
Lemma F_5401c : fetch_word AsanUbsan.M.loaded_segments (0x5401c : word) = Some W_5401c.
Proof. vm_refl. Qed.
Lemma D_5401c : decode_any W_5401c = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54020 : bv 32 := 0xeb66ece3.
Lemma F_54020 : fetch_word AsanUbsan.M.loaded_segments (0x54020 : word) = Some W_54020.
Proof. vm_refl. Qed.
Lemma D_54020 : decode_any W_54020 = Some (Branch BC_LTU 13 22 7864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54024 : bv 32 := 0x22061663.
Lemma F_54024 : fetch_word AsanUbsan.M.loaded_segments (0x54024 : word) = Some W_54024.
Proof. vm_refl. Qed.
Lemma D_54024 : decode_any W_54024 = Some (Branch BC_NE 12 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54028 : bv 32 := 0xee9ff06f.
Lemma F_54028 : fetch_word AsanUbsan.M.loaded_segments (0x54028 : word) = Some W_54028.
Proof. vm_refl. Qed.
Lemma D_54028 : decode_any W_54028 = Some (Jal 0 2096872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5402c : bv 32 := 0x00050493.
Lemma F_5402c : fetch_word AsanUbsan.M.loaded_segments (0x5402c : word) = Some W_5402c.
Proof. vm_refl. Qed.
Lemma D_5402c : decode_any W_5402c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54030 : bv 32 := 0x00058913.
Lemma F_54030 : fetch_word AsanUbsan.M.loaded_segments (0x54030 : word) = Some W_54030.
Proof. vm_refl. Qed.
Lemma D_54030 : decode_any W_54030 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54034 : bv 32 := 0x00060b13.
Lemma F_54034 : fetch_word AsanUbsan.M.loaded_segments (0x54034 : word) = Some W_54034.
Proof. vm_refl. Qed.
Lemma D_54034 : decode_any W_54034 = Some (OpImm ALU_ADD 22 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54038 : bv 32 := 0x80040513.
Lemma F_54038 : fetch_word AsanUbsan.M.loaded_segments (0x54038 : word) = Some W_54038.
Proof. vm_refl. Qed.
Lemma D_54038 : decode_any W_54038 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5403c : bv 32 := 0xfb050513.
Lemma F_5403c : fetch_word AsanUbsan.M.loaded_segments (0x5403c : word) = Some W_5403c.
Proof. vm_refl. Qed.
Lemma D_5403c : decode_any W_5403c = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54040 : bv 32 := 0x80040593.
Lemma F_54040 : fetch_word AsanUbsan.M.loaded_segments (0x54040 : word) = Some W_54040.
Proof. vm_refl. Qed.
Lemma D_54040 : decode_any W_54040 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54044 : bv 32 := 0xfa058593.
Lemma F_54044 : fetch_word AsanUbsan.M.loaded_segments (0x54044 : word) = Some W_54044.
Proof. vm_refl. Qed.
Lemma D_54044 : decode_any W_54044 = Some (OpImm ALU_ADD 11 11 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54048 : bv 32 := 0x7ff58b93.
Lemma F_54048 : fetch_word AsanUbsan.M.loaded_segments (0x54048 : word) = Some W_54048.
Proof. vm_refl. Qed.
Lemma D_54048 : decode_any W_54048 = Some (OpImm ALU_ADD 23 11 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5404c : bv 32 := 0x000bb4a3.
Lemma F_5404c : fetch_word AsanUbsan.M.loaded_segments (0x5404c : word) = Some W_5404c.
Proof. vm_refl. Qed.
Lemma D_5404c : decode_any W_5404c = Some (Store SZ8 23 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54050 : bv 32 := 0x00aa3023.
Lemma F_54050 : fetch_word AsanUbsan.M.loaded_segments (0x54050 : word) = Some W_54050.
Proof. vm_refl. Qed.
Lemma D_54050 : decode_any W_54050 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54054 : bv 32 := 0x000a3423.
Lemma F_54054 : fetch_word AsanUbsan.M.loaded_segments (0x54054 : word) = Some W_54054.
Proof. vm_refl. Qed.
Lemma D_54054 : decode_any W_54054 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54058 : bv 32 := 0x620210ef.
Lemma F_54058 : fetch_word AsanUbsan.M.loaded_segments (0x54058 : word) = Some W_54058.
Proof. vm_refl. Qed.
Lemma D_54058 : decode_any W_54058 = Some (Jal 1 136736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5405c : bv 32 := 0x00050593.
Lemma F_5405c : fetch_word AsanUbsan.M.loaded_segments (0x5405c : word) = Some W_5405c.
Proof. vm_refl. Qed.
Lemma D_5405c : decode_any W_5405c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54060 : bv 32 := 0x00055517.
Lemma F_54060 : fetch_word AsanUbsan.M.loaded_segments (0x54060 : word) = Some W_54060.
Proof. vm_refl. Qed.
Lemma D_54060 : decode_any W_54060 = Some (Auipc 10 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54064 : bv 32 := 0x44853503.
Lemma F_54064 : fetch_word AsanUbsan.M.loaded_segments (0x54064 : word) = Some W_54064.
Proof. vm_refl. Qed.
Lemma D_54064 : decode_any W_54064 = Some (Load SZ8 true 10 10 1096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54068 : bv 32 := 0x02154703.
Lemma F_54068 : fetch_word AsanUbsan.M.loaded_segments (0x54068 : word) = Some W_54068.
Proof. vm_refl. Qed.
Lemma D_54068 : decode_any W_54068 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5406c : bv 32 := 0x008bb4a3.
Lemma F_5406c : fetch_word AsanUbsan.M.loaded_segments (0x5406c : word) = Some W_5406c.
Proof. vm_refl. Qed.
Lemma D_5406c : decode_any W_5406c = Some (Store SZ8 23 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54070 : bv 32 := 0x80040513.
Lemma F_54070 : fetch_word AsanUbsan.M.loaded_segments (0x54070 : word) = Some W_54070.
Proof. vm_refl. Qed.
Lemma D_54070 : decode_any W_54070 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54074 : bv 32 := 0xfa050513.
Lemma F_54074 : fetch_word AsanUbsan.M.loaded_segments (0x54074 : word) = Some W_54074.
Proof. vm_refl. Qed.
Lemma D_54074 : decode_any W_54074 = Some (OpImm ALU_ADD 10 10 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54078 : bv 32 := 0x0ff00793.
Lemma F_54078 : fetch_word AsanUbsan.M.loaded_segments (0x54078 : word) = Some W_54078.
Proof. vm_refl. Qed.
Lemma D_54078 : decode_any W_54078 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5407c : bv 32 := 0x00040613.
Lemma F_5407c : fetch_word AsanUbsan.M.loaded_segments (0x5407c : word) = Some W_5407c.
Proof. vm_refl. Qed.
Lemma D_5407c : decode_any W_5407c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54080 : bv 32 := 0x00000693.
Lemma F_54080 : fetch_word AsanUbsan.M.loaded_segments (0x54080 : word) = Some W_54080.
Proof. vm_refl. Qed.
Lemma D_54080 : decode_any W_54080 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54084 : bv 32 := 0x345080ef.
Lemma F_54084 : fetch_word AsanUbsan.M.loaded_segments (0x54084 : word) = Some W_54084.
Proof. vm_refl. Qed.
Lemma D_54084 : decode_any W_54084 = Some (Jal 1 35652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54088 : bv 32 := 0xfffc1517.
Lemma F_54088 : fetch_word AsanUbsan.M.loaded_segments (0x54088 : word) = Some W_54088.
Proof. vm_refl. Qed.
Lemma D_54088 : decode_any W_54088 = Some (Auipc 10 1048513, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5408c : bv 32 := 0xd8450513.
Lemma F_5408c : fetch_word AsanUbsan.M.loaded_segments (0x5408c : word) = Some W_5408c.
Proof. vm_refl. Qed.
Lemma D_5408c : decode_any W_5408c = Some (OpImm ALU_ADD 10 10 3460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54090 : bv 32 := 0x2e5090ef.
Lemma F_54090 : fetch_word AsanUbsan.M.loaded_segments (0x54090 : word) = Some W_54090.
Proof. vm_refl. Qed.
Lemma D_54090 : decode_any W_54090 = Some (Jal 1 39652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54094 : bv 32 := 0x04051063.
Lemma F_54094 : fetch_word AsanUbsan.M.loaded_segments (0x54094 : word) = Some W_54094.
Proof. vm_refl. Qed.
Lemma D_54094 : decode_any W_54094 = Some (Branch BC_NE 10 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54098 : bv 32 := 0x345090ef.
Lemma F_54098 : fetch_word AsanUbsan.M.loaded_segments (0x54098 : word) = Some W_54098.
Proof. vm_refl. Qed.
Lemma D_54098 : decode_any W_54098 = Some (Jal 1 39748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5409c : bv 32 := 0x00050a63.
Lemma F_5409c : fetch_word AsanUbsan.M.loaded_segments (0x5409c : word) = Some W_5409c.
Proof. vm_refl. Qed.
Lemma D_5409c : decode_any W_5409c = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540a0 : bv 32 := 0x80040513.
Lemma F_540a0 : fetch_word AsanUbsan.M.loaded_segments (0x540a0 : word) = Some W_540a0.
Proof. vm_refl. Qed.
Lemma D_540a0 : decode_any W_540a0 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540a4 : bv 32 := 0xfa050513.
Lemma F_540a4 : fetch_word AsanUbsan.M.loaded_segments (0x540a4 : word) = Some W_540a4.
Proof. vm_refl. Qed.
Lemma D_540a4 : decode_any W_540a4 = Some (OpImm ALU_ADD 10 10 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540a8 : bv 32 := 0x63d090ef.
Lemma F_540a8 : fetch_word AsanUbsan.M.loaded_segments (0x540a8 : word) = Some W_540a8.
Proof. vm_refl. Qed.
Lemma D_540a8 : decode_any W_540a8 = Some (Jal 1 40508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540ac : bv 32 := 0x02051463.
Lemma F_540ac : fetch_word AsanUbsan.M.loaded_segments (0x540ac : word) = Some W_540ac.
Proof. vm_refl. Qed.
Lemma D_540ac : decode_any W_540ac = Some (Branch BC_NE 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540b0 : bv 32 := 0xfffc1517.
Lemma F_540b0 : fetch_word AsanUbsan.M.loaded_segments (0x540b0 : word) = Some W_540b0.
Proof. vm_refl. Qed.
Lemma D_540b0 : decode_any W_540b0 = Some (Auipc 10 1048513, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540b4 : bv 32 := 0xd5c50513.
Lemma F_540b4 : fetch_word AsanUbsan.M.loaded_segments (0x540b4 : word) = Some W_540b4.
Proof. vm_refl. Qed.
Lemma D_540b4 : decode_any W_540b4 = Some (OpImm ALU_ADD 10 10 3420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540b8 : bv 32 := 0x80040793.
Lemma F_540b8 : fetch_word AsanUbsan.M.loaded_segments (0x540b8 : word) = Some W_540b8.
Proof. vm_refl. Qed.
Lemma D_540b8 : decode_any W_540b8 = Some (OpImm ALU_ADD 15 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540bc : bv 32 := 0xfa078793.
Lemma F_540bc : fetch_word AsanUbsan.M.loaded_segments (0x540bc : word) = Some W_540bc.
Proof. vm_refl. Qed.
Lemma D_540bc : decode_any W_540bc = Some (OpImm ALU_ADD 15 15 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540c0 : bv 32 := 0x00048593.
Lemma F_540c0 : fetch_word AsanUbsan.M.loaded_segments (0x540c0 : word) = Some W_540c0.
Proof. vm_refl. Qed.
Lemma D_540c0 : decode_any W_540c0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540c4 : bv 32 := 0x000b0613.
Lemma F_540c4 : fetch_word AsanUbsan.M.loaded_segments (0x540c4 : word) = Some W_540c4.
Proof. vm_refl. Qed.
Lemma D_540c4 : decode_any W_540c4 = Some (OpImm ALU_ADD 12 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540c8 : bv 32 := 0x00090693.
Lemma F_540c8 : fetch_word AsanUbsan.M.loaded_segments (0x540c8 : word) = Some W_540c8.
Proof. vm_refl. Qed.
Lemma D_540c8 : decode_any W_540c8 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540cc : bv 32 := 0x000b0713.
Lemma F_540cc : fetch_word AsanUbsan.M.loaded_segments (0x540cc : word) = Some W_540cc.
Proof. vm_refl. Qed.
Lemma D_540cc : decode_any W_540cc = Some (OpImm ALU_ADD 14 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540d0 : bv 32 := 0x5dc050ef.
Lemma F_540d0 : fetch_word AsanUbsan.M.loaded_segments (0x540d0 : word) = Some W_540d0.
Proof. vm_refl. Qed.
Lemma D_540d0 : decode_any W_540d0 = Some (Jal 1 21980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540d4 : bv 32 := 0x000b0613.
Lemma F_540d4 : fetch_word AsanUbsan.M.loaded_segments (0x540d4 : word) = Some W_540d4.
Proof. vm_refl. Qed.
Lemma D_540d4 : decode_any W_540d4 = Some (OpImm ALU_ADD 12 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540d8 : bv 32 := 0x00090593.
Lemma F_540d8 : fetch_word AsanUbsan.M.loaded_segments (0x540d8 : word) = Some W_540d8.
Proof. vm_refl. Qed.
Lemma D_540d8 : decode_any W_540d8 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540dc : bv 32 := 0x00048513.
Lemma F_540dc : fetch_word AsanUbsan.M.loaded_segments (0x540dc : word) = Some W_540dc.
Proof. vm_refl. Qed.
Lemma D_540dc : decode_any W_540dc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540e0 : bv 32 := 0xfff94693.
Lemma F_540e0 : fetch_word AsanUbsan.M.loaded_segments (0x540e0 : word) = Some W_540e0.
Proof. vm_refl. Qed.
Lemma D_540e0 : decode_any W_540e0 = Some (OpImm ALU_XOR 13 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540e4 : bv 32 := 0xdb66f0e3.
Lemma F_540e4 : fetch_word AsanUbsan.M.loaded_segments (0x540e4 : word) = Some W_540e4.
Proof. vm_refl. Qed.
Lemma D_540e4 : decode_any W_540e4 = Some (Branch BC_GEU 13 22 7584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540e8 : bv 32 := 0x80040693.
Lemma F_540e8 : fetch_word AsanUbsan.M.loaded_segments (0x540e8 : word) = Some W_540e8.
Proof. vm_refl. Qed.
Lemma D_540e8 : decode_any W_540e8 = Some (OpImm ALU_ADD 13 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540ec : bv 32 := 0xfb068693.
Lemma F_540ec : fetch_word AsanUbsan.M.loaded_segments (0x540ec : word) = Some W_540ec.
Proof. vm_refl. Qed.
Lemma D_540ec : decode_any W_540ec = Some (OpImm ALU_ADD 13 13 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540f0 : bv 32 := 0x80040713.
Lemma F_540f0 : fetch_word AsanUbsan.M.loaded_segments (0x540f0 : word) = Some W_540f0.
Proof. vm_refl. Qed.
Lemma D_540f0 : decode_any W_540f0 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540f4 : bv 32 := 0xfa070713.
Lemma F_540f4 : fetch_word AsanUbsan.M.loaded_segments (0x540f4 : word) = Some W_540f4.
Proof. vm_refl. Qed.
Lemma D_540f4 : decode_any W_540f4 = Some (OpImm ALU_ADD 14 14 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540f8 : bv 32 := 0x7ff70b93.
Lemma F_540f8 : fetch_word AsanUbsan.M.loaded_segments (0x540f8 : word) = Some W_540f8.
Proof. vm_refl. Qed.
Lemma D_540f8 : decode_any W_540f8 = Some (OpImm ALU_ADD 23 14 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_540fc : bv 32 := 0x000bb4a3.
Lemma F_540fc : fetch_word AsanUbsan.M.loaded_segments (0x540fc : word) = Some W_540fc.
Proof. vm_refl. Qed.
Lemma D_540fc : decode_any W_540fc = Some (Store SZ8 23 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54100 : bv 32 := 0x00da3023.
Lemma F_54100 : fetch_word AsanUbsan.M.loaded_segments (0x54100 : word) = Some W_54100.
Proof. vm_refl. Qed.
Lemma D_54100 : decode_any W_54100 = Some (Store SZ8 20 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54104 : bv 32 := 0x000a3423.
Lemma F_54104 : fetch_word AsanUbsan.M.loaded_segments (0x54104 : word) = Some W_54104.
Proof. vm_refl. Qed.
Lemma D_54104 : decode_any W_54104 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54108 : bv 32 := 0x00060493.
Lemma F_54108 : fetch_word AsanUbsan.M.loaded_segments (0x54108 : word) = Some W_54108.
Proof. vm_refl. Qed.
Lemma D_54108 : decode_any W_54108 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5410c : bv 32 := 0x00058913.
Lemma F_5410c : fetch_word AsanUbsan.M.loaded_segments (0x5410c : word) = Some W_5410c.
Proof. vm_refl. Qed.
Lemma D_5410c : decode_any W_5410c = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54110 : bv 32 := 0x00050b13.
Lemma F_54110 : fetch_word AsanUbsan.M.loaded_segments (0x54110 : word) = Some W_54110.
Proof. vm_refl. Qed.
Lemma D_54110 : decode_any W_54110 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54114 : bv 32 := 0x564210ef.
Lemma F_54114 : fetch_word AsanUbsan.M.loaded_segments (0x54114 : word) = Some W_54114.
Proof. vm_refl. Qed.
Lemma D_54114 : decode_any W_54114 = Some (Jal 1 136548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54118 : bv 32 := 0x00050593.
Lemma F_54118 : fetch_word AsanUbsan.M.loaded_segments (0x54118 : word) = Some W_54118.
Proof. vm_refl. Qed.
Lemma D_54118 : decode_any W_54118 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5411c : bv 32 := 0x00055517.
Lemma F_5411c : fetch_word AsanUbsan.M.loaded_segments (0x5411c : word) = Some W_5411c.
Proof. vm_refl. Qed.
Lemma D_5411c : decode_any W_5411c = Some (Auipc 10 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54120 : bv 32 := 0x38c53503.
Lemma F_54120 : fetch_word AsanUbsan.M.loaded_segments (0x54120 : word) = Some W_54120.
Proof. vm_refl. Qed.
Lemma D_54120 : decode_any W_54120 = Some (Load SZ8 true 10 10 908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54124 : bv 32 := 0x02154703.
Lemma F_54124 : fetch_word AsanUbsan.M.loaded_segments (0x54124 : word) = Some W_54124.
Proof. vm_refl. Qed.
Lemma D_54124 : decode_any W_54124 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54128 : bv 32 := 0x008bb4a3.
Lemma F_54128 : fetch_word AsanUbsan.M.loaded_segments (0x54128 : word) = Some W_54128.
Proof. vm_refl. Qed.
Lemma D_54128 : decode_any W_54128 = Some (Store SZ8 23 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5412c : bv 32 := 0x80040513.
Lemma F_5412c : fetch_word AsanUbsan.M.loaded_segments (0x5412c : word) = Some W_5412c.
Proof. vm_refl. Qed.
Lemma D_5412c : decode_any W_5412c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54130 : bv 32 := 0xfa050513.
Lemma F_54130 : fetch_word AsanUbsan.M.loaded_segments (0x54130 : word) = Some W_54130.
Proof. vm_refl. Qed.
Lemma D_54130 : decode_any W_54130 = Some (OpImm ALU_ADD 10 10 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54134 : bv 32 := 0x0ff00793.
Lemma F_54134 : fetch_word AsanUbsan.M.loaded_segments (0x54134 : word) = Some W_54134.
Proof. vm_refl. Qed.
Lemma D_54134 : decode_any W_54134 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54138 : bv 32 := 0x00040613.
Lemma F_54138 : fetch_word AsanUbsan.M.loaded_segments (0x54138 : word) = Some W_54138.
Proof. vm_refl. Qed.
Lemma D_54138 : decode_any W_54138 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5413c : bv 32 := 0x00000693.
Lemma F_5413c : fetch_word AsanUbsan.M.loaded_segments (0x5413c : word) = Some W_5413c.
Proof. vm_refl. Qed.
Lemma D_5413c : decode_any W_5413c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54140 : bv 32 := 0x289080ef.
Lemma F_54140 : fetch_word AsanUbsan.M.loaded_segments (0x54140 : word) = Some W_54140.
Proof. vm_refl. Qed.
Lemma D_54140 : decode_any W_54140 = Some (Jal 1 35464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54144 : bv 32 := 0x80040613.
Lemma F_54144 : fetch_word AsanUbsan.M.loaded_segments (0x54144 : word) = Some W_54144.
Proof. vm_refl. Qed.
Lemma D_54144 : decode_any W_54144 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54148 : bv 32 := 0xfa060613.
Lemma F_54148 : fetch_word AsanUbsan.M.loaded_segments (0x54148 : word) = Some W_54148.
Proof. vm_refl. Qed.
Lemma D_54148 : decode_any W_54148 = Some (OpImm ALU_ADD 12 12 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5414c : bv 32 := 0x00090513.
Lemma F_5414c : fetch_word AsanUbsan.M.loaded_segments (0x5414c : word) = Some W_5414c.
Proof. vm_refl. Qed.
Lemma D_5414c : decode_any W_5414c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54150 : bv 32 := 0x00048593.
Lemma F_54150 : fetch_word AsanUbsan.M.loaded_segments (0x54150 : word) = Some W_54150.
Proof. vm_refl. Qed.
Lemma D_54150 : decode_any W_54150 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54154 : bv 32 := 0x02d050ef.
Lemma F_54154 : fetch_word AsanUbsan.M.loaded_segments (0x54154 : word) = Some W_54154.
Proof. vm_refl. Qed.
Lemma D_54154 : decode_any W_54154 = Some (Jal 1 22572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54158 : bv 32 := 0x000b0513.
Lemma F_54158 : fetch_word AsanUbsan.M.loaded_segments (0x54158 : word) = Some W_54158.
Proof. vm_refl. Qed.
Lemma D_54158 : decode_any W_54158 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5415c : bv 32 := 0x00090593.
Lemma F_5415c : fetch_word AsanUbsan.M.loaded_segments (0x5415c : word) = Some W_5415c.
Proof. vm_refl. Qed.
Lemma D_5415c : decode_any W_5415c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54160 : bv 32 := 0x00048613.
Lemma F_54160 : fetch_word AsanUbsan.M.loaded_segments (0x54160 : word) = Some W_54160.
Proof. vm_refl. Qed.
Lemma D_54160 : decode_any W_54160 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54164 : bv 32 := 0xfbf48b13.
Lemma F_54164 : fetch_word AsanUbsan.M.loaded_segments (0x54164 : word) = Some W_54164.
Proof. vm_refl. Qed.
Lemma D_54164 : decode_any W_54164 = Some (OpImm ALU_ADD 22 9 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54168 : bv 32 := 0xfbf00693.
Lemma F_54168 : fetch_word AsanUbsan.M.loaded_segments (0x54168 : word) = Some W_54168.
Proof. vm_refl. Qed.
Lemma D_54168 : decode_any W_54168 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5416c : bv 32 := 0xd366e2e3.
Lemma F_5416c : fetch_word AsanUbsan.M.loaded_segments (0x5416c : word) = Some W_5416c.
Proof. vm_refl. Qed.
Lemma D_5416c : decode_any W_5416c = Some (Branch BC_LTU 13 22 7460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54170 : bv 32 := 0x02061e63.
Lemma F_54170 : fetch_word AsanUbsan.M.loaded_segments (0x54170 : word) = Some W_54170.
Proof. vm_refl. Qed.
Lemma D_54170 : decode_any W_54170 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54174 : bv 32 := 0xd55ff06f.
Lemma F_54174 : fetch_word AsanUbsan.M.loaded_segments (0x54174 : word) = Some W_54174.
Proof. vm_refl. Qed.
Lemma D_54174 : decode_any W_54174 = Some (Jal 0 2096468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54178 : bv 32 := 0x00070783.
Lemma F_54178 : fetch_word AsanUbsan.M.loaded_segments (0x54178 : word) = Some W_54178.
Proof. vm_refl. Qed.
Lemma D_54178 : decode_any W_54178 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5417c : bv 32 := 0x007af813.
Lemma F_5417c : fetch_word AsanUbsan.M.loaded_segments (0x5417c : word) = Some W_5417c.
Proof. vm_refl. Qed.
Lemma D_5417c : decode_any W_5417c = Some (OpImm ALU_AND 16 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54180 : bv 32 := 0x00f038b3.
Lemma F_54180 : fetch_word AsanUbsan.M.loaded_segments (0x54180 : word) = Some W_54180.
Proof. vm_refl. Qed.
Lemma D_54180 : decode_any W_54180 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54184 : bv 32 := 0x00f827b3.
Lemma F_54184 : fetch_word AsanUbsan.M.loaded_segments (0x54184 : word) = Some W_54184.
Proof. vm_refl. Qed.
Lemma D_54184 : decode_any W_54184 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54188 : bv 32 := 0x0017c793.
Lemma F_54188 : fetch_word AsanUbsan.M.loaded_segments (0x54188 : word) = Some W_54188.
Proof. vm_refl. Qed.
Lemma D_54188 : decode_any W_54188 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5418c : bv 32 := 0x00f8f7b3.
Lemma F_5418c : fetch_word AsanUbsan.M.loaded_segments (0x5418c : word) = Some W_5418c.
Proof. vm_refl. Qed.
Lemma D_5418c : decode_any W_5418c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54190 : bv 32 := 0x00e6fa63.
Lemma F_54190 : fetch_word AsanUbsan.M.loaded_segments (0x54190 : word) = Some W_54190.
Proof. vm_refl. Qed.
Lemma D_54190 : decode_any W_54190 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54194 : bv 32 := 0x0006c803.
Lemma F_54194 : fetch_word AsanUbsan.M.loaded_segments (0x54194 : word) = Some W_54194.
Proof. vm_refl. Qed.
Lemma D_54194 : decode_any W_54194 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54198 : bv 32 := 0x00168693.
Lemma F_54198 : fetch_word AsanUbsan.M.loaded_segments (0x54198 : word) = Some W_54198.
Proof. vm_refl. Qed.
Lemma D_54198 : decode_any W_54198 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5419c : bv 32 := 0x00f867b3.
Lemma F_5419c : fetch_word AsanUbsan.M.loaded_segments (0x5419c : word) = Some W_5419c.
Proof. vm_refl. Qed.
Lemma D_5419c : decode_any W_5419c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541a0 : bv 32 := 0xfee69ae3.
Lemma F_541a0 : fetch_word AsanUbsan.M.loaded_segments (0x541a0 : word) = Some W_541a0.
Proof. vm_refl. Qed.
Lemma D_541a0 : decode_any W_541a0 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541a4 : bv 32 := 0x0ff7f693.
Lemma F_541a4 : fetch_word AsanUbsan.M.loaded_segments (0x541a4 : word) = Some W_541a4.
Proof. vm_refl. Qed.
Lemma D_541a4 : decode_any W_541a4 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541a8 : bv 32 := 0xd20680e3.
Lemma F_541a8 : fetch_word AsanUbsan.M.loaded_segments (0x541a8 : word) = Some W_541a8.
Proof. vm_refl. Qed.
Lemma D_541a8 : decode_any W_541a8 = Some (Branch BC_EQ 13 0 7456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541ac : bv 32 := 0x00050a93.
Lemma F_541ac : fetch_word AsanUbsan.M.loaded_segments (0x541ac : word) = Some W_541ac.
Proof. vm_refl. Qed.
Lemma D_541ac : decode_any W_541ac = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541b0 : bv 32 := 0x00058513.
Lemma F_541b0 : fetch_word AsanUbsan.M.loaded_segments (0x541b0 : word) = Some W_541b0.
Proof. vm_refl. Qed.
Lemma D_541b0 : decode_any W_541b0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541b4 : bv 32 := 0x00058b93.
Lemma F_541b4 : fetch_word AsanUbsan.M.loaded_segments (0x541b4 : word) = Some W_541b4.
Proof. vm_refl. Qed.
Lemma D_541b4 : decode_any W_541b4 = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541b8 : bv 32 := 0x00060593.
Lemma F_541b8 : fetch_word AsanUbsan.M.loaded_segments (0x541b8 : word) = Some W_541b8.
Proof. vm_refl. Qed.
Lemma D_541b8 : decode_any W_541b8 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541bc : bv 32 := 0x00060493.
Lemma F_541bc : fetch_word AsanUbsan.M.loaded_segments (0x541bc : word) = Some W_541bc.
Proof. vm_refl. Qed.
Lemma D_541bc : decode_any W_541bc = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541c0 : bv 32 := 0x7dc020ef.
Lemma F_541c0 : fetch_word AsanUbsan.M.loaded_segments (0x541c0 : word) = Some W_541c0.
Proof. vm_refl. Qed.
Lemma D_541c0 : decode_any W_541c0 = Some (Jal 1 10204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541c4 : bv 32 := 0x000b8593.
Lemma F_541c4 : fetch_word AsanUbsan.M.loaded_segments (0x541c4 : word) = Some W_541c4.
Proof. vm_refl. Qed.
Lemma D_541c4 : decode_any W_541c4 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541c8 : bv 32 := 0x00048613.
Lemma F_541c8 : fetch_word AsanUbsan.M.loaded_segments (0x541c8 : word) = Some W_541c8.
Proof. vm_refl. Qed.
Lemma D_541c8 : decode_any W_541c8 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541cc : bv 32 := 0x00050913.
Lemma F_541cc : fetch_word AsanUbsan.M.loaded_segments (0x541cc : word) = Some W_541cc.
Proof. vm_refl. Qed.
Lemma D_541cc : decode_any W_541cc = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541d0 : bv 32 := 0x000a8513.
Lemma F_541d0 : fetch_word AsanUbsan.M.loaded_segments (0x541d0 : word) = Some W_541d0.
Proof. vm_refl. Qed.
Lemma D_541d0 : decode_any W_541d0 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541d4 : bv 32 := 0xce090ae3.
Lemma F_541d4 : fetch_word AsanUbsan.M.loaded_segments (0x541d4 : word) = Some W_541d4.
Proof. vm_refl. Qed.
Lemma D_541d4 : decode_any W_541d4 = Some (Branch BC_EQ 18 0 7412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541d8 : bv 32 := 0x4a0210ef.
Lemma F_541d8 : fetch_word AsanUbsan.M.loaded_segments (0x541d8 : word) = Some W_541d8.
Proof. vm_refl. Qed.
Lemma D_541d8 : decode_any W_541d8 = Some (Jal 1 136352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541dc : bv 32 := 0xfffbc597.
Lemma F_541dc : fetch_word AsanUbsan.M.loaded_segments (0x541dc : word) = Some W_541dc.
Proof. vm_refl. Qed.
Lemma D_541dc : decode_any W_541dc = Some (Auipc 11 1048508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541e0 : bv 32 := 0x21c5b583.
Lemma F_541e0 : fetch_word AsanUbsan.M.loaded_segments (0x541e0 : word) = Some W_541e0.
Proof. vm_refl. Qed.
Lemma D_541e0 : decode_any W_541e0 = Some (Load SZ8 true 11 11 540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541e4 : bv 32 := 0x00ba3023.
Lemma F_541e4 : fetch_word AsanUbsan.M.loaded_segments (0x541e4 : word) = Some W_541e4.
Proof. vm_refl. Qed.
Lemma D_541e4 : decode_any W_541e4 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541e8 : bv 32 := 0x80040613.
Lemma F_541e8 : fetch_word AsanUbsan.M.loaded_segments (0x541e8 : word) = Some W_541e8.
Proof. vm_refl. Qed.
Lemma D_541e8 : decode_any W_541e8 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541ec : bv 32 := 0xfa060613.
Lemma F_541ec : fetch_word AsanUbsan.M.loaded_segments (0x541ec : word) = Some W_541ec.
Proof. vm_refl. Qed.
Lemma D_541ec : decode_any W_541ec = Some (OpImm ALU_ADD 12 12 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541f0 : bv 32 := 0x00040593.
Lemma F_541f0 : fetch_word AsanUbsan.M.loaded_segments (0x541f0 : word) = Some W_541f0.
Proof. vm_refl. Qed.
Lemma D_541f0 : decode_any W_541f0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541f4 : bv 32 := 0x00090693.
Lemma F_541f4 : fetch_word AsanUbsan.M.loaded_segments (0x541f4 : word) = Some W_541f4.
Proof. vm_refl. Qed.
Lemma D_541f4 : decode_any W_541f4 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541f8 : bv 32 := 0x00000713.
Lemma F_541f8 : fetch_word AsanUbsan.M.loaded_segments (0x541f8 : word) = Some W_541f8.
Proof. vm_refl. Qed.
Lemma D_541f8 : decode_any W_541f8 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_541fc : bv 32 := 0x00048793.
Lemma F_541fc : fetch_word AsanUbsan.M.loaded_segments (0x541fc : word) = Some W_541fc.
Proof. vm_refl. Qed.
Lemma D_541fc : decode_any W_541fc = Some (OpImm ALU_ADD 15 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54200 : bv 32 := 0x00000813.
Lemma F_54200 : fetch_word AsanUbsan.M.loaded_segments (0x54200 : word) = Some W_54200.
Proof. vm_refl. Qed.
Lemma D_54200 : decode_any W_54200 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54204 : bv 32 := 0x00000893.
Lemma F_54204 : fetch_word AsanUbsan.M.loaded_segments (0x54204 : word) = Some W_54204.
Proof. vm_refl. Qed.
Lemma D_54204 : decode_any W_54204 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54208 : bv 32 := 0x4d1050ef.
Lemma F_54208 : fetch_word AsanUbsan.M.loaded_segments (0x54208 : word) = Some W_54208.
Proof. vm_refl. Qed.
Lemma D_54208 : decode_any W_54208 = Some (Jal 1 23760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5420c : bv 32 := 0x000a8513.
Lemma F_5420c : fetch_word AsanUbsan.M.loaded_segments (0x5420c : word) = Some W_5420c.
Proof. vm_refl. Qed.
Lemma D_5420c : decode_any W_5420c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54210 : bv 32 := 0x000b8593.
Lemma F_54210 : fetch_word AsanUbsan.M.loaded_segments (0x54210 : word) = Some W_54210.
Proof. vm_refl. Qed.
Lemma D_54210 : decode_any W_54210 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54214 : bv 32 := 0x00048613.
Lemma F_54214 : fetch_word AsanUbsan.M.loaded_segments (0x54214 : word) = Some W_54214.
Proof. vm_refl. Qed.
Lemma D_54214 : decode_any W_54214 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54218 : bv 32 := 0xcb1ff06f.
Lemma F_54218 : fetch_word AsanUbsan.M.loaded_segments (0x54218 : word) = Some W_54218.
Proof. vm_refl. Qed.
Lemma D_54218 : decode_any W_54218 = Some (Jal 0 2096304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5421c : bv 32 := 0x00070783.
Lemma F_5421c : fetch_word AsanUbsan.M.loaded_segments (0x5421c : word) = Some W_5421c.
Proof. vm_refl. Qed.
Lemma D_5421c : decode_any W_5421c = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54220 : bv 32 := 0x0079f813.
Lemma F_54220 : fetch_word AsanUbsan.M.loaded_segments (0x54220 : word) = Some W_54220.
Proof. vm_refl. Qed.
Lemma D_54220 : decode_any W_54220 = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54224 : bv 32 := 0x00f038b3.
Lemma F_54224 : fetch_word AsanUbsan.M.loaded_segments (0x54224 : word) = Some W_54224.
Proof. vm_refl. Qed.
Lemma D_54224 : decode_any W_54224 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54228 : bv 32 := 0x00f827b3.
Lemma F_54228 : fetch_word AsanUbsan.M.loaded_segments (0x54228 : word) = Some W_54228.
Proof. vm_refl. Qed.
Lemma D_54228 : decode_any W_54228 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5422c : bv 32 := 0x0017c793.
Lemma F_5422c : fetch_word AsanUbsan.M.loaded_segments (0x5422c : word) = Some W_5422c.
Proof. vm_refl. Qed.
Lemma D_5422c : decode_any W_5422c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54230 : bv 32 := 0x00f8f7b3.
Lemma F_54230 : fetch_word AsanUbsan.M.loaded_segments (0x54230 : word) = Some W_54230.
Proof. vm_refl. Qed.
Lemma D_54230 : decode_any W_54230 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54234 : bv 32 := 0x00e6fa63.
Lemma F_54234 : fetch_word AsanUbsan.M.loaded_segments (0x54234 : word) = Some W_54234.
Proof. vm_refl. Qed.
Lemma D_54234 : decode_any W_54234 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54238 : bv 32 := 0x0006c803.
Lemma F_54238 : fetch_word AsanUbsan.M.loaded_segments (0x54238 : word) = Some W_54238.
Proof. vm_refl. Qed.
Lemma D_54238 : decode_any W_54238 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5423c : bv 32 := 0x00168693.
Lemma F_5423c : fetch_word AsanUbsan.M.loaded_segments (0x5423c : word) = Some W_5423c.
Proof. vm_refl. Qed.
Lemma D_5423c : decode_any W_5423c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54240 : bv 32 := 0x00f867b3.
Lemma F_54240 : fetch_word AsanUbsan.M.loaded_segments (0x54240 : word) = Some W_54240.
Proof. vm_refl. Qed.
Lemma D_54240 : decode_any W_54240 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54244 : bv 32 := 0xfee69ae3.
Lemma F_54244 : fetch_word AsanUbsan.M.loaded_segments (0x54244 : word) = Some W_54244.
Proof. vm_refl. Qed.
Lemma D_54244 : decode_any W_54244 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54248 : bv 32 := 0x0ff7f693.
Lemma F_54248 : fetch_word AsanUbsan.M.loaded_segments (0x54248 : word) = Some W_54248.
Proof. vm_refl. Qed.
Lemma D_54248 : decode_any W_54248 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5424c : bv 32 := 0xcc0682e3.
Lemma F_5424c : fetch_word AsanUbsan.M.loaded_segments (0x5424c : word) = Some W_5424c.
Proof. vm_refl. Qed.
Lemma D_5424c : decode_any W_5424c = Some (Branch BC_EQ 13 0 7364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54250 : bv 32 := 0x00050493.
Lemma F_54250 : fetch_word AsanUbsan.M.loaded_segments (0x54250 : word) = Some W_54250.
Proof. vm_refl. Qed.
Lemma D_54250 : decode_any W_54250 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54254 : bv 32 := 0x00058a93.
Lemma F_54254 : fetch_word AsanUbsan.M.loaded_segments (0x54254 : word) = Some W_54254.
Proof. vm_refl. Qed.
Lemma D_54254 : decode_any W_54254 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54258 : bv 32 := 0x00060593.
Lemma F_54258 : fetch_word AsanUbsan.M.loaded_segments (0x54258 : word) = Some W_54258.
Proof. vm_refl. Qed.
Lemma D_54258 : decode_any W_54258 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5425c : bv 32 := 0x00060913.
Lemma F_5425c : fetch_word AsanUbsan.M.loaded_segments (0x5425c : word) = Some W_5425c.
Proof. vm_refl. Qed.
Lemma D_5425c : decode_any W_5425c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54260 : bv 32 := 0x73c020ef.
Lemma F_54260 : fetch_word AsanUbsan.M.loaded_segments (0x54260 : word) = Some W_54260.
Proof. vm_refl. Qed.
Lemma D_54260 : decode_any W_54260 = Some (Jal 1 10044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54264 : bv 32 := 0x000a8593.
Lemma F_54264 : fetch_word AsanUbsan.M.loaded_segments (0x54264 : word) = Some W_54264.
Proof. vm_refl. Qed.
Lemma D_54264 : decode_any W_54264 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54268 : bv 32 := 0x00090613.
Lemma F_54268 : fetch_word AsanUbsan.M.loaded_segments (0x54268 : word) = Some W_54268.
Proof. vm_refl. Qed.
Lemma D_54268 : decode_any W_54268 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5426c : bv 32 := 0x00050993.
Lemma F_5426c : fetch_word AsanUbsan.M.loaded_segments (0x5426c : word) = Some W_5426c.
Proof. vm_refl. Qed.
Lemma D_5426c : decode_any W_5426c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54270 : bv 32 := 0x00048513.
Lemma F_54270 : fetch_word AsanUbsan.M.loaded_segments (0x54270 : word) = Some W_54270.
Proof. vm_refl. Qed.
Lemma D_54270 : decode_any W_54270 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54274 : bv 32 := 0xc8098ee3.
Lemma F_54274 : fetch_word AsanUbsan.M.loaded_segments (0x54274 : word) = Some W_54274.
Proof. vm_refl. Qed.
Lemma D_54274 : decode_any W_54274 = Some (Branch BC_EQ 19 0 7324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54278 : bv 32 := 0x400210ef.
Lemma F_54278 : fetch_word AsanUbsan.M.loaded_segments (0x54278 : word) = Some W_54278.
Proof. vm_refl. Qed.
Lemma D_54278 : decode_any W_54278 = Some (Jal 1 136192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5427c : bv 32 := 0xfffbc597.
Lemma F_5427c : fetch_word AsanUbsan.M.loaded_segments (0x5427c : word) = Some W_5427c.
Proof. vm_refl. Qed.
Lemma D_5427c : decode_any W_5427c = Some (Auipc 11 1048508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54280 : bv 32 := 0x17c5b583.
Lemma F_54280 : fetch_word AsanUbsan.M.loaded_segments (0x54280 : word) = Some W_54280.
Proof. vm_refl. Qed.
Lemma D_54280 : decode_any W_54280 = Some (Load SZ8 true 11 11 380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54284 : bv 32 := 0x00ba3023.
Lemma F_54284 : fetch_word AsanUbsan.M.loaded_segments (0x54284 : word) = Some W_54284.
Proof. vm_refl. Qed.
Lemma D_54284 : decode_any W_54284 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54288 : bv 32 := 0x80040613.
Lemma F_54288 : fetch_word AsanUbsan.M.loaded_segments (0x54288 : word) = Some W_54288.
Proof. vm_refl. Qed.
Lemma D_54288 : decode_any W_54288 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5428c : bv 32 := 0xfa060613.
Lemma F_5428c : fetch_word AsanUbsan.M.loaded_segments (0x5428c : word) = Some W_5428c.
Proof. vm_refl. Qed.
Lemma D_5428c : decode_any W_5428c = Some (OpImm ALU_ADD 12 12 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54290 : bv 32 := 0x00100713.
Lemma F_54290 : fetch_word AsanUbsan.M.loaded_segments (0x54290 : word) = Some W_54290.
Proof. vm_refl. Qed.
Lemma D_54290 : decode_any W_54290 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54294 : bv 32 := 0x00040593.
Lemma F_54294 : fetch_word AsanUbsan.M.loaded_segments (0x54294 : word) = Some W_54294.
Proof. vm_refl. Qed.
Lemma D_54294 : decode_any W_54294 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54298 : bv 32 := 0x00098693.
Lemma F_54298 : fetch_word AsanUbsan.M.loaded_segments (0x54298 : word) = Some W_54298.
Proof. vm_refl. Qed.
Lemma D_54298 : decode_any W_54298 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5429c : bv 32 := 0x00090793.
Lemma F_5429c : fetch_word AsanUbsan.M.loaded_segments (0x5429c : word) = Some W_5429c.
Proof. vm_refl. Qed.
Lemma D_5429c : decode_any W_5429c = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542a0 : bv 32 := 0x00000813.
Lemma F_542a0 : fetch_word AsanUbsan.M.loaded_segments (0x542a0 : word) = Some W_542a0.
Proof. vm_refl. Qed.
Lemma D_542a0 : decode_any W_542a0 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542a4 : bv 32 := 0x00000893.
Lemma F_542a4 : fetch_word AsanUbsan.M.loaded_segments (0x542a4 : word) = Some W_542a4.
Proof. vm_refl. Qed.
Lemma D_542a4 : decode_any W_542a4 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542a8 : bv 32 := 0x431050ef.
Lemma F_542a8 : fetch_word AsanUbsan.M.loaded_segments (0x542a8 : word) = Some W_542a8.
Proof. vm_refl. Qed.
Lemma D_542a8 : decode_any W_542a8 = Some (Jal 1 23600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542ac : bv 32 := 0x00048513.
Lemma F_542ac : fetch_word AsanUbsan.M.loaded_segments (0x542ac : word) = Some W_542ac.
Proof. vm_refl. Qed.
Lemma D_542ac : decode_any W_542ac = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542b0 : bv 32 := 0x000a8593.
Lemma F_542b0 : fetch_word AsanUbsan.M.loaded_segments (0x542b0 : word) = Some W_542b0.
Proof. vm_refl. Qed.
Lemma D_542b0 : decode_any W_542b0 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542b4 : bv 32 := 0x00090613.
Lemma F_542b4 : fetch_word AsanUbsan.M.loaded_segments (0x542b4 : word) = Some W_542b4.
Proof. vm_refl. Qed.
Lemma D_542b4 : decode_any W_542b4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542b8 : bv 32 := 0xc59ff06f.
Lemma F_542b8 : fetch_word AsanUbsan.M.loaded_segments (0x542b8 : word) = Some W_542b8.
Proof. vm_refl. Qed.
Lemma D_542b8 : decode_any W_542b8 = Some (Jal 0 2096216, 4%Z).
Proof. vm_refl. Qed.
