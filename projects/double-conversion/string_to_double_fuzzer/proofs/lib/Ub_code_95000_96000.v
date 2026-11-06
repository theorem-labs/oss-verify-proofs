(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation USEGS := ImgU.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_95e20 : bv 32 := 0x00008067.
Lemma F_95e20 : fetch_word USEGS (0x95e20 : word) = Some W_95e20.
Proof. vm_refl. Qed.
Lemma D_95e20 : decode_any W_95e20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e24 : bv 32 := 0xe8010113.
Lemma F_95e24 : fetch_word USEGS (0x95e24 : word) = Some W_95e24.
Proof. vm_refl. Qed.
Lemma D_95e24 : decode_any W_95e24 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e28 : bv 32 := 0x16113c23.
Lemma F_95e28 : fetch_word USEGS (0x95e28 : word) = Some W_95e28.
Proof. vm_refl. Qed.
Lemma D_95e28 : decode_any W_95e28 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e2c : bv 32 := 0x16813823.
Lemma F_95e2c : fetch_word USEGS (0x95e2c : word) = Some W_95e2c.
Proof. vm_refl. Qed.
Lemma D_95e2c : decode_any W_95e2c = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e30 : bv 32 := 0x16913423.
Lemma F_95e30 : fetch_word USEGS (0x95e30 : word) = Some W_95e30.
Proof. vm_refl. Qed.
Lemma D_95e30 : decode_any W_95e30 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e34 : bv 32 := 0x17213023.
Lemma F_95e34 : fetch_word USEGS (0x95e34 : word) = Some W_95e34.
Proof. vm_refl. Qed.
Lemma D_95e34 : decode_any W_95e34 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e38 : bv 32 := 0x00058413.
Lemma F_95e38 : fetch_word USEGS (0x95e38 : word) = Some W_95e38.
Proof. vm_refl. Qed.
Lemma D_95e38 : decode_any W_95e38 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e3c : bv 32 := 0x00050493.
Lemma F_95e3c : fetch_word USEGS (0x95e3c : word) = Some W_95e3c.
Proof. vm_refl. Qed.
Lemma D_95e3c : decode_any W_95e3c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e40 : bv 32 := 0x03010513.
Lemma F_95e40 : fetch_word USEGS (0x95e40 : word) = Some W_95e40.
Proof. vm_refl. Qed.
Lemma D_95e40 : decode_any W_95e40 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e44 : bv 32 := 0x13000613.
Lemma F_95e44 : fetch_word USEGS (0x95e44 : word) = Some W_95e44.
Proof. vm_refl. Qed.
Lemma D_95e44 : decode_any W_95e44 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e48 : bv 32 := 0x00000593.
Lemma F_95e48 : fetch_word USEGS (0x95e48 : word) = Some W_95e48.
Proof. vm_refl. Qed.
Lemma D_95e48 : decode_any W_95e48 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e4c : bv 32 := 0x554110ef.
Lemma F_95e4c : fetch_word USEGS (0x95e4c : word) = Some W_95e4c.
Proof. vm_refl. Qed.
Lemma D_95e4c : decode_any W_95e4c = Some (Jal 1 70996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e50 : bv 32 := 0x0001c517.
Lemma F_95e50 : fetch_word USEGS (0x95e50 : word) = Some W_95e50.
Proof. vm_refl. Qed.
Lemma D_95e50 : decode_any W_95e50 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e54 : bv 32 := 0x43053503.
Lemma F_95e54 : fetch_word USEGS (0x95e54 : word) = Some W_95e54.
Proof. vm_refl. Qed.
Lemma D_95e54 : decode_any W_95e54 = Some (Load SZ8 true 10 10 1072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e58 : bv 32 := 0x00953023.
Lemma F_95e58 : fetch_word USEGS (0x95e58 : word) = Some W_95e58.
Proof. vm_refl. Qed.
Lemma D_95e58 : decode_any W_95e58 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e5c : bv 32 := 0x0004b503.
Lemma F_95e5c : fetch_word USEGS (0x95e5c : word) = Some W_95e5c.
Proof. vm_refl. Qed.
Lemma D_95e5c : decode_any W_95e5c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e60 : bv 32 := 0x00848493.
Lemma F_95e60 : fetch_word USEGS (0x95e60 : word) = Some W_95e60.
Proof. vm_refl. Qed.
Lemma D_95e60 : decode_any W_95e60 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e64 : bv 32 := 0xfe051ce3.
Lemma F_95e64 : fetch_word USEGS (0x95e64 : word) = Some W_95e64.
Proof. vm_refl. Qed.
Lemma D_95e64 : decode_any W_95e64 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e68 : bv 32 := 0x0004f517.
Lemma F_95e68 : fetch_word USEGS (0x95e68 : word) = Some W_95e68.
Proof. vm_refl. Qed.
Lemma D_95e68 : decode_any W_95e68 = Some (Auipc 10 79, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e6c : bv 32 := 0x44050913.
Lemma F_95e6c : fetch_word USEGS (0x95e6c : word) = Some W_95e6c.
Proof. vm_refl. Qed.
Lemma D_95e6c : decode_any W_95e6c = Some (OpImm ALU_ADD 18 10 1088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e70 : bv 32 := 0x00993423.
Lemma F_95e70 : fetch_word USEGS (0x95e70 : word) = Some W_95e70.
Proof. vm_refl. Qed.
Lemma D_95e70 : decode_any W_95e70 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e74 : bv 32 := 0x0004b583.
Lemma F_95e74 : fetch_word USEGS (0x95e74 : word) = Some W_95e74.
Proof. vm_refl. Qed.
Lemma D_95e74 : decode_any W_95e74 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e78 : bv 32 := 0x04058c63.
Lemma F_95e78 : fetch_word USEGS (0x95e78 : word) = Some W_95e78.
Proof. vm_refl. Qed.
Lemma D_95e78 : decode_any W_95e78 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e7c : bv 32 := 0x01048493.
Lemma F_95e7c : fetch_word USEGS (0x95e7c : word) = Some W_95e7c.
Proof. vm_refl. Qed.
Lemma D_95e7c : decode_any W_95e7c = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e80 : bv 32 := 0x02500513.
Lemma F_95e80 : fetch_word USEGS (0x95e80 : word) = Some W_95e80.
Proof. vm_refl. Qed.
Lemma D_95e80 : decode_any W_95e80 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e84 : bv 32 := 0x03010613.
Lemma F_95e84 : fetch_word USEGS (0x95e84 : word) = Some W_95e84.
Proof. vm_refl. Qed.
Lemma D_95e84 : decode_any W_95e84 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e88 : bv 32 := 0x0100006f.
Lemma F_95e88 : fetch_word USEGS (0x95e88 : word) = Some W_95e88.
Proof. vm_refl. Qed.
Lemma D_95e88 : decode_any W_95e88 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e8c : bv 32 := 0x0004b583.
Lemma F_95e8c : fetch_word USEGS (0x95e8c : word) = Some W_95e8c.
Proof. vm_refl. Qed.
Lemma D_95e8c : decode_any W_95e8c = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e90 : bv 32 := 0x01048493.
Lemma F_95e90 : fetch_word USEGS (0x95e90 : word) = Some W_95e90.
Proof. vm_refl. Qed.
Lemma D_95e90 : decode_any W_95e90 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e94 : bv 32 := 0x00058e63.
Lemma F_95e94 : fetch_word USEGS (0x95e94 : word) = Some W_95e94.
Proof. vm_refl. Qed.
Lemma D_95e94 : decode_any W_95e94 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e98 : bv 32 := 0xfeb56ae3.
Lemma F_95e98 : fetch_word USEGS (0x95e98 : word) = Some W_95e98.
Proof. vm_refl. Qed.
Lemma D_95e98 : decode_any W_95e98 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e9c : bv 32 := 0xff84b683.
Lemma F_95e9c : fetch_word USEGS (0x95e9c : word) = Some W_95e9c.
Proof. vm_refl. Qed.
Lemma D_95e9c : decode_any W_95e9c = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ea0 : bv 32 := 0x00359593.
Lemma F_95ea0 : fetch_word USEGS (0x95ea0 : word) = Some W_95ea0.
Proof. vm_refl. Qed.
Lemma D_95ea0 : decode_any W_95ea0 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ea4 : bv 32 := 0x00b605b3.
Lemma F_95ea4 : fetch_word USEGS (0x95ea4 : word) = Some W_95ea4.
Proof. vm_refl. Qed.
Lemma D_95ea4 : decode_any W_95ea4 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ea8 : bv 32 := 0x00d5b023.
Lemma F_95ea8 : fetch_word USEGS (0x95ea8 : word) = Some W_95ea8.
Proof. vm_refl. Qed.
Lemma D_95ea8 : decode_any W_95ea8 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95eac : bv 32 := 0xfe1ff06f.
Lemma F_95eac : fetch_word USEGS (0x95eac : word) = Some W_95eac.
Proof. vm_refl. Qed.
Lemma D_95eac : decode_any W_95eac = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95eb0 : bv 32 := 0x0b013583.
Lemma F_95eb0 : fetch_word USEGS (0x95eb0 : word) = Some W_95eb0.
Proof. vm_refl. Qed.
Lemma D_95eb0 : decode_any W_95eb0 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95eb4 : bv 32 := 0x13013503.
Lemma F_95eb4 : fetch_word USEGS (0x95eb4 : word) = Some W_95eb4.
Proof. vm_refl. Qed.
Lemma D_95eb4 : decode_any W_95eb4 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95eb8 : bv 32 := 0x0004f617.
Lemma F_95eb8 : fetch_word USEGS (0x95eb8 : word) = Some W_95eb8.
Proof. vm_refl. Qed.
Lemma D_95eb8 : decode_any W_95eb8 = Some (Auipc 12 79, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ebc : bv 32 := 0x44b63c23.
Lemma F_95ebc : fetch_word USEGS (0x95ebc : word) = Some W_95ebc.
Proof. vm_refl. Qed.
Lemma D_95ebc : decode_any W_95ebc = Some (Store SZ8 12 11 1112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ec0 : bv 32 := 0x00050c63.
Lemma F_95ec0 : fetch_word USEGS (0x95ec0 : word) = Some W_95ec0.
Proof. vm_refl. Qed.
Lemma D_95ec0 : decode_any W_95ec0 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ed8 : bv 32 := 0x06013503.
Lemma F_95ed8 : fetch_word USEGS (0x95ed8 : word) = Some W_95ed8.
Proof. vm_refl. Qed.
Lemma D_95ed8 : decode_any W_95ed8 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95edc : bv 32 := 0x02a93823.
Lemma F_95edc : fetch_word USEGS (0x95edc : word) = Some W_95edc.
Proof. vm_refl. Qed.
Lemma D_95edc : decode_any W_95edc = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ee0 : bv 32 := 0x00041463.
Lemma F_95ee0 : fetch_word USEGS (0x95ee0 : word) = Some W_95ee0.
Proof. vm_refl. Qed.
Lemma D_95ee0 : decode_any W_95ee0 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ee8 : bv 32 := 0x00041663.
Lemma F_95ee8 : fetch_word USEGS (0x95ee8 : word) = Some W_95ee8.
Proof. vm_refl. Qed.
Lemma D_95ee8 : decode_any W_95ee8 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ef4 : bv 32 := 0x0001c517.
Lemma F_95ef4 : fetch_word USEGS (0x95ef4 : word) = Some W_95ef4.
Proof. vm_refl. Qed.
Lemma D_95ef4 : decode_any W_95ef4 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ef8 : bv 32 := 0x39453583.
Lemma F_95ef8 : fetch_word USEGS (0x95ef8 : word) = Some W_95ef8.
Proof. vm_refl. Qed.
Lemma D_95ef8 : decode_any W_95ef8 = Some (Load SZ8 true 11 10 916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95efc : bv 32 := 0x0001c517.
Lemma F_95efc : fetch_word USEGS (0x95efc : word) = Some W_95efc.
Proof. vm_refl. Qed.
Lemma D_95efc : decode_any W_95efc = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f00 : bv 32 := 0x39453503.
Lemma F_95f00 : fetch_word USEGS (0x95f00 : word) = Some W_95f00.
Proof. vm_refl. Qed.
Lemma D_95f00 : decode_any W_95f00 = Some (Load SZ8 true 10 10 916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f04 : bv 32 := 0x0085b023.
Lemma F_95f04 : fetch_word USEGS (0x95f04 : word) = Some W_95f04.
Proof. vm_refl. Qed.
Lemma D_95f04 : decode_any W_95f04 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f08 : bv 32 := 0x00140593.
Lemma F_95f08 : fetch_word USEGS (0x95f08 : word) = Some W_95f08.
Proof. vm_refl. Qed.
Lemma D_95f08 : decode_any W_95f08 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f0c : bv 32 := 0x00853023.
Lemma F_95f0c : fetch_word USEGS (0x95f0c : word) = Some W_95f0c.
Proof. vm_refl. Qed.
Lemma D_95f0c : decode_any W_95f0c = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f10 : bv 32 := 0x02f00613.
Lemma F_95f10 : fetch_word USEGS (0x95f10 : word) = Some W_95f10.
Proof. vm_refl. Qed.
Lemma D_95f10 : decode_any W_95f10 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f14 : bv 32 := 0x00c0006f.
Lemma F_95f14 : fetch_word USEGS (0x95f14 : word) = Some W_95f14.
Proof. vm_refl. Qed.
Lemma D_95f14 : decode_any W_95f14 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f18 : bv 32 := 0x00b53023.
Lemma F_95f18 : fetch_word USEGS (0x95f18 : word) = Some W_95f18.
Proof. vm_refl. Qed.
Lemma D_95f18 : decode_any W_95f18 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f1c : bv 32 := 0x00158593.
Lemma F_95f1c : fetch_word USEGS (0x95f1c : word) = Some W_95f1c.
Proof. vm_refl. Qed.
Lemma D_95f1c : decode_any W_95f1c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f20 : bv 32 := 0xfff5c683.
Lemma F_95f20 : fetch_word USEGS (0x95f20 : word) = Some W_95f20.
Proof. vm_refl. Qed.
Lemma D_95f20 : decode_any W_95f20 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f24 : bv 32 := 0xfec68ae3.
Lemma F_95f24 : fetch_word USEGS (0x95f24 : word) = Some W_95f24.
Proof. vm_refl. Qed.
Lemma D_95f24 : decode_any W_95f24 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f28 : bv 32 := 0xfe069ae3.
Lemma F_95f28 : fetch_word USEGS (0x95f28 : word) = Some W_95f28.
Proof. vm_refl. Qed.
Lemma D_95f28 : decode_any W_95f28 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f2c : bv 32 := 0x03010513.
Lemma F_95f2c : fetch_word USEGS (0x95f2c : word) = Some W_95f2c.
Proof. vm_refl. Qed.
Lemma D_95f2c : decode_any W_95f2c = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f30 : bv 32 := 0x214000ef.
Lemma F_95f30 : fetch_word USEGS (0x95f30 : word) = Some W_95f30.
Proof. vm_refl. Qed.
Lemma D_95f30 : decode_any W_95f30 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f34 : bv 32 := 0x0f813503.
Lemma F_95f34 : fetch_word USEGS (0x95f34 : word) = Some W_95f34.
Proof. vm_refl. Qed.
Lemma D_95f34 : decode_any W_95f34 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f38 : bv 32 := 0x1ad000ef.
Lemma F_95f38 : fetch_word USEGS (0x95f38 : word) = Some W_95f38.
Proof. vm_refl. Qed.
Lemma D_95f38 : decode_any W_95f38 = Some (Jal 1 2476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f3c : bv 32 := 0x08813503.
Lemma F_95f3c : fetch_word USEGS (0x95f3c : word) = Some W_95f3c.
Proof. vm_refl. Qed.
Lemma D_95f3c : decode_any W_95f3c = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f40 : bv 32 := 0x09013583.
Lemma F_95f40 : fetch_word USEGS (0x95f40 : word) = Some W_95f40.
Proof. vm_refl. Qed.
Lemma D_95f40 : decode_any W_95f40 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f44 : bv 32 := 0x00b51c63.
Lemma F_95f44 : fetch_word USEGS (0x95f44 : word) = Some W_95f44.
Proof. vm_refl. Qed.
Lemma D_95f44 : decode_any W_95f44 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f48 : bv 32 := 0x09813503.
Lemma F_95f48 : fetch_word USEGS (0x95f48 : word) = Some W_95f48.
Proof. vm_refl. Qed.
Lemma D_95f48 : decode_any W_95f48 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f4c : bv 32 := 0x0a013583.
Lemma F_95f4c : fetch_word USEGS (0x95f4c : word) = Some W_95f4c.
Proof. vm_refl. Qed.
Lemma D_95f4c : decode_any W_95f4c = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f50 : bv 32 := 0x00b51663.
Lemma F_95f50 : fetch_word USEGS (0x95f50 : word) = Some W_95f50.
Proof. vm_refl. Qed.
Lemma D_95f50 : decode_any W_95f50 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f54 : bv 32 := 0x0e813503.
Lemma F_95f54 : fetch_word USEGS (0x95f54 : word) = Some W_95f54.
Proof. vm_refl. Qed.
Lemma D_95f54 : decode_any W_95f54 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f58 : bv 32 := 0x0e050063.
Lemma F_95f58 : fetch_word USEGS (0x95f58 : word) = Some W_95f58.
Proof. vm_refl. Qed.
Lemma D_95f58 : decode_any W_95f58 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f88 : bv 32 := 0x02d13423.
Lemma F_95f88 : fetch_word USEGS (0x95f88 : word) = Some W_95f88.
Proof. vm_refl. Qed.
Lemma D_95f88 : decode_any W_95f88 = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f8c : bv 32 := 0x00000693.
Lemma F_95f8c : fetch_word USEGS (0x95f8c : word) = Some W_95f8c.
Proof. vm_refl. Qed.
Lemma D_95f8c : decode_any W_95f8c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f90 : bv 32 := 0x00000073.
Lemma F_95f90 : fetch_word USEGS (0x95f90 : word) = Some W_95f90.
Proof. vm_refl. Qed.
Lemma D_95f90 : decode_any W_95f90 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_95f90 : is_ecall W_95f90 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_95f94 : bv 32 := 0x02051513.
Lemma F_95f94 : fetch_word USEGS (0x95f94 : word) = Some W_95f94.
Proof. vm_refl. Qed.
Lemma D_95f94 : decode_any W_95f94 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f98 : bv 32 := 0x00055463.
Lemma F_95f98 : fetch_word USEGS (0x95f98 : word) = Some W_95f98.
Proof. vm_refl. Qed.
Lemma D_95f98 : decode_any W_95f98 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f9c : bv 32 := 0x00000023.
Lemma F_95f9c : fetch_word USEGS (0x95f9c : word) = Some W_95f9c.
Proof. vm_refl. Qed.
Lemma D_95f9c : decode_any W_95f9c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fa0 : bv 32 := 0x01e15503.
Lemma F_95fa0 : fetch_word USEGS (0x95fa0 : word) = Some W_95fa0.
Proof. vm_refl. Qed.
Lemma D_95fa0 : decode_any W_95fa0 = Some (Load SZ2 false 10 2 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fa4 : bv 32 := 0x02057513.
Lemma F_95fa4 : fetch_word USEGS (0x95fa4 : word) = Some W_95fa4.
Proof. vm_refl. Qed.
Lemma D_95fa4 : decode_any W_95fa4 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fa8 : bv 32 := 0x02050463.
Lemma F_95fa8 : fetch_word USEGS (0x95fa8 : word) = Some W_95fa8.
Proof. vm_refl. Qed.
Lemma D_95fa8 : decode_any W_95fa8 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fac : bv 32 := 0xfff7d517.
Lemma F_95fac : fetch_word USEGS (0x95fac : word) = Some W_95fac.
Proof. vm_refl. Qed.
Lemma D_95fac : decode_any W_95fac = Some (Auipc 10 1048445, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fb0 : bv 32 := 0x00008637.
Lemma F_95fb0 : fetch_word USEGS (0x95fb0 : word) = Some W_95fb0.
Proof. vm_refl. Qed.
Lemma D_95fb0 : decode_any W_95fb0 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fb4 : bv 32 := 0x03800893.
Lemma F_95fb4 : fetch_word USEGS (0x95fb4 : word) = Some W_95fb4.
Proof. vm_refl. Qed.
Lemma D_95fb4 : decode_any W_95fb4 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fb8 : bv 32 := 0x31850593.
Lemma F_95fb8 : fetch_word USEGS (0x95fb8 : word) = Some W_95fb8.
Proof. vm_refl. Qed.
Lemma D_95fb8 : decode_any W_95fb8 = Some (OpImm ALU_ADD 11 10 792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fbc : bv 32 := 0x0026061b.
Lemma F_95fbc : fetch_word USEGS (0x95fbc : word) = Some W_95fbc.
Proof. vm_refl. Qed.
Lemma D_95fbc : decode_any W_95fbc = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fc0 : bv 32 := 0xf9c00513.
Lemma F_95fc0 : fetch_word USEGS (0x95fc0 : word) = Some W_95fc0.
Proof. vm_refl. Qed.
Lemma D_95fc0 : decode_any W_95fc0 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fc4 : bv 32 := 0x00000073.
Lemma F_95fc4 : fetch_word USEGS (0x95fc4 : word) = Some W_95fc4.
Proof. vm_refl. Qed.
Lemma D_95fc4 : decode_any W_95fc4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_95fc4 : is_ecall W_95fc4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_95fc8 : bv 32 := 0x00055463.
Lemma F_95fc8 : fetch_word USEGS (0x95fc8 : word) = Some W_95fc8.
Proof. vm_refl. Qed.
Lemma D_95fc8 : decode_any W_95fc8 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fcc : bv 32 := 0x00000023.
Lemma F_95fcc : fetch_word USEGS (0x95fcc : word) = Some W_95fcc.
Proof. vm_refl. Qed.
Lemma D_95fcc : decode_any W_95fcc = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fd0 : bv 32 := 0x02615503.
Lemma F_95fd0 : fetch_word USEGS (0x95fd0 : word) = Some W_95fd0.
Proof. vm_refl. Qed.
Lemma D_95fd0 : decode_any W_95fd0 = Some (Load SZ2 false 10 2 38, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fd4 : bv 32 := 0x02057513.
Lemma F_95fd4 : fetch_word USEGS (0x95fd4 : word) = Some W_95fd4.
Proof. vm_refl. Qed.
Lemma D_95fd4 : decode_any W_95fd4 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fd8 : bv 32 := 0x02050463.
Lemma F_95fd8 : fetch_word USEGS (0x95fd8 : word) = Some W_95fd8.
Proof. vm_refl. Qed.
Lemma D_95fd8 : decode_any W_95fd8 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fdc : bv 32 := 0xfff7d517.
Lemma F_95fdc : fetch_word USEGS (0x95fdc : word) = Some W_95fdc.
Proof. vm_refl. Qed.
Lemma D_95fdc : decode_any W_95fdc = Some (Auipc 10 1048445, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fe0 : bv 32 := 0x00008637.
Lemma F_95fe0 : fetch_word USEGS (0x95fe0 : word) = Some W_95fe0.
Proof. vm_refl. Qed.
Lemma D_95fe0 : decode_any W_95fe0 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fe4 : bv 32 := 0x03800893.
Lemma F_95fe4 : fetch_word USEGS (0x95fe4 : word) = Some W_95fe4.
Proof. vm_refl. Qed.
Lemma D_95fe4 : decode_any W_95fe4 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fe8 : bv 32 := 0x2e850593.
Lemma F_95fe8 : fetch_word USEGS (0x95fe8 : word) = Some W_95fe8.
Proof. vm_refl. Qed.
Lemma D_95fe8 : decode_any W_95fe8 = Some (OpImm ALU_ADD 11 10 744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fec : bv 32 := 0x0026061b.
Lemma F_95fec : fetch_word USEGS (0x95fec : word) = Some W_95fec.
Proof. vm_refl. Qed.
Lemma D_95fec : decode_any W_95fec = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ff0 : bv 32 := 0xf9c00513.
Lemma F_95ff0 : fetch_word USEGS (0x95ff0 : word) = Some W_95ff0.
Proof. vm_refl. Qed.
Lemma D_95ff0 : decode_any W_95ff0 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ff4 : bv 32 := 0x00000073.
Lemma F_95ff4 : fetch_word USEGS (0x95ff4 : word) = Some W_95ff4.
Proof. vm_refl. Qed.
Lemma D_95ff4 : decode_any W_95ff4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_95ff4 : is_ecall W_95ff4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_95ff8 : bv 32 := 0x00055463.
Lemma F_95ff8 : fetch_word USEGS (0x95ff8 : word) = Some W_95ff8.
Proof. vm_refl. Qed.
Lemma D_95ff8 : decode_any W_95ff8 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ffc : bv 32 := 0x00000023.
Lemma F_95ffc : fetch_word USEGS (0x95ffc : word) = Some W_95ffc.
Proof. vm_refl. Qed.
Lemma D_95ffc : decode_any W_95ffc = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96000 : bv 32 := 0x02e15503.
Lemma F_96000 : fetch_word USEGS (0x96000 : word) = Some W_96000.
Proof. vm_refl. Qed.
Lemma D_96000 : decode_any W_96000 = Some (Load SZ2 false 10 2 46, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96004 : bv 32 := 0x02057513.
Lemma F_96004 : fetch_word USEGS (0x96004 : word) = Some W_96004.
Proof. vm_refl. Qed.
Lemma D_96004 : decode_any W_96004 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96008 : bv 32 := 0x02050463.
Lemma F_96008 : fetch_word USEGS (0x96008 : word) = Some W_96008.
Proof. vm_refl. Qed.
Lemma D_96008 : decode_any W_96008 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9600c : bv 32 := 0xfff7d517.
Lemma F_9600c : fetch_word USEGS (0x9600c : word) = Some W_9600c.
Proof. vm_refl. Qed.
Lemma D_9600c : decode_any W_9600c = Some (Auipc 10 1048445, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96010 : bv 32 := 0x00008637.
Lemma F_96010 : fetch_word USEGS (0x96010 : word) = Some W_96010.
Proof. vm_refl. Qed.
Lemma D_96010 : decode_any W_96010 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96034 : bv 32 := 0x00a90123.
Lemma F_96034 : fetch_word USEGS (0x96034 : word) = Some W_96034.
Proof. vm_refl. Qed.
Lemma D_96034 : decode_any W_96034 = Some (Store SZ1 18 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96038 : bv 32 := 0x17813083.
Lemma F_96038 : fetch_word USEGS (0x96038 : word) = Some W_96038.
Proof. vm_refl. Qed.
Lemma D_96038 : decode_any W_96038 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9603c : bv 32 := 0x17013403.
Lemma F_9603c : fetch_word USEGS (0x9603c : word) = Some W_9603c.
Proof. vm_refl. Qed.
Lemma D_9603c : decode_any W_9603c = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96040 : bv 32 := 0x16813483.
Lemma F_96040 : fetch_word USEGS (0x96040 : word) = Some W_96040.
Proof. vm_refl. Qed.
Lemma D_96040 : decode_any W_96040 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96044 : bv 32 := 0x16013903.
Lemma F_96044 : fetch_word USEGS (0x96044 : word) = Some W_96044.
Proof. vm_refl. Qed.
Lemma D_96044 : decode_any W_96044 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96048 : bv 32 := 0x18010113.
Lemma F_96048 : fetch_word USEGS (0x96048 : word) = Some W_96048.
Proof. vm_refl. Qed.
Lemma D_96048 : decode_any W_96048 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9604c : bv 32 := 0x00008067.
Lemma F_9604c : fetch_word USEGS (0x9604c : word) = Some W_9604c.
Proof. vm_refl. Qed.
Lemma D_9604c : decode_any W_9604c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96050 : bv 32 := 0xfe010113.
Lemma F_96050 : fetch_word USEGS (0x96050 : word) = Some W_96050.
Proof. vm_refl. Qed.
Lemma D_96050 : decode_any W_96050 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96054 : bv 32 := 0x00113c23.
Lemma F_96054 : fetch_word USEGS (0x96054 : word) = Some W_96054.
Proof. vm_refl. Qed.
Lemma D_96054 : decode_any W_96054 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96058 : bv 32 := 0x00813823.
Lemma F_96058 : fetch_word USEGS (0x96058 : word) = Some W_96058.
Proof. vm_refl. Qed.
Lemma D_96058 : decode_any W_96058 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9605c : bv 32 := 0x00913423.
Lemma F_9605c : fetch_word USEGS (0x9605c : word) = Some W_9605c.
Proof. vm_refl. Qed.
Lemma D_9605c : decode_any W_9605c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96060 : bv 32 := 0xdc1ff0ef.
Lemma F_96060 : fetch_word USEGS (0x96060 : word) = Some W_96060.
Proof. vm_refl. Qed.
Lemma D_96060 : decode_any W_96060 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96064 : bv 32 := 0x0001c517.
Lemma F_96064 : fetch_word USEGS (0x96064 : word) = Some W_96064.
Proof. vm_refl. Qed.
Lemma D_96064 : decode_any W_96064 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96068 : bv 32 := 0x0001c597.
Lemma F_96068 : fetch_word USEGS (0x96068 : word) = Some W_96068.
Proof. vm_refl. Qed.
Lemma D_96068 : decode_any W_96068 = Some (Auipc 11 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9606c : bv 32 := 0x23453403.
Lemma F_9606c : fetch_word USEGS (0x9606c : word) = Some W_9606c.
Proof. vm_refl. Qed.
Lemma D_9606c : decode_any W_9606c = Some (Load SZ8 true 8 10 564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96070 : bv 32 := 0x2385b483.
Lemma F_96070 : fetch_word USEGS (0x96070 : word) = Some W_96070.
Proof. vm_refl. Qed.
Lemma D_96070 : decode_any W_96070 = Some (Load SZ8 true 9 11 568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96074 : bv 32 := 0x0084fa63.
Lemma F_96074 : fetch_word USEGS (0x96074 : word) = Some W_96074.
Proof. vm_refl. Qed.
Lemma D_96074 : decode_any W_96074 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96078 : bv 32 := 0x0004b503.
Lemma F_96078 : fetch_word USEGS (0x96078 : word) = Some W_96078.
Proof. vm_refl. Qed.
Lemma D_96078 : decode_any W_96078 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9607c : bv 32 := 0x000500e7.
Lemma F_9607c : fetch_word USEGS (0x9607c : word) = Some W_9607c.
Proof. vm_refl. Qed.
Lemma D_9607c : decode_any W_9607c = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96080 : bv 32 := 0x00848493.
Lemma F_96080 : fetch_word USEGS (0x96080 : word) = Some W_96080.
Proof. vm_refl. Qed.
Lemma D_96080 : decode_any W_96080 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96084 : bv 32 := 0xfe84eae3.
Lemma F_96084 : fetch_word USEGS (0x96084 : word) = Some W_96084.
Proof. vm_refl. Qed.
Lemma D_96084 : decode_any W_96084 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96088 : bv 32 := 0x01813083.
Lemma F_96088 : fetch_word USEGS (0x96088 : word) = Some W_96088.
Proof. vm_refl. Qed.
Lemma D_96088 : decode_any W_96088 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9608c : bv 32 := 0x01013403.
Lemma F_9608c : fetch_word USEGS (0x9608c : word) = Some W_9608c.
Proof. vm_refl. Qed.
Lemma D_9608c : decode_any W_9608c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96090 : bv 32 := 0x00813483.
Lemma F_96090 : fetch_word USEGS (0x96090 : word) = Some W_96090.
Proof. vm_refl. Qed.
Lemma D_96090 : decode_any W_96090 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96094 : bv 32 := 0x02010113.
Lemma F_96094 : fetch_word USEGS (0x96094 : word) = Some W_96094.
Proof. vm_refl. Qed.
Lemma D_96094 : decode_any W_96094 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96098 : bv 32 := 0x00008067.
Lemma F_96098 : fetch_word USEGS (0x96098 : word) = Some W_96098.
Proof. vm_refl. Qed.
Lemma D_96098 : decode_any W_96098 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9609c : bv 32 := 0xfe010113.
Lemma F_9609c : fetch_word USEGS (0x9609c : word) = Some W_9609c.
Proof. vm_refl. Qed.
Lemma D_9609c : decode_any W_9609c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960a0 : bv 32 := 0x00113c23.
Lemma F_960a0 : fetch_word USEGS (0x960a0 : word) = Some W_960a0.
Proof. vm_refl. Qed.
Lemma D_960a0 : decode_any W_960a0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960a4 : bv 32 := 0x00813823.
Lemma F_960a4 : fetch_word USEGS (0x960a4 : word) = Some W_960a4.
Proof. vm_refl. Qed.
Lemma D_960a4 : decode_any W_960a4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960a8 : bv 32 := 0x00913423.
Lemma F_960a8 : fetch_word USEGS (0x960a8 : word) = Some W_960a8.
Proof. vm_refl. Qed.
Lemma D_960a8 : decode_any W_960a8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960ac : bv 32 := 0x01213023.
Lemma F_960ac : fetch_word USEGS (0x960ac : word) = Some W_960ac.
Proof. vm_refl. Qed.
Lemma D_960ac : decode_any W_960ac = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960b0 : bv 32 := 0x00060413.
Lemma F_960b0 : fetch_word USEGS (0x960b0 : word) = Some W_960b0.
Proof. vm_refl. Qed.
Lemma D_960b0 : decode_any W_960b0 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960b4 : bv 32 := 0x00058493.
Lemma F_960b4 : fetch_word USEGS (0x960b4 : word) = Some W_960b4.
Proof. vm_refl. Qed.
Lemma D_960b4 : decode_any W_960b4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960b8 : bv 32 := 0x00050913.
Lemma F_960b8 : fetch_word USEGS (0x960b8 : word) = Some W_960b8.
Proof. vm_refl. Qed.
Lemma D_960b8 : decode_any W_960b8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960bc : bv 32 := 0x00063583.
Lemma F_960bc : fetch_word USEGS (0x960bc : word) = Some W_960bc.
Proof. vm_refl. Qed.
Lemma D_960bc : decode_any W_960bc = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960c0 : bv 32 := 0x00349513.
Lemma F_960c0 : fetch_word USEGS (0x960c0 : word) = Some W_960c0.
Proof. vm_refl. Qed.
Lemma D_960c0 : decode_any W_960c0 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960c4 : bv 32 := 0x00a60533.
Lemma F_960c4 : fetch_word USEGS (0x960c4 : word) = Some W_960c4.
Proof. vm_refl. Qed.
Lemma D_960c4 : decode_any W_960c4 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960c8 : bv 32 := 0x00850513.
Lemma F_960c8 : fetch_word USEGS (0x960c8 : word) = Some W_960c8.
Proof. vm_refl. Qed.
Lemma D_960c8 : decode_any W_960c8 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960cc : bv 32 := 0xd59ff0ef.
Lemma F_960cc : fetch_word USEGS (0x960cc : word) = Some W_960cc.
Proof. vm_refl. Qed.
Lemma D_960cc : decode_any W_960cc = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960d0 : bv 32 := 0x00000517.
Lemma F_960d0 : fetch_word USEGS (0x960d0 : word) = Some W_960d0.
Proof. vm_refl. Qed.
Lemma D_960d0 : decode_any W_960d0 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960d4 : bv 32 := 0x02c50313.
Lemma F_960d4 : fetch_word USEGS (0x960d4 : word) = Some W_960d4.
Proof. vm_refl. Qed.
Lemma D_960d4 : decode_any W_960d4 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960d8 : bv 32 := 0x00090513.
Lemma F_960d8 : fetch_word USEGS (0x960d8 : word) = Some W_960d8.
Proof. vm_refl. Qed.
Lemma D_960d8 : decode_any W_960d8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960dc : bv 32 := 0x00048593.
Lemma F_960dc : fetch_word USEGS (0x960dc : word) = Some W_960dc.
Proof. vm_refl. Qed.
Lemma D_960dc : decode_any W_960dc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960e0 : bv 32 := 0x00040613.
Lemma F_960e0 : fetch_word USEGS (0x960e0 : word) = Some W_960e0.
Proof. vm_refl. Qed.
Lemma D_960e0 : decode_any W_960e0 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960e4 : bv 32 := 0x01813083.
Lemma F_960e4 : fetch_word USEGS (0x960e4 : word) = Some W_960e4.
Proof. vm_refl. Qed.
Lemma D_960e4 : decode_any W_960e4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960e8 : bv 32 := 0x01013403.
Lemma F_960e8 : fetch_word USEGS (0x960e8 : word) = Some W_960e8.
Proof. vm_refl. Qed.
Lemma D_960e8 : decode_any W_960e8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960ec : bv 32 := 0x00813483.
Lemma F_960ec : fetch_word USEGS (0x960ec : word) = Some W_960ec.
Proof. vm_refl. Qed.
Lemma D_960ec : decode_any W_960ec = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960f0 : bv 32 := 0x00013903.
Lemma F_960f0 : fetch_word USEGS (0x960f0 : word) = Some W_960f0.
Proof. vm_refl. Qed.
Lemma D_960f0 : decode_any W_960f0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960f4 : bv 32 := 0x02010113.
Lemma F_960f4 : fetch_word USEGS (0x960f4 : word) = Some W_960f4.
Proof. vm_refl. Qed.
Lemma D_960f4 : decode_any W_960f4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960f8 : bv 32 := 0x00030067.
Lemma F_960f8 : fetch_word USEGS (0x960f8 : word) = Some W_960f8.
Proof. vm_refl. Qed.
Lemma D_960f8 : decode_any W_960f8 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.
