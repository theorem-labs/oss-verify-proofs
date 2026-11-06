(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_98e44 : bv 32 := 0x00008067.
Lemma F_98e44 : fetch_word Plain.M.loaded_segments (0x98e9c : word) = Some W_98e44.
Proof. vm_refl. Qed.
Lemma D_98e44 : decode_any W_98e44 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e48 : bv 32 := 0xe8010113.
Lemma F_98e48 : fetch_word Plain.M.loaded_segments (0x98ea0 : word) = Some W_98e48.
Proof. vm_refl. Qed.
Lemma D_98e48 : decode_any W_98e48 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e4c : bv 32 := 0x16113c23.
Lemma F_98e4c : fetch_word Plain.M.loaded_segments (0x98ea4 : word) = Some W_98e4c.
Proof. vm_refl. Qed.
Lemma D_98e4c : decode_any W_98e4c = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e50 : bv 32 := 0x16813823.
Lemma F_98e50 : fetch_word Plain.M.loaded_segments (0x98ea8 : word) = Some W_98e50.
Proof. vm_refl. Qed.
Lemma D_98e50 : decode_any W_98e50 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e54 : bv 32 := 0x16913423.
Lemma F_98e54 : fetch_word Plain.M.loaded_segments (0x98eac : word) = Some W_98e54.
Proof. vm_refl. Qed.
Lemma D_98e54 : decode_any W_98e54 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e58 : bv 32 := 0x17213023.
Lemma F_98e58 : fetch_word Plain.M.loaded_segments (0x98eb0 : word) = Some W_98e58.
Proof. vm_refl. Qed.
Lemma D_98e58 : decode_any W_98e58 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e5c : bv 32 := 0x00058413.
Lemma F_98e5c : fetch_word Plain.M.loaded_segments (0x98eb4 : word) = Some W_98e5c.
Proof. vm_refl. Qed.
Lemma D_98e5c : decode_any W_98e5c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e60 : bv 32 := 0x00050493.
Lemma F_98e60 : fetch_word Plain.M.loaded_segments (0x98eb8 : word) = Some W_98e60.
Proof. vm_refl. Qed.
Lemma D_98e60 : decode_any W_98e60 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e64 : bv 32 := 0x03010513.
Lemma F_98e64 : fetch_word Plain.M.loaded_segments (0x98ebc : word) = Some W_98e64.
Proof. vm_refl. Qed.
Lemma D_98e64 : decode_any W_98e64 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e68 : bv 32 := 0x13000613.
Lemma F_98e68 : fetch_word Plain.M.loaded_segments (0x98ec0 : word) = Some W_98e68.
Proof. vm_refl. Qed.
Lemma D_98e68 : decode_any W_98e68 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e6c : bv 32 := 0x00000593.
Lemma F_98e6c : fetch_word Plain.M.loaded_segments (0x98ec4 : word) = Some W_98e6c.
Proof. vm_refl. Qed.
Lemma D_98e6c : decode_any W_98e6c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e70 : bv 32 := 0x550110ef.
Lemma F_98e70 : fetch_word Plain.M.loaded_segments (0x98ec8 : word) = Some W_98e70.
Proof. vm_refl. Qed.
Lemma D_98e70 : decode_any W_98e70 = Some (Jal 1 70992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e74 : bv 32 := 0x0001d517.
Lemma F_98e74 : fetch_word Plain.M.loaded_segments (0x98ecc : word) = Some W_98e74.
Proof. vm_refl. Qed.
Lemma D_98e74 : decode_any W_98e74 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e78 : bv 32 := 0xd0c53503.
Lemma F_98e78 : fetch_word Plain.M.loaded_segments (0x98ed0 : word) = Some W_98e78.
Proof. vm_refl. Qed.
Lemma D_98e78 : decode_any W_98e78 = Some (Load SZ8 true 10 10 3340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e7c : bv 32 := 0x00953023.
Lemma F_98e7c : fetch_word Plain.M.loaded_segments (0x98ed4 : word) = Some W_98e7c.
Proof. vm_refl. Qed.
Lemma D_98e7c : decode_any W_98e7c = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e80 : bv 32 := 0x0004b503.
Lemma F_98e80 : fetch_word Plain.M.loaded_segments (0x98ed8 : word) = Some W_98e80.
Proof. vm_refl. Qed.
Lemma D_98e80 : decode_any W_98e80 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e84 : bv 32 := 0x00848493.
Lemma F_98e84 : fetch_word Plain.M.loaded_segments (0x98edc : word) = Some W_98e84.
Proof. vm_refl. Qed.
Lemma D_98e84 : decode_any W_98e84 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e88 : bv 32 := 0xfe051ce3.
Lemma F_98e88 : fetch_word Plain.M.loaded_segments (0x98ee0 : word) = Some W_98e88.
Proof. vm_refl. Qed.
Lemma D_98e88 : decode_any W_98e88 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e8c : bv 32 := 0x00050517.
Lemma F_98e8c : fetch_word Plain.M.loaded_segments (0x98ee4 : word) = Some W_98e8c.
Proof. vm_refl. Qed.
Lemma D_98e8c : decode_any W_98e8c = Some (Auipc 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e90 : bv 32 := 0xd8c50913.
Lemma F_98e90 : fetch_word Plain.M.loaded_segments (0x98ee8 : word) = Some W_98e90.
Proof. vm_refl. Qed.
Lemma D_98e90 : decode_any W_98e90 = Some (OpImm ALU_ADD 18 10 3468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e94 : bv 32 := 0x00993423.
Lemma F_98e94 : fetch_word Plain.M.loaded_segments (0x98eec : word) = Some W_98e94.
Proof. vm_refl. Qed.
Lemma D_98e94 : decode_any W_98e94 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e98 : bv 32 := 0x0004b583.
Lemma F_98e98 : fetch_word Plain.M.loaded_segments (0x98ef0 : word) = Some W_98e98.
Proof. vm_refl. Qed.
Lemma D_98e98 : decode_any W_98e98 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e9c : bv 32 := 0x04058c63.
Lemma F_98e9c : fetch_word Plain.M.loaded_segments (0x98ef4 : word) = Some W_98e9c.
Proof. vm_refl. Qed.
Lemma D_98e9c : decode_any W_98e9c = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ea0 : bv 32 := 0x01048493.
Lemma F_98ea0 : fetch_word Plain.M.loaded_segments (0x98ef8 : word) = Some W_98ea0.
Proof. vm_refl. Qed.
Lemma D_98ea0 : decode_any W_98ea0 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ea4 : bv 32 := 0x02500513.
Lemma F_98ea4 : fetch_word Plain.M.loaded_segments (0x98efc : word) = Some W_98ea4.
Proof. vm_refl. Qed.
Lemma D_98ea4 : decode_any W_98ea4 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ea8 : bv 32 := 0x03010613.
Lemma F_98ea8 : fetch_word Plain.M.loaded_segments (0x98f00 : word) = Some W_98ea8.
Proof. vm_refl. Qed.
Lemma D_98ea8 : decode_any W_98ea8 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98eac : bv 32 := 0x0100006f.
Lemma F_98eac : fetch_word Plain.M.loaded_segments (0x98f04 : word) = Some W_98eac.
Proof. vm_refl. Qed.
Lemma D_98eac : decode_any W_98eac = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98eb0 : bv 32 := 0x0004b583.
Lemma F_98eb0 : fetch_word Plain.M.loaded_segments (0x98f08 : word) = Some W_98eb0.
Proof. vm_refl. Qed.
Lemma D_98eb0 : decode_any W_98eb0 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98eb4 : bv 32 := 0x01048493.
Lemma F_98eb4 : fetch_word Plain.M.loaded_segments (0x98f0c : word) = Some W_98eb4.
Proof. vm_refl. Qed.
Lemma D_98eb4 : decode_any W_98eb4 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98eb8 : bv 32 := 0x00058e63.
Lemma F_98eb8 : fetch_word Plain.M.loaded_segments (0x98f10 : word) = Some W_98eb8.
Proof. vm_refl. Qed.
Lemma D_98eb8 : decode_any W_98eb8 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ebc : bv 32 := 0xfeb56ae3.
Lemma F_98ebc : fetch_word Plain.M.loaded_segments (0x98f14 : word) = Some W_98ebc.
Proof. vm_refl. Qed.
Lemma D_98ebc : decode_any W_98ebc = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ec0 : bv 32 := 0xff84b683.
Lemma F_98ec0 : fetch_word Plain.M.loaded_segments (0x98f18 : word) = Some W_98ec0.
Proof. vm_refl. Qed.
Lemma D_98ec0 : decode_any W_98ec0 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ec4 : bv 32 := 0x00359593.
Lemma F_98ec4 : fetch_word Plain.M.loaded_segments (0x98f1c : word) = Some W_98ec4.
Proof. vm_refl. Qed.
Lemma D_98ec4 : decode_any W_98ec4 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ec8 : bv 32 := 0x00b605b3.
Lemma F_98ec8 : fetch_word Plain.M.loaded_segments (0x98f20 : word) = Some W_98ec8.
Proof. vm_refl. Qed.
Lemma D_98ec8 : decode_any W_98ec8 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ecc : bv 32 := 0x00d5b023.
Lemma F_98ecc : fetch_word Plain.M.loaded_segments (0x98f24 : word) = Some W_98ecc.
Proof. vm_refl. Qed.
Lemma D_98ecc : decode_any W_98ecc = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ed0 : bv 32 := 0xfe1ff06f.
Lemma F_98ed0 : fetch_word Plain.M.loaded_segments (0x98f28 : word) = Some W_98ed0.
Proof. vm_refl. Qed.
Lemma D_98ed0 : decode_any W_98ed0 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ed4 : bv 32 := 0x0b013583.
Lemma F_98ed4 : fetch_word Plain.M.loaded_segments (0x98f2c : word) = Some W_98ed4.
Proof. vm_refl. Qed.
Lemma D_98ed4 : decode_any W_98ed4 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ed8 : bv 32 := 0x13013503.
Lemma F_98ed8 : fetch_word Plain.M.loaded_segments (0x98f30 : word) = Some W_98ed8.
Proof. vm_refl. Qed.
Lemma D_98ed8 : decode_any W_98ed8 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98edc : bv 32 := 0x00050617.
Lemma F_98edc : fetch_word Plain.M.loaded_segments (0x98f34 : word) = Some W_98edc.
Proof. vm_refl. Qed.
Lemma D_98edc : decode_any W_98edc = Some (Auipc 12 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ee0 : bv 32 := 0xdab63223.
Lemma F_98ee0 : fetch_word Plain.M.loaded_segments (0x98f38 : word) = Some W_98ee0.
Proof. vm_refl. Qed.
Lemma D_98ee0 : decode_any W_98ee0 = Some (Store SZ8 12 11 3492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ee4 : bv 32 := 0x00050c63.
Lemma F_98ee4 : fetch_word Plain.M.loaded_segments (0x98f3c : word) = Some W_98ee4.
Proof. vm_refl. Qed.
Lemma D_98ee4 : decode_any W_98ee4 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98efc : bv 32 := 0x06013503.
Lemma F_98efc : fetch_word Plain.M.loaded_segments (0x98f54 : word) = Some W_98efc.
Proof. vm_refl. Qed.
Lemma D_98efc : decode_any W_98efc = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f00 : bv 32 := 0x02a93823.
Lemma F_98f00 : fetch_word Plain.M.loaded_segments (0x98f58 : word) = Some W_98f00.
Proof. vm_refl. Qed.
Lemma D_98f00 : decode_any W_98f00 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f04 : bv 32 := 0x00041463.
Lemma F_98f04 : fetch_word Plain.M.loaded_segments (0x98f5c : word) = Some W_98f04.
Proof. vm_refl. Qed.
Lemma D_98f04 : decode_any W_98f04 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f0c : bv 32 := 0x00041663.
Lemma F_98f0c : fetch_word Plain.M.loaded_segments (0x98f64 : word) = Some W_98f0c.
Proof. vm_refl. Qed.
Lemma D_98f0c : decode_any W_98f0c = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f18 : bv 32 := 0x0001d517.
Lemma F_98f18 : fetch_word Plain.M.loaded_segments (0x98f70 : word) = Some W_98f18.
Proof. vm_refl. Qed.
Lemma D_98f18 : decode_any W_98f18 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f1c : bv 32 := 0xc7053583.
Lemma F_98f1c : fetch_word Plain.M.loaded_segments (0x98f74 : word) = Some W_98f1c.
Proof. vm_refl. Qed.
Lemma D_98f1c : decode_any W_98f1c = Some (Load SZ8 true 11 10 3184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f20 : bv 32 := 0x0001d517.
Lemma F_98f20 : fetch_word Plain.M.loaded_segments (0x98f78 : word) = Some W_98f20.
Proof. vm_refl. Qed.
Lemma D_98f20 : decode_any W_98f20 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f24 : bv 32 := 0xc7053503.
Lemma F_98f24 : fetch_word Plain.M.loaded_segments (0x98f7c : word) = Some W_98f24.
Proof. vm_refl. Qed.
Lemma D_98f24 : decode_any W_98f24 = Some (Load SZ8 true 10 10 3184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f28 : bv 32 := 0x0085b023.
Lemma F_98f28 : fetch_word Plain.M.loaded_segments (0x98f80 : word) = Some W_98f28.
Proof. vm_refl. Qed.
Lemma D_98f28 : decode_any W_98f28 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f2c : bv 32 := 0x00140593.
Lemma F_98f2c : fetch_word Plain.M.loaded_segments (0x98f84 : word) = Some W_98f2c.
Proof. vm_refl. Qed.
Lemma D_98f2c : decode_any W_98f2c = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f30 : bv 32 := 0x00853023.
Lemma F_98f30 : fetch_word Plain.M.loaded_segments (0x98f88 : word) = Some W_98f30.
Proof. vm_refl. Qed.
Lemma D_98f30 : decode_any W_98f30 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f34 : bv 32 := 0x02f00613.
Lemma F_98f34 : fetch_word Plain.M.loaded_segments (0x98f8c : word) = Some W_98f34.
Proof. vm_refl. Qed.
Lemma D_98f34 : decode_any W_98f34 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f38 : bv 32 := 0x00c0006f.
Lemma F_98f38 : fetch_word Plain.M.loaded_segments (0x98f90 : word) = Some W_98f38.
Proof. vm_refl. Qed.
Lemma D_98f38 : decode_any W_98f38 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f3c : bv 32 := 0x00b53023.
Lemma F_98f3c : fetch_word Plain.M.loaded_segments (0x98f94 : word) = Some W_98f3c.
Proof. vm_refl. Qed.
Lemma D_98f3c : decode_any W_98f3c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f40 : bv 32 := 0x00158593.
Lemma F_98f40 : fetch_word Plain.M.loaded_segments (0x98f98 : word) = Some W_98f40.
Proof. vm_refl. Qed.
Lemma D_98f40 : decode_any W_98f40 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f44 : bv 32 := 0xfff5c683.
Lemma F_98f44 : fetch_word Plain.M.loaded_segments (0x98f9c : word) = Some W_98f44.
Proof. vm_refl. Qed.
Lemma D_98f44 : decode_any W_98f44 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f48 : bv 32 := 0xfec68ae3.
Lemma F_98f48 : fetch_word Plain.M.loaded_segments (0x98fa0 : word) = Some W_98f48.
Proof. vm_refl. Qed.
Lemma D_98f48 : decode_any W_98f48 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f4c : bv 32 := 0xfe069ae3.
Lemma F_98f4c : fetch_word Plain.M.loaded_segments (0x98fa4 : word) = Some W_98f4c.
Proof. vm_refl. Qed.
Lemma D_98f4c : decode_any W_98f4c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f50 : bv 32 := 0x03010513.
Lemma F_98f50 : fetch_word Plain.M.loaded_segments (0x98fa8 : word) = Some W_98f50.
Proof. vm_refl. Qed.
Lemma D_98f50 : decode_any W_98f50 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f54 : bv 32 := 0x214000ef.
Lemma F_98f54 : fetch_word Plain.M.loaded_segments (0x98fac : word) = Some W_98f54.
Proof. vm_refl. Qed.
Lemma D_98f54 : decode_any W_98f54 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f58 : bv 32 := 0x0f813503.
Lemma F_98f58 : fetch_word Plain.M.loaded_segments (0x98fb0 : word) = Some W_98f58.
Proof. vm_refl. Qed.
Lemma D_98f58 : decode_any W_98f58 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f5c : bv 32 := 0x1ad000ef.
Lemma F_98f5c : fetch_word Plain.M.loaded_segments (0x98fb4 : word) = Some W_98f5c.
Proof. vm_refl. Qed.
Lemma D_98f5c : decode_any W_98f5c = Some (Jal 1 2476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f60 : bv 32 := 0x08813503.
Lemma F_98f60 : fetch_word Plain.M.loaded_segments (0x98fb8 : word) = Some W_98f60.
Proof. vm_refl. Qed.
Lemma D_98f60 : decode_any W_98f60 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f64 : bv 32 := 0x09013583.
Lemma F_98f64 : fetch_word Plain.M.loaded_segments (0x98fbc : word) = Some W_98f64.
Proof. vm_refl. Qed.
Lemma D_98f64 : decode_any W_98f64 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f68 : bv 32 := 0x00b51c63.
Lemma F_98f68 : fetch_word Plain.M.loaded_segments (0x98fc0 : word) = Some W_98f68.
Proof. vm_refl. Qed.
Lemma D_98f68 : decode_any W_98f68 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f6c : bv 32 := 0x09813503.
Lemma F_98f6c : fetch_word Plain.M.loaded_segments (0x98fc4 : word) = Some W_98f6c.
Proof. vm_refl. Qed.
Lemma D_98f6c : decode_any W_98f6c = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f70 : bv 32 := 0x0a013583.
Lemma F_98f70 : fetch_word Plain.M.loaded_segments (0x98fc8 : word) = Some W_98f70.
Proof. vm_refl. Qed.
Lemma D_98f70 : decode_any W_98f70 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f74 : bv 32 := 0x00b51663.
Lemma F_98f74 : fetch_word Plain.M.loaded_segments (0x98fcc : word) = Some W_98f74.
Proof. vm_refl. Qed.
Lemma D_98f74 : decode_any W_98f74 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f78 : bv 32 := 0x0e813503.
Lemma F_98f78 : fetch_word Plain.M.loaded_segments (0x98fd0 : word) = Some W_98f78.
Proof. vm_refl. Qed.
Lemma D_98f78 : decode_any W_98f78 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f7c : bv 32 := 0x0e050063.
Lemma F_98f7c : fetch_word Plain.M.loaded_segments (0x98fd4 : word) = Some W_98f7c.
Proof. vm_refl. Qed.
Lemma D_98f7c : decode_any W_98f7c = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9905c : bv 32 := 0x17813083.
Lemma F_9905c : fetch_word Plain.M.loaded_segments (0x990b4 : word) = Some W_9905c.
Proof. vm_refl. Qed.
Lemma D_9905c : decode_any W_9905c = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99060 : bv 32 := 0x17013403.
Lemma F_99060 : fetch_word Plain.M.loaded_segments (0x990b8 : word) = Some W_99060.
Proof. vm_refl. Qed.
Lemma D_99060 : decode_any W_99060 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99064 : bv 32 := 0x16813483.
Lemma F_99064 : fetch_word Plain.M.loaded_segments (0x990bc : word) = Some W_99064.
Proof. vm_refl. Qed.
Lemma D_99064 : decode_any W_99064 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99068 : bv 32 := 0x16013903.
Lemma F_99068 : fetch_word Plain.M.loaded_segments (0x990c0 : word) = Some W_99068.
Proof. vm_refl. Qed.
Lemma D_99068 : decode_any W_99068 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9906c : bv 32 := 0x18010113.
Lemma F_9906c : fetch_word Plain.M.loaded_segments (0x990c4 : word) = Some W_9906c.
Proof. vm_refl. Qed.
Lemma D_9906c : decode_any W_9906c = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99070 : bv 32 := 0x00008067.
Lemma F_99070 : fetch_word Plain.M.loaded_segments (0x990c8 : word) = Some W_99070.
Proof. vm_refl. Qed.
Lemma D_99070 : decode_any W_99070 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99074 : bv 32 := 0xfe010113.
Lemma F_99074 : fetch_word Plain.M.loaded_segments (0x990cc : word) = Some W_99074.
Proof. vm_refl. Qed.
Lemma D_99074 : decode_any W_99074 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99078 : bv 32 := 0x00113c23.
Lemma F_99078 : fetch_word Plain.M.loaded_segments (0x990d0 : word) = Some W_99078.
Proof. vm_refl. Qed.
Lemma D_99078 : decode_any W_99078 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9907c : bv 32 := 0x00813823.
Lemma F_9907c : fetch_word Plain.M.loaded_segments (0x990d4 : word) = Some W_9907c.
Proof. vm_refl. Qed.
Lemma D_9907c : decode_any W_9907c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99080 : bv 32 := 0x00913423.
Lemma F_99080 : fetch_word Plain.M.loaded_segments (0x990d8 : word) = Some W_99080.
Proof. vm_refl. Qed.
Lemma D_99080 : decode_any W_99080 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99084 : bv 32 := 0xdc1ff0ef.
Lemma F_99084 : fetch_word Plain.M.loaded_segments (0x990dc : word) = Some W_99084.
Proof. vm_refl. Qed.
Lemma D_99084 : decode_any W_99084 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99088 : bv 32 := 0x0001d517.
Lemma F_99088 : fetch_word Plain.M.loaded_segments (0x990e0 : word) = Some W_99088.
Proof. vm_refl. Qed.
Lemma D_99088 : decode_any W_99088 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9908c : bv 32 := 0x0001d597.
Lemma F_9908c : fetch_word Plain.M.loaded_segments (0x990e4 : word) = Some W_9908c.
Proof. vm_refl. Qed.
Lemma D_9908c : decode_any W_9908c = Some (Auipc 11 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99090 : bv 32 := 0xb1053403.
Lemma F_99090 : fetch_word Plain.M.loaded_segments (0x990e8 : word) = Some W_99090.
Proof. vm_refl. Qed.
Lemma D_99090 : decode_any W_99090 = Some (Load SZ8 true 8 10 2832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99094 : bv 32 := 0xb145b483.
Lemma F_99094 : fetch_word Plain.M.loaded_segments (0x990ec : word) = Some W_99094.
Proof. vm_refl. Qed.
Lemma D_99094 : decode_any W_99094 = Some (Load SZ8 true 9 11 2836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99098 : bv 32 := 0x0084fa63.
Lemma F_99098 : fetch_word Plain.M.loaded_segments (0x990f0 : word) = Some W_99098.
Proof. vm_refl. Qed.
Lemma D_99098 : decode_any W_99098 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9909c : bv 32 := 0x0004b503.
Lemma F_9909c : fetch_word Plain.M.loaded_segments (0x990f4 : word) = Some W_9909c.
Proof. vm_refl. Qed.
Lemma D_9909c : decode_any W_9909c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990a0 : bv 32 := 0x000500e7.
Lemma F_990a0 : fetch_word Plain.M.loaded_segments (0x990f8 : word) = Some W_990a0.
Proof. vm_refl. Qed.
Lemma D_990a0 : decode_any W_990a0 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990a4 : bv 32 := 0x00848493.
Lemma F_990a4 : fetch_word Plain.M.loaded_segments (0x990fc : word) = Some W_990a4.
Proof. vm_refl. Qed.
Lemma D_990a4 : decode_any W_990a4 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990a8 : bv 32 := 0xfe84eae3.
Lemma F_990a8 : fetch_word Plain.M.loaded_segments (0x99100 : word) = Some W_990a8.
Proof. vm_refl. Qed.
Lemma D_990a8 : decode_any W_990a8 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990ac : bv 32 := 0x01813083.
Lemma F_990ac : fetch_word Plain.M.loaded_segments (0x99104 : word) = Some W_990ac.
Proof. vm_refl. Qed.
Lemma D_990ac : decode_any W_990ac = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990b0 : bv 32 := 0x01013403.
Lemma F_990b0 : fetch_word Plain.M.loaded_segments (0x99108 : word) = Some W_990b0.
Proof. vm_refl. Qed.
Lemma D_990b0 : decode_any W_990b0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990b4 : bv 32 := 0x00813483.
Lemma F_990b4 : fetch_word Plain.M.loaded_segments (0x9910c : word) = Some W_990b4.
Proof. vm_refl. Qed.
Lemma D_990b4 : decode_any W_990b4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990b8 : bv 32 := 0x02010113.
Lemma F_990b8 : fetch_word Plain.M.loaded_segments (0x99110 : word) = Some W_990b8.
Proof. vm_refl. Qed.
Lemma D_990b8 : decode_any W_990b8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990bc : bv 32 := 0x00008067.
Lemma F_990bc : fetch_word Plain.M.loaded_segments (0x99114 : word) = Some W_990bc.
Proof. vm_refl. Qed.
Lemma D_990bc : decode_any W_990bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990c0 : bv 32 := 0xfe010113.
Lemma F_990c0 : fetch_word Plain.M.loaded_segments (0x99118 : word) = Some W_990c0.
Proof. vm_refl. Qed.
Lemma D_990c0 : decode_any W_990c0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990c4 : bv 32 := 0x00113c23.
Lemma F_990c4 : fetch_word Plain.M.loaded_segments (0x9911c : word) = Some W_990c4.
Proof. vm_refl. Qed.
Lemma D_990c4 : decode_any W_990c4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990c8 : bv 32 := 0x00813823.
Lemma F_990c8 : fetch_word Plain.M.loaded_segments (0x99120 : word) = Some W_990c8.
Proof. vm_refl. Qed.
Lemma D_990c8 : decode_any W_990c8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990cc : bv 32 := 0x00913423.
Lemma F_990cc : fetch_word Plain.M.loaded_segments (0x99124 : word) = Some W_990cc.
Proof. vm_refl. Qed.
Lemma D_990cc : decode_any W_990cc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990d0 : bv 32 := 0x01213023.
Lemma F_990d0 : fetch_word Plain.M.loaded_segments (0x99128 : word) = Some W_990d0.
Proof. vm_refl. Qed.
Lemma D_990d0 : decode_any W_990d0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990d4 : bv 32 := 0x00060413.
Lemma F_990d4 : fetch_word Plain.M.loaded_segments (0x9912c : word) = Some W_990d4.
Proof. vm_refl. Qed.
Lemma D_990d4 : decode_any W_990d4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990d8 : bv 32 := 0x00058493.
Lemma F_990d8 : fetch_word Plain.M.loaded_segments (0x99130 : word) = Some W_990d8.
Proof. vm_refl. Qed.
Lemma D_990d8 : decode_any W_990d8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990dc : bv 32 := 0x00050913.
Lemma F_990dc : fetch_word Plain.M.loaded_segments (0x99134 : word) = Some W_990dc.
Proof. vm_refl. Qed.
Lemma D_990dc : decode_any W_990dc = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990e0 : bv 32 := 0x00063583.
Lemma F_990e0 : fetch_word Plain.M.loaded_segments (0x99138 : word) = Some W_990e0.
Proof. vm_refl. Qed.
Lemma D_990e0 : decode_any W_990e0 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990e4 : bv 32 := 0x00349513.
Lemma F_990e4 : fetch_word Plain.M.loaded_segments (0x9913c : word) = Some W_990e4.
Proof. vm_refl. Qed.
Lemma D_990e4 : decode_any W_990e4 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990e8 : bv 32 := 0x00a60533.
Lemma F_990e8 : fetch_word Plain.M.loaded_segments (0x99140 : word) = Some W_990e8.
Proof. vm_refl. Qed.
Lemma D_990e8 : decode_any W_990e8 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990ec : bv 32 := 0x00850513.
Lemma F_990ec : fetch_word Plain.M.loaded_segments (0x99144 : word) = Some W_990ec.
Proof. vm_refl. Qed.
Lemma D_990ec : decode_any W_990ec = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990f0 : bv 32 := 0xd59ff0ef.
Lemma F_990f0 : fetch_word Plain.M.loaded_segments (0x99148 : word) = Some W_990f0.
Proof. vm_refl. Qed.
Lemma D_990f0 : decode_any W_990f0 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990f4 : bv 32 := 0x00000517.
Lemma F_990f4 : fetch_word Plain.M.loaded_segments (0x9914c : word) = Some W_990f4.
Proof. vm_refl. Qed.
Lemma D_990f4 : decode_any W_990f4 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990f8 : bv 32 := 0x02c50313.
Lemma F_990f8 : fetch_word Plain.M.loaded_segments (0x99150 : word) = Some W_990f8.
Proof. vm_refl. Qed.
Lemma D_990f8 : decode_any W_990f8 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990fc : bv 32 := 0x00090513.
Lemma F_990fc : fetch_word Plain.M.loaded_segments (0x99154 : word) = Some W_990fc.
Proof. vm_refl. Qed.
Lemma D_990fc : decode_any W_990fc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99100 : bv 32 := 0x00048593.
Lemma F_99100 : fetch_word Plain.M.loaded_segments (0x99158 : word) = Some W_99100.
Proof. vm_refl. Qed.
Lemma D_99100 : decode_any W_99100 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99104 : bv 32 := 0x00040613.
Lemma F_99104 : fetch_word Plain.M.loaded_segments (0x9915c : word) = Some W_99104.
Proof. vm_refl. Qed.
Lemma D_99104 : decode_any W_99104 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99108 : bv 32 := 0x01813083.
Lemma F_99108 : fetch_word Plain.M.loaded_segments (0x99160 : word) = Some W_99108.
Proof. vm_refl. Qed.
Lemma D_99108 : decode_any W_99108 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9910c : bv 32 := 0x01013403.
Lemma F_9910c : fetch_word Plain.M.loaded_segments (0x99164 : word) = Some W_9910c.
Proof. vm_refl. Qed.
Lemma D_9910c : decode_any W_9910c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99110 : bv 32 := 0x00813483.
Lemma F_99110 : fetch_word Plain.M.loaded_segments (0x99168 : word) = Some W_99110.
Proof. vm_refl. Qed.
Lemma D_99110 : decode_any W_99110 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99114 : bv 32 := 0x00013903.
Lemma F_99114 : fetch_word Plain.M.loaded_segments (0x9916c : word) = Some W_99114.
Proof. vm_refl. Qed.
Lemma D_99114 : decode_any W_99114 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99118 : bv 32 := 0x02010113.
Lemma F_99118 : fetch_word Plain.M.loaded_segments (0x99170 : word) = Some W_99118.
Proof. vm_refl. Qed.
Lemma D_99118 : decode_any W_99118 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9911c : bv 32 := 0x00030067.
Lemma F_9911c : fetch_word Plain.M.loaded_segments (0x99174 : word) = Some W_9911c.
Proof. vm_refl. Qed.
Lemma D_9911c : decode_any W_9911c = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99120 : bv 32 := 0xfd010113.
Lemma F_99120 : fetch_word Plain.M.loaded_segments (0x99178 : word) = Some W_99120.
Proof. vm_refl. Qed.
Lemma D_99120 : decode_any W_99120 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99124 : bv 32 := 0x02113423.
Lemma F_99124 : fetch_word Plain.M.loaded_segments (0x9917c : word) = Some W_99124.
Proof. vm_refl. Qed.
Lemma D_99124 : decode_any W_99124 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99128 : bv 32 := 0x02813023.
Lemma F_99128 : fetch_word Plain.M.loaded_segments (0x99180 : word) = Some W_99128.
Proof. vm_refl. Qed.
Lemma D_99128 : decode_any W_99128 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9912c : bv 32 := 0x00913c23.
Lemma F_9912c : fetch_word Plain.M.loaded_segments (0x99184 : word) = Some W_9912c.
Proof. vm_refl. Qed.
Lemma D_9912c : decode_any W_9912c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99130 : bv 32 := 0x01213823.
Lemma F_99130 : fetch_word Plain.M.loaded_segments (0x99188 : word) = Some W_99130.
Proof. vm_refl. Qed.
Lemma D_99130 : decode_any W_99130 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99134 : bv 32 := 0x01313423.
Lemma F_99134 : fetch_word Plain.M.loaded_segments (0x9918c : word) = Some W_99134.
Proof. vm_refl. Qed.
Lemma D_99134 : decode_any W_99134 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99138 : bv 32 := 0x00060413.
Lemma F_99138 : fetch_word Plain.M.loaded_segments (0x99190 : word) = Some W_99138.
Proof. vm_refl. Qed.
Lemma D_99138 : decode_any W_99138 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9913c : bv 32 := 0x00058493.
Lemma F_9913c : fetch_word Plain.M.loaded_segments (0x99194 : word) = Some W_9913c.
Proof. vm_refl. Qed.
Lemma D_9913c : decode_any W_9913c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99140 : bv 32 := 0x00050913.
Lemma F_99140 : fetch_word Plain.M.loaded_segments (0x99198 : word) = Some W_99140.
Proof. vm_refl. Qed.
Lemma D_99140 : decode_any W_99140 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99144 : bv 32 := 0x00359513.
Lemma F_99144 : fetch_word Plain.M.loaded_segments (0x9919c : word) = Some W_99144.
Proof. vm_refl. Qed.
Lemma D_99144 : decode_any W_99144 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99148 : bv 32 := 0x00a60533.
Lemma F_99148 : fetch_word Plain.M.loaded_segments (0x991a0 : word) = Some W_99148.
Proof. vm_refl. Qed.
Lemma D_99148 : decode_any W_99148 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9914c : bv 32 := 0x00850993.
Lemma F_9914c : fetch_word Plain.M.loaded_segments (0x991a4 : word) = Some W_9914c.
Proof. vm_refl. Qed.
Lemma D_9914c : decode_any W_9914c = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99150 : bv 32 := 0xf25ff0ef.
Lemma F_99150 : fetch_word Plain.M.loaded_segments (0x991a8 : word) = Some W_99150.
Proof. vm_refl. Qed.
Lemma D_99150 : decode_any W_99150 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99154 : bv 32 := 0x00048513.
Lemma F_99154 : fetch_word Plain.M.loaded_segments (0x991ac : word) = Some W_99154.
Proof. vm_refl. Qed.
Lemma D_99154 : decode_any W_99154 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99158 : bv 32 := 0x00040593.
Lemma F_99158 : fetch_word Plain.M.loaded_segments (0x991b0 : word) = Some W_99158.
Proof. vm_refl. Qed.
Lemma D_99158 : decode_any W_99158 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9915c : bv 32 := 0x00098613.
Lemma F_9915c : fetch_word Plain.M.loaded_segments (0x991b4 : word) = Some W_9915c.
Proof. vm_refl. Qed.
Lemma D_9915c : decode_any W_9915c = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99160 : bv 32 := 0x000900e7.
Lemma F_99160 : fetch_word Plain.M.loaded_segments (0x991b8 : word) = Some W_99160.
Proof. vm_refl. Qed.
Lemma D_99160 : decode_any W_99160 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
