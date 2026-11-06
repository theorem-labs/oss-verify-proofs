(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_66e58 : bv 32 := 0x00008067.
Lemma F_66e58 : fetch_word Plain.M.loaded_segments (0x66e58 : word) = Some W_66e58.
Proof. vm_refl. Qed.
Lemma D_66e58 : decode_any W_66e58 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e5c : bv 32 := 0xe8010113.
Lemma F_66e5c : fetch_word Plain.M.loaded_segments (0x66e5c : word) = Some W_66e5c.
Proof. vm_refl. Qed.
Lemma D_66e5c : decode_any W_66e5c = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e60 : bv 32 := 0x16113c23.
Lemma F_66e60 : fetch_word Plain.M.loaded_segments (0x66e60 : word) = Some W_66e60.
Proof. vm_refl. Qed.
Lemma D_66e60 : decode_any W_66e60 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e64 : bv 32 := 0x16813823.
Lemma F_66e64 : fetch_word Plain.M.loaded_segments (0x66e64 : word) = Some W_66e64.
Proof. vm_refl. Qed.
Lemma D_66e64 : decode_any W_66e64 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e68 : bv 32 := 0x16913423.
Lemma F_66e68 : fetch_word Plain.M.loaded_segments (0x66e68 : word) = Some W_66e68.
Proof. vm_refl. Qed.
Lemma D_66e68 : decode_any W_66e68 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e6c : bv 32 := 0x17213023.
Lemma F_66e6c : fetch_word Plain.M.loaded_segments (0x66e6c : word) = Some W_66e6c.
Proof. vm_refl. Qed.
Lemma D_66e6c : decode_any W_66e6c = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e70 : bv 32 := 0x00058413.
Lemma F_66e70 : fetch_word Plain.M.loaded_segments (0x66e70 : word) = Some W_66e70.
Proof. vm_refl. Qed.
Lemma D_66e70 : decode_any W_66e70 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e74 : bv 32 := 0x00050493.
Lemma F_66e74 : fetch_word Plain.M.loaded_segments (0x66e74 : word) = Some W_66e74.
Proof. vm_refl. Qed.
Lemma D_66e74 : decode_any W_66e74 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e78 : bv 32 := 0x03010513.
Lemma F_66e78 : fetch_word Plain.M.loaded_segments (0x66e78 : word) = Some W_66e78.
Proof. vm_refl. Qed.
Lemma D_66e78 : decode_any W_66e78 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e7c : bv 32 := 0x13000613.
Lemma F_66e7c : fetch_word Plain.M.loaded_segments (0x66e7c : word) = Some W_66e7c.
Proof. vm_refl. Qed.
Lemma D_66e7c : decode_any W_66e7c = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e80 : bv 32 := 0x00000593.
Lemma F_66e80 : fetch_word Plain.M.loaded_segments (0x66e80 : word) = Some W_66e80.
Proof. vm_refl. Qed.
Lemma D_66e80 : decode_any W_66e80 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e84 : bv 32 := 0x1210e0ef.
Lemma F_66e84 : fetch_word Plain.M.loaded_segments (0x66e84 : word) = Some W_66e84.
Proof. vm_refl. Qed.
Lemma D_66e84 : decode_any W_66e84 = Some (Jal 1 59680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e88 : bv 32 := 0x00019517.
Lemma F_66e88 : fetch_word Plain.M.loaded_segments (0x66e88 : word) = Some W_66e88.
Proof. vm_refl. Qed.
Lemma D_66e88 : decode_any W_66e88 = Some (Auipc 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e8c : bv 32 := 0x98853503.
Lemma F_66e8c : fetch_word Plain.M.loaded_segments (0x66e8c : word) = Some W_66e8c.
Proof. vm_refl. Qed.
Lemma D_66e8c : decode_any W_66e8c = Some (Load SZ8 true 10 10 2440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e90 : bv 32 := 0x00953023.
Lemma F_66e90 : fetch_word Plain.M.loaded_segments (0x66e90 : word) = Some W_66e90.
Proof. vm_refl. Qed.
Lemma D_66e90 : decode_any W_66e90 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e94 : bv 32 := 0x0004b503.
Lemma F_66e94 : fetch_word Plain.M.loaded_segments (0x66e94 : word) = Some W_66e94.
Proof. vm_refl. Qed.
Lemma D_66e94 : decode_any W_66e94 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e98 : bv 32 := 0x00848493.
Lemma F_66e98 : fetch_word Plain.M.loaded_segments (0x66e98 : word) = Some W_66e98.
Proof. vm_refl. Qed.
Lemma D_66e98 : decode_any W_66e98 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e9c : bv 32 := 0xfe051ce3.
Lemma F_66e9c : fetch_word Plain.M.loaded_segments (0x66e9c : word) = Some W_66e9c.
Proof. vm_refl. Qed.
Lemma D_66e9c : decode_any W_66e9c = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ea0 : bv 32 := 0x0004c517.
Lemma F_66ea0 : fetch_word Plain.M.loaded_segments (0x66ea0 : word) = Some W_66ea0.
Proof. vm_refl. Qed.
Lemma D_66ea0 : decode_any W_66ea0 = Some (Auipc 10 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ea4 : bv 32 := 0xa4050913.
Lemma F_66ea4 : fetch_word Plain.M.loaded_segments (0x66ea4 : word) = Some W_66ea4.
Proof. vm_refl. Qed.
Lemma D_66ea4 : decode_any W_66ea4 = Some (OpImm ALU_ADD 18 10 2624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ea8 : bv 32 := 0x00993423.
Lemma F_66ea8 : fetch_word Plain.M.loaded_segments (0x66ea8 : word) = Some W_66ea8.
Proof. vm_refl. Qed.
Lemma D_66ea8 : decode_any W_66ea8 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66eac : bv 32 := 0x0004b583.
Lemma F_66eac : fetch_word Plain.M.loaded_segments (0x66eac : word) = Some W_66eac.
Proof. vm_refl. Qed.
Lemma D_66eac : decode_any W_66eac = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66eb0 : bv 32 := 0x04058c63.
Lemma F_66eb0 : fetch_word Plain.M.loaded_segments (0x66eb0 : word) = Some W_66eb0.
Proof. vm_refl. Qed.
Lemma D_66eb0 : decode_any W_66eb0 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66eb4 : bv 32 := 0x01048493.
Lemma F_66eb4 : fetch_word Plain.M.loaded_segments (0x66eb4 : word) = Some W_66eb4.
Proof. vm_refl. Qed.
Lemma D_66eb4 : decode_any W_66eb4 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66eb8 : bv 32 := 0x02500513.
Lemma F_66eb8 : fetch_word Plain.M.loaded_segments (0x66eb8 : word) = Some W_66eb8.
Proof. vm_refl. Qed.
Lemma D_66eb8 : decode_any W_66eb8 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ebc : bv 32 := 0x03010613.
Lemma F_66ebc : fetch_word Plain.M.loaded_segments (0x66ebc : word) = Some W_66ebc.
Proof. vm_refl. Qed.
Lemma D_66ebc : decode_any W_66ebc = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ec0 : bv 32 := 0x0100006f.
Lemma F_66ec0 : fetch_word Plain.M.loaded_segments (0x66ec0 : word) = Some W_66ec0.
Proof. vm_refl. Qed.
Lemma D_66ec0 : decode_any W_66ec0 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ec4 : bv 32 := 0x0004b583.
Lemma F_66ec4 : fetch_word Plain.M.loaded_segments (0x66ec4 : word) = Some W_66ec4.
Proof. vm_refl. Qed.
Lemma D_66ec4 : decode_any W_66ec4 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ec8 : bv 32 := 0x01048493.
Lemma F_66ec8 : fetch_word Plain.M.loaded_segments (0x66ec8 : word) = Some W_66ec8.
Proof. vm_refl. Qed.
Lemma D_66ec8 : decode_any W_66ec8 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ecc : bv 32 := 0x00058e63.
Lemma F_66ecc : fetch_word Plain.M.loaded_segments (0x66ecc : word) = Some W_66ecc.
Proof. vm_refl. Qed.
Lemma D_66ecc : decode_any W_66ecc = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ed0 : bv 32 := 0xfeb56ae3.
Lemma F_66ed0 : fetch_word Plain.M.loaded_segments (0x66ed0 : word) = Some W_66ed0.
Proof. vm_refl. Qed.
Lemma D_66ed0 : decode_any W_66ed0 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ed4 : bv 32 := 0xff84b683.
Lemma F_66ed4 : fetch_word Plain.M.loaded_segments (0x66ed4 : word) = Some W_66ed4.
Proof. vm_refl. Qed.
Lemma D_66ed4 : decode_any W_66ed4 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ed8 : bv 32 := 0x00359593.
Lemma F_66ed8 : fetch_word Plain.M.loaded_segments (0x66ed8 : word) = Some W_66ed8.
Proof. vm_refl. Qed.
Lemma D_66ed8 : decode_any W_66ed8 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66edc : bv 32 := 0x00b605b3.
Lemma F_66edc : fetch_word Plain.M.loaded_segments (0x66edc : word) = Some W_66edc.
Proof. vm_refl. Qed.
Lemma D_66edc : decode_any W_66edc = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ee0 : bv 32 := 0x00d5b023.
Lemma F_66ee0 : fetch_word Plain.M.loaded_segments (0x66ee0 : word) = Some W_66ee0.
Proof. vm_refl. Qed.
Lemma D_66ee0 : decode_any W_66ee0 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ee4 : bv 32 := 0xfe1ff06f.
Lemma F_66ee4 : fetch_word Plain.M.loaded_segments (0x66ee4 : word) = Some W_66ee4.
Proof. vm_refl. Qed.
Lemma D_66ee4 : decode_any W_66ee4 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ee8 : bv 32 := 0x0b013583.
Lemma F_66ee8 : fetch_word Plain.M.loaded_segments (0x66ee8 : word) = Some W_66ee8.
Proof. vm_refl. Qed.
Lemma D_66ee8 : decode_any W_66ee8 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66eec : bv 32 := 0x13013503.
Lemma F_66eec : fetch_word Plain.M.loaded_segments (0x66eec : word) = Some W_66eec.
Proof. vm_refl. Qed.
Lemma D_66eec : decode_any W_66eec = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ef0 : bv 32 := 0x0004c617.
Lemma F_66ef0 : fetch_word Plain.M.loaded_segments (0x66ef0 : word) = Some W_66ef0.
Proof. vm_refl. Qed.
Lemma D_66ef0 : decode_any W_66ef0 = Some (Auipc 12 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ef4 : bv 32 := 0xa4b63c23.
Lemma F_66ef4 : fetch_word Plain.M.loaded_segments (0x66ef4 : word) = Some W_66ef4.
Proof. vm_refl. Qed.
Lemma D_66ef4 : decode_any W_66ef4 = Some (Store SZ8 12 11 2648, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ef8 : bv 32 := 0x00050c63.
Lemma F_66ef8 : fetch_word Plain.M.loaded_segments (0x66ef8 : word) = Some W_66ef8.
Proof. vm_refl. Qed.
Lemma D_66ef8 : decode_any W_66ef8 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66efc : bv 32 := 0x0004c597.
Lemma F_66efc : fetch_word Plain.M.loaded_segments (0x66efc : word) = Some W_66efc.
Proof. vm_refl. Qed.
Lemma D_66efc : decode_any W_66efc = Some (Auipc 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f00 : bv 32 := 0x9ca5b623.
Lemma F_66f00 : fetch_word Plain.M.loaded_segments (0x66f00 : word) = Some W_66f00.
Proof. vm_refl. Qed.
Lemma D_66f00 : decode_any W_66f00 = Some (Store SZ8 11 10 2508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f04 : bv 32 := 0x00c0006f.
Lemma F_66f04 : fetch_word Plain.M.loaded_segments (0x66f04 : word) = Some W_66f04.
Proof. vm_refl. Qed.
Lemma D_66f04 : decode_any W_66f04 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f08 : bv 32 := 0x0004c517.
Lemma F_66f08 : fetch_word Plain.M.loaded_segments (0x66f08 : word) = Some W_66f08.
Proof. vm_refl. Qed.
Lemma D_66f08 : decode_any W_66f08 = Some (Auipc 10 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f0c : bv 32 := 0xa4053023.
Lemma F_66f0c : fetch_word Plain.M.loaded_segments (0x66f0c : word) = Some W_66f0c.
Proof. vm_refl. Qed.
Lemma D_66f0c : decode_any W_66f0c = Some (Store SZ8 10 0 2624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f10 : bv 32 := 0x06013503.
Lemma F_66f10 : fetch_word Plain.M.loaded_segments (0x66f10 : word) = Some W_66f10.
Proof. vm_refl. Qed.
Lemma D_66f10 : decode_any W_66f10 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f14 : bv 32 := 0x02a93823.
Lemma F_66f14 : fetch_word Plain.M.loaded_segments (0x66f14 : word) = Some W_66f14.
Proof. vm_refl. Qed.
Lemma D_66f14 : decode_any W_66f14 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f18 : bv 32 := 0x00041463.
Lemma F_66f18 : fetch_word Plain.M.loaded_segments (0x66f18 : word) = Some W_66f18.
Proof. vm_refl. Qed.
Lemma D_66f18 : decode_any W_66f18 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f1c : bv 32 := 0x12813403.
Lemma F_66f1c : fetch_word Plain.M.loaded_segments (0x66f1c : word) = Some W_66f1c.
Proof. vm_refl. Qed.
Lemma D_66f1c : decode_any W_66f1c = Some (Load SZ8 true 8 2 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f20 : bv 32 := 0x00041663.
Lemma F_66f20 : fetch_word Plain.M.loaded_segments (0x66f20 : word) = Some W_66f20.
Proof. vm_refl. Qed.
Lemma D_66f20 : decode_any W_66f20 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f24 : bv 32 := 0xfffaa517.
Lemma F_66f24 : fetch_word Plain.M.loaded_segments (0x66f24 : word) = Some W_66f24.
Proof. vm_refl. Qed.
Lemma D_66f24 : decode_any W_66f24 = Some (Auipc 10 1048490, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f28 : bv 32 := 0x54c50413.
Lemma F_66f28 : fetch_word Plain.M.loaded_segments (0x66f28 : word) = Some W_66f28.
Proof. vm_refl. Qed.
Lemma D_66f28 : decode_any W_66f28 = Some (OpImm ALU_ADD 8 10 1356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f2c : bv 32 := 0x00019517.
Lemma F_66f2c : fetch_word Plain.M.loaded_segments (0x66f2c : word) = Some W_66f2c.
Proof. vm_refl. Qed.
Lemma D_66f2c : decode_any W_66f2c = Some (Auipc 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f30 : bv 32 := 0x8ec53583.
Lemma F_66f30 : fetch_word Plain.M.loaded_segments (0x66f30 : word) = Some W_66f30.
Proof. vm_refl. Qed.
Lemma D_66f30 : decode_any W_66f30 = Some (Load SZ8 true 11 10 2284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f34 : bv 32 := 0x00019517.
Lemma F_66f34 : fetch_word Plain.M.loaded_segments (0x66f34 : word) = Some W_66f34.
Proof. vm_refl. Qed.
Lemma D_66f34 : decode_any W_66f34 = Some (Auipc 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f38 : bv 32 := 0x8ec53503.
Lemma F_66f38 : fetch_word Plain.M.loaded_segments (0x66f38 : word) = Some W_66f38.
Proof. vm_refl. Qed.
Lemma D_66f38 : decode_any W_66f38 = Some (Load SZ8 true 10 10 2284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f3c : bv 32 := 0x0085b023.
Lemma F_66f3c : fetch_word Plain.M.loaded_segments (0x66f3c : word) = Some W_66f3c.
Proof. vm_refl. Qed.
Lemma D_66f3c : decode_any W_66f3c = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f40 : bv 32 := 0x00140593.
Lemma F_66f40 : fetch_word Plain.M.loaded_segments (0x66f40 : word) = Some W_66f40.
Proof. vm_refl. Qed.
Lemma D_66f40 : decode_any W_66f40 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f44 : bv 32 := 0x00853023.
Lemma F_66f44 : fetch_word Plain.M.loaded_segments (0x66f44 : word) = Some W_66f44.
Proof. vm_refl. Qed.
Lemma D_66f44 : decode_any W_66f44 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f48 : bv 32 := 0x02f00613.
Lemma F_66f48 : fetch_word Plain.M.loaded_segments (0x66f48 : word) = Some W_66f48.
Proof. vm_refl. Qed.
Lemma D_66f48 : decode_any W_66f48 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f4c : bv 32 := 0x00c0006f.
Lemma F_66f4c : fetch_word Plain.M.loaded_segments (0x66f4c : word) = Some W_66f4c.
Proof. vm_refl. Qed.
Lemma D_66f4c : decode_any W_66f4c = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f50 : bv 32 := 0x00b53023.
Lemma F_66f50 : fetch_word Plain.M.loaded_segments (0x66f50 : word) = Some W_66f50.
Proof. vm_refl. Qed.
Lemma D_66f50 : decode_any W_66f50 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f54 : bv 32 := 0x00158593.
Lemma F_66f54 : fetch_word Plain.M.loaded_segments (0x66f54 : word) = Some W_66f54.
Proof. vm_refl. Qed.
Lemma D_66f54 : decode_any W_66f54 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f58 : bv 32 := 0xfff5c683.
Lemma F_66f58 : fetch_word Plain.M.loaded_segments (0x66f58 : word) = Some W_66f58.
Proof. vm_refl. Qed.
Lemma D_66f58 : decode_any W_66f58 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f5c : bv 32 := 0xfec68ae3.
Lemma F_66f5c : fetch_word Plain.M.loaded_segments (0x66f5c : word) = Some W_66f5c.
Proof. vm_refl. Qed.
Lemma D_66f5c : decode_any W_66f5c = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f60 : bv 32 := 0xfe069ae3.
Lemma F_66f60 : fetch_word Plain.M.loaded_segments (0x66f60 : word) = Some W_66f60.
Proof. vm_refl. Qed.
Lemma D_66f60 : decode_any W_66f60 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f64 : bv 32 := 0x03010513.
Lemma F_66f64 : fetch_word Plain.M.loaded_segments (0x66f64 : word) = Some W_66f64.
Proof. vm_refl. Qed.
Lemma D_66f64 : decode_any W_66f64 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f68 : bv 32 := 0x2ec000ef.
Lemma F_66f68 : fetch_word Plain.M.loaded_segments (0x66f68 : word) = Some W_66f68.
Proof. vm_refl. Qed.
Lemma D_66f68 : decode_any W_66f68 = Some (Jal 1 748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f6c : bv 32 := 0x0f813503.
Lemma F_66f6c : fetch_word Plain.M.loaded_segments (0x66f6c : word) = Some W_66f6c.
Proof. vm_refl. Qed.
Lemma D_66f6c : decode_any W_66f6c = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f70 : bv 32 := 0x594000ef.
Lemma F_66f70 : fetch_word Plain.M.loaded_segments (0x66f70 : word) = Some W_66f70.
Proof. vm_refl. Qed.
Lemma D_66f70 : decode_any W_66f70 = Some (Jal 1 1428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f74 : bv 32 := 0x08813503.
Lemma F_66f74 : fetch_word Plain.M.loaded_segments (0x66f74 : word) = Some W_66f74.
Proof. vm_refl. Qed.
Lemma D_66f74 : decode_any W_66f74 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f78 : bv 32 := 0x09013583.
Lemma F_66f78 : fetch_word Plain.M.loaded_segments (0x66f78 : word) = Some W_66f78.
Proof. vm_refl. Qed.
Lemma D_66f78 : decode_any W_66f78 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f7c : bv 32 := 0x00b51c63.
Lemma F_66f7c : fetch_word Plain.M.loaded_segments (0x66f7c : word) = Some W_66f7c.
Proof. vm_refl. Qed.
Lemma D_66f7c : decode_any W_66f7c = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f80 : bv 32 := 0x09813503.
Lemma F_66f80 : fetch_word Plain.M.loaded_segments (0x66f80 : word) = Some W_66f80.
Proof. vm_refl. Qed.
Lemma D_66f80 : decode_any W_66f80 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f84 : bv 32 := 0x0a013583.
Lemma F_66f84 : fetch_word Plain.M.loaded_segments (0x66f84 : word) = Some W_66f84.
Proof. vm_refl. Qed.
Lemma D_66f84 : decode_any W_66f84 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f88 : bv 32 := 0x00b51663.
Lemma F_66f88 : fetch_word Plain.M.loaded_segments (0x66f88 : word) = Some W_66f88.
Proof. vm_refl. Qed.
Lemma D_66f88 : decode_any W_66f88 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f8c : bv 32 := 0x0e813503.
Lemma F_66f8c : fetch_word Plain.M.loaded_segments (0x66f8c : word) = Some W_66f8c.
Proof. vm_refl. Qed.
Lemma D_66f8c : decode_any W_66f8c = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f90 : bv 32 := 0x0e050063.
Lemma F_66f90 : fetch_word Plain.M.loaded_segments (0x66f90 : word) = Some W_66f90.
Proof. vm_refl. Qed.
Lemma D_66f90 : decode_any W_66f90 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f94 : bv 32 := 0x00200693.
Lemma F_66f94 : fetch_word Plain.M.loaded_segments (0x66f94 : word) = Some W_66f94.
Proof. vm_refl. Qed.
Lemma D_66f94 : decode_any W_66f94 = Some (OpImm ALU_ADD 13 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f98 : bv 32 := 0x00100793.
Lemma F_66f98 : fetch_word Plain.M.loaded_segments (0x66f98 : word) = Some W_66f98.
Proof. vm_refl. Qed.
Lemma D_66f98 : decode_any W_66f98 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f9c : bv 32 := 0x00013423.
Lemma F_66f9c : fetch_word Plain.M.loaded_segments (0x66f9c : word) = Some W_66f9c.
Proof. vm_refl. Qed.
Lemma D_66f9c : decode_any W_66f9c = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fa0 : bv 32 := 0x00013823.
Lemma F_66fa0 : fetch_word Plain.M.loaded_segments (0x66fa0 : word) = Some W_66fa0.
Proof. vm_refl. Qed.
Lemma D_66fa0 : decode_any W_66fa0 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fa4 : bv 32 := 0x04900893.
Lemma F_66fa4 : fetch_word Plain.M.loaded_segments (0x66fa4 : word) = Some W_66fa4.
Proof. vm_refl. Qed.
Lemma D_66fa4 : decode_any W_66fa4 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fa8 : bv 32 := 0x01810513.
Lemma F_66fa8 : fetch_word Plain.M.loaded_segments (0x66fa8 : word) = Some W_66fa8.
Proof. vm_refl. Qed.
Lemma D_66fa8 : decode_any W_66fa8 = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fac : bv 32 := 0x00300593.
Lemma F_66fac : fetch_word Plain.M.loaded_segments (0x66fac : word) = Some W_66fac.
Proof. vm_refl. Qed.
Lemma D_66fac : decode_any W_66fac = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fb0 : bv 32 := 0x00810613.
Lemma F_66fb0 : fetch_word Plain.M.loaded_segments (0x66fb0 : word) = Some W_66fb0.
Proof. vm_refl. Qed.
Lemma D_66fb0 : decode_any W_66fb0 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fb4 : bv 32 := 0x00800713.
Lemma F_66fb4 : fetch_word Plain.M.loaded_segments (0x66fb4 : word) = Some W_66fb4.
Proof. vm_refl. Qed.
Lemma D_66fb4 : decode_any W_66fb4 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fb8 : bv 32 := 0x00013c23.
Lemma F_66fb8 : fetch_word Plain.M.loaded_segments (0x66fb8 : word) = Some W_66fb8.
Proof. vm_refl. Qed.
Lemma D_66fb8 : decode_any W_66fb8 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fbc : bv 32 := 0x02f13023.
Lemma F_66fbc : fetch_word Plain.M.loaded_segments (0x66fbc : word) = Some W_66fbc.
Proof. vm_refl. Qed.
Lemma D_66fbc : decode_any W_66fbc = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fc0 : bv 32 := 0x02d13423.
Lemma F_66fc0 : fetch_word Plain.M.loaded_segments (0x66fc0 : word) = Some W_66fc0.
Proof. vm_refl. Qed.
Lemma D_66fc0 : decode_any W_66fc0 = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fc4 : bv 32 := 0x00000693.
Lemma F_66fc4 : fetch_word Plain.M.loaded_segments (0x66fc4 : word) = Some W_66fc4.
Proof. vm_refl. Qed.
Lemma D_66fc4 : decode_any W_66fc4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fc8 : bv 32 := 0x00000073.
Lemma F_66fc8 : fetch_word Plain.M.loaded_segments (0x66fc8 : word) = Some W_66fc8.
Proof. vm_refl. Qed.
Lemma D_66fc8 : decode_any W_66fc8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_66fc8 : is_ecall W_66fc8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_66fcc : bv 32 := 0x02051513.
Lemma F_66fcc : fetch_word Plain.M.loaded_segments (0x66fcc : word) = Some W_66fcc.
Proof. vm_refl. Qed.
Lemma D_66fcc : decode_any W_66fcc = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fd0 : bv 32 := 0x00055463.
Lemma F_66fd0 : fetch_word Plain.M.loaded_segments (0x66fd0 : word) = Some W_66fd0.
Proof. vm_refl. Qed.
Lemma D_66fd0 : decode_any W_66fd0 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fd4 : bv 32 := 0x00000023.
Lemma F_66fd4 : fetch_word Plain.M.loaded_segments (0x66fd4 : word) = Some W_66fd4.
Proof. vm_refl. Qed.
Lemma D_66fd4 : decode_any W_66fd4 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fd8 : bv 32 := 0x01e15503.
Lemma F_66fd8 : fetch_word Plain.M.loaded_segments (0x66fd8 : word) = Some W_66fd8.
Proof. vm_refl. Qed.
Lemma D_66fd8 : decode_any W_66fd8 = Some (Load SZ2 false 10 2 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fdc : bv 32 := 0x02057513.
Lemma F_66fdc : fetch_word Plain.M.loaded_segments (0x66fdc : word) = Some W_66fdc.
Proof. vm_refl. Qed.
Lemma D_66fdc : decode_any W_66fdc = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fe0 : bv 32 := 0x02050463.
Lemma F_66fe0 : fetch_word Plain.M.loaded_segments (0x66fe0 : word) = Some W_66fe0.
Proof. vm_refl. Qed.
Lemma D_66fe0 : decode_any W_66fe0 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fe4 : bv 32 := 0xfffae517.
Lemma F_66fe4 : fetch_word Plain.M.loaded_segments (0x66fe4 : word) = Some W_66fe4.
Proof. vm_refl. Qed.
Lemma D_66fe4 : decode_any W_66fe4 = Some (Auipc 10 1048494, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fe8 : bv 32 := 0x00008637.
Lemma F_66fe8 : fetch_word Plain.M.loaded_segments (0x66fe8 : word) = Some W_66fe8.
Proof. vm_refl. Qed.
Lemma D_66fe8 : decode_any W_66fe8 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fec : bv 32 := 0x03800893.
Lemma F_66fec : fetch_word Plain.M.loaded_segments (0x66fec : word) = Some W_66fec.
Proof. vm_refl. Qed.
Lemma D_66fec : decode_any W_66fec = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ff0 : bv 32 := 0xde150593.
Lemma F_66ff0 : fetch_word Plain.M.loaded_segments (0x66ff0 : word) = Some W_66ff0.
Proof. vm_refl. Qed.
Lemma D_66ff0 : decode_any W_66ff0 = Some (OpImm ALU_ADD 11 10 3553, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ff4 : bv 32 := 0x0026061b.
Lemma F_66ff4 : fetch_word Plain.M.loaded_segments (0x66ff4 : word) = Some W_66ff4.
Proof. vm_refl. Qed.
Lemma D_66ff4 : decode_any W_66ff4 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ff8 : bv 32 := 0xf9c00513.
Lemma F_66ff8 : fetch_word Plain.M.loaded_segments (0x66ff8 : word) = Some W_66ff8.
Proof. vm_refl. Qed.
Lemma D_66ff8 : decode_any W_66ff8 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ffc : bv 32 := 0x00000073.
Lemma F_66ffc : fetch_word Plain.M.loaded_segments (0x66ffc : word) = Some W_66ffc.
Proof. vm_refl. Qed.
Lemma D_66ffc : decode_any W_66ffc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_66ffc : is_ecall W_66ffc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_67000 : bv 32 := 0x00055463.
Lemma F_67000 : fetch_word Plain.M.loaded_segments (0x67000 : word) = Some W_67000.
Proof. vm_refl. Qed.
Lemma D_67000 : decode_any W_67000 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67004 : bv 32 := 0x00000023.
Lemma F_67004 : fetch_word Plain.M.loaded_segments (0x67004 : word) = Some W_67004.
Proof. vm_refl. Qed.
Lemma D_67004 : decode_any W_67004 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67008 : bv 32 := 0x02615503.
Lemma F_67008 : fetch_word Plain.M.loaded_segments (0x67008 : word) = Some W_67008.
Proof. vm_refl. Qed.
Lemma D_67008 : decode_any W_67008 = Some (Load SZ2 false 10 2 38, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6700c : bv 32 := 0x02057513.
Lemma F_6700c : fetch_word Plain.M.loaded_segments (0x6700c : word) = Some W_6700c.
Proof. vm_refl. Qed.
Lemma D_6700c : decode_any W_6700c = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67010 : bv 32 := 0x02050463.
Lemma F_67010 : fetch_word Plain.M.loaded_segments (0x67010 : word) = Some W_67010.
Proof. vm_refl. Qed.
Lemma D_67010 : decode_any W_67010 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67014 : bv 32 := 0xfffae517.
Lemma F_67014 : fetch_word Plain.M.loaded_segments (0x67014 : word) = Some W_67014.
Proof. vm_refl. Qed.
Lemma D_67014 : decode_any W_67014 = Some (Auipc 10 1048494, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67018 : bv 32 := 0x00008637.
Lemma F_67018 : fetch_word Plain.M.loaded_segments (0x67018 : word) = Some W_67018.
Proof. vm_refl. Qed.
Lemma D_67018 : decode_any W_67018 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6701c : bv 32 := 0x03800893.
Lemma F_6701c : fetch_word Plain.M.loaded_segments (0x6701c : word) = Some W_6701c.
Proof. vm_refl. Qed.
Lemma D_6701c : decode_any W_6701c = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67020 : bv 32 := 0xdb150593.
Lemma F_67020 : fetch_word Plain.M.loaded_segments (0x67020 : word) = Some W_67020.
Proof. vm_refl. Qed.
Lemma D_67020 : decode_any W_67020 = Some (OpImm ALU_ADD 11 10 3505, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67024 : bv 32 := 0x0026061b.
Lemma F_67024 : fetch_word Plain.M.loaded_segments (0x67024 : word) = Some W_67024.
Proof. vm_refl. Qed.
Lemma D_67024 : decode_any W_67024 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67028 : bv 32 := 0xf9c00513.
Lemma F_67028 : fetch_word Plain.M.loaded_segments (0x67028 : word) = Some W_67028.
Proof. vm_refl. Qed.
Lemma D_67028 : decode_any W_67028 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6702c : bv 32 := 0x00000073.
Lemma F_6702c : fetch_word Plain.M.loaded_segments (0x6702c : word) = Some W_6702c.
Proof. vm_refl. Qed.
Lemma D_6702c : decode_any W_6702c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6702c : is_ecall W_6702c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_67030 : bv 32 := 0x00055463.
Lemma F_67030 : fetch_word Plain.M.loaded_segments (0x67030 : word) = Some W_67030.
Proof. vm_refl. Qed.
Lemma D_67030 : decode_any W_67030 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67034 : bv 32 := 0x00000023.
Lemma F_67034 : fetch_word Plain.M.loaded_segments (0x67034 : word) = Some W_67034.
Proof. vm_refl. Qed.
Lemma D_67034 : decode_any W_67034 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67038 : bv 32 := 0x02e15503.
Lemma F_67038 : fetch_word Plain.M.loaded_segments (0x67038 : word) = Some W_67038.
Proof. vm_refl. Qed.
Lemma D_67038 : decode_any W_67038 = Some (Load SZ2 false 10 2 46, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6703c : bv 32 := 0x02057513.
Lemma F_6703c : fetch_word Plain.M.loaded_segments (0x6703c : word) = Some W_6703c.
Proof. vm_refl. Qed.
Lemma D_6703c : decode_any W_6703c = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67040 : bv 32 := 0x02050463.
Lemma F_67040 : fetch_word Plain.M.loaded_segments (0x67040 : word) = Some W_67040.
Proof. vm_refl. Qed.
Lemma D_67040 : decode_any W_67040 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67044 : bv 32 := 0xfffae517.
Lemma F_67044 : fetch_word Plain.M.loaded_segments (0x67044 : word) = Some W_67044.
Proof. vm_refl. Qed.
Lemma D_67044 : decode_any W_67044 = Some (Auipc 10 1048494, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67048 : bv 32 := 0x00008637.
Lemma F_67048 : fetch_word Plain.M.loaded_segments (0x67048 : word) = Some W_67048.
Proof. vm_refl. Qed.
Lemma D_67048 : decode_any W_67048 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6704c : bv 32 := 0x03800893.
Lemma F_6704c : fetch_word Plain.M.loaded_segments (0x6704c : word) = Some W_6704c.
Proof. vm_refl. Qed.
Lemma D_6704c : decode_any W_6704c = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67050 : bv 32 := 0xd8150593.
Lemma F_67050 : fetch_word Plain.M.loaded_segments (0x67050 : word) = Some W_67050.
Proof. vm_refl. Qed.
Lemma D_67050 : decode_any W_67050 = Some (OpImm ALU_ADD 11 10 3457, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67054 : bv 32 := 0x0026061b.
Lemma F_67054 : fetch_word Plain.M.loaded_segments (0x67054 : word) = Some W_67054.
Proof. vm_refl. Qed.
Lemma D_67054 : decode_any W_67054 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67058 : bv 32 := 0xf9c00513.
Lemma F_67058 : fetch_word Plain.M.loaded_segments (0x67058 : word) = Some W_67058.
Proof. vm_refl. Qed.
Lemma D_67058 : decode_any W_67058 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6705c : bv 32 := 0x00000073.
Lemma F_6705c : fetch_word Plain.M.loaded_segments (0x6705c : word) = Some W_6705c.
Proof. vm_refl. Qed.
Lemma D_6705c : decode_any W_6705c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6705c : is_ecall W_6705c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_67060 : bv 32 := 0x00055463.
Lemma F_67060 : fetch_word Plain.M.loaded_segments (0x67060 : word) = Some W_67060.
Proof. vm_refl. Qed.
Lemma D_67060 : decode_any W_67060 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67064 : bv 32 := 0x00000023.
Lemma F_67064 : fetch_word Plain.M.loaded_segments (0x67064 : word) = Some W_67064.
Proof. vm_refl. Qed.
Lemma D_67064 : decode_any W_67064 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67068 : bv 32 := 0x00100513.
Lemma F_67068 : fetch_word Plain.M.loaded_segments (0x67068 : word) = Some W_67068.
Proof. vm_refl. Qed.
Lemma D_67068 : decode_any W_67068 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6706c : bv 32 := 0x00a90123.
Lemma F_6706c : fetch_word Plain.M.loaded_segments (0x6706c : word) = Some W_6706c.
Proof. vm_refl. Qed.
Lemma D_6706c : decode_any W_6706c = Some (Store SZ1 18 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67070 : bv 32 := 0x17813083.
Lemma F_67070 : fetch_word Plain.M.loaded_segments (0x67070 : word) = Some W_67070.
Proof. vm_refl. Qed.
Lemma D_67070 : decode_any W_67070 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67074 : bv 32 := 0x17013403.
Lemma F_67074 : fetch_word Plain.M.loaded_segments (0x67074 : word) = Some W_67074.
Proof. vm_refl. Qed.
Lemma D_67074 : decode_any W_67074 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67078 : bv 32 := 0x16813483.
Lemma F_67078 : fetch_word Plain.M.loaded_segments (0x67078 : word) = Some W_67078.
Proof. vm_refl. Qed.
Lemma D_67078 : decode_any W_67078 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6707c : bv 32 := 0x16013903.
Lemma F_6707c : fetch_word Plain.M.loaded_segments (0x6707c : word) = Some W_6707c.
Proof. vm_refl. Qed.
Lemma D_6707c : decode_any W_6707c = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67080 : bv 32 := 0x18010113.
Lemma F_67080 : fetch_word Plain.M.loaded_segments (0x67080 : word) = Some W_67080.
Proof. vm_refl. Qed.
Lemma D_67080 : decode_any W_67080 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67084 : bv 32 := 0x00008067.
Lemma F_67084 : fetch_word Plain.M.loaded_segments (0x67084 : word) = Some W_67084.
Proof. vm_refl. Qed.
Lemma D_67084 : decode_any W_67084 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67088 : bv 32 := 0xfe010113.
Lemma F_67088 : fetch_word Plain.M.loaded_segments (0x67088 : word) = Some W_67088.
Proof. vm_refl. Qed.
Lemma D_67088 : decode_any W_67088 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6708c : bv 32 := 0x00113c23.
Lemma F_6708c : fetch_word Plain.M.loaded_segments (0x6708c : word) = Some W_6708c.
Proof. vm_refl. Qed.
Lemma D_6708c : decode_any W_6708c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67090 : bv 32 := 0x00813823.
Lemma F_67090 : fetch_word Plain.M.loaded_segments (0x67090 : word) = Some W_67090.
Proof. vm_refl. Qed.
Lemma D_67090 : decode_any W_67090 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67094 : bv 32 := 0x00913423.
Lemma F_67094 : fetch_word Plain.M.loaded_segments (0x67094 : word) = Some W_67094.
Proof. vm_refl. Qed.
Lemma D_67094 : decode_any W_67094 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67098 : bv 32 := 0xdc1ff0ef.
Lemma F_67098 : fetch_word Plain.M.loaded_segments (0x67098 : word) = Some W_67098.
Proof. vm_refl. Qed.
Lemma D_67098 : decode_any W_67098 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6709c : bv 32 := 0x00018517.
Lemma F_6709c : fetch_word Plain.M.loaded_segments (0x6709c : word) = Some W_6709c.
Proof. vm_refl. Qed.
Lemma D_6709c : decode_any W_6709c = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670a0 : bv 32 := 0x00018597.
Lemma F_670a0 : fetch_word Plain.M.loaded_segments (0x670a0 : word) = Some W_670a0.
Proof. vm_refl. Qed.
Lemma D_670a0 : decode_any W_670a0 = Some (Auipc 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670a4 : bv 32 := 0x78c53403.
Lemma F_670a4 : fetch_word Plain.M.loaded_segments (0x670a4 : word) = Some W_670a4.
Proof. vm_refl. Qed.
Lemma D_670a4 : decode_any W_670a4 = Some (Load SZ8 true 8 10 1932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670a8 : bv 32 := 0x7905b483.
Lemma F_670a8 : fetch_word Plain.M.loaded_segments (0x670a8 : word) = Some W_670a8.
Proof. vm_refl. Qed.
Lemma D_670a8 : decode_any W_670a8 = Some (Load SZ8 true 9 11 1936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670ac : bv 32 := 0x0084fa63.
Lemma F_670ac : fetch_word Plain.M.loaded_segments (0x670ac : word) = Some W_670ac.
Proof. vm_refl. Qed.
Lemma D_670ac : decode_any W_670ac = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670b0 : bv 32 := 0x0004b503.
Lemma F_670b0 : fetch_word Plain.M.loaded_segments (0x670b0 : word) = Some W_670b0.
Proof. vm_refl. Qed.
Lemma D_670b0 : decode_any W_670b0 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670b4 : bv 32 := 0x000500e7.
Lemma F_670b4 : fetch_word Plain.M.loaded_segments (0x670b4 : word) = Some W_670b4.
Proof. vm_refl. Qed.
Lemma D_670b4 : decode_any W_670b4 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670b8 : bv 32 := 0x00848493.
Lemma F_670b8 : fetch_word Plain.M.loaded_segments (0x670b8 : word) = Some W_670b8.
Proof. vm_refl. Qed.
Lemma D_670b8 : decode_any W_670b8 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670bc : bv 32 := 0xfe84eae3.
Lemma F_670bc : fetch_word Plain.M.loaded_segments (0x670bc : word) = Some W_670bc.
Proof. vm_refl. Qed.
Lemma D_670bc : decode_any W_670bc = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670c0 : bv 32 := 0x01813083.
Lemma F_670c0 : fetch_word Plain.M.loaded_segments (0x670c0 : word) = Some W_670c0.
Proof. vm_refl. Qed.
Lemma D_670c0 : decode_any W_670c0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670c4 : bv 32 := 0x01013403.
Lemma F_670c4 : fetch_word Plain.M.loaded_segments (0x670c4 : word) = Some W_670c4.
Proof. vm_refl. Qed.
Lemma D_670c4 : decode_any W_670c4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670c8 : bv 32 := 0x00813483.
Lemma F_670c8 : fetch_word Plain.M.loaded_segments (0x670c8 : word) = Some W_670c8.
Proof. vm_refl. Qed.
Lemma D_670c8 : decode_any W_670c8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670cc : bv 32 := 0x02010113.
Lemma F_670cc : fetch_word Plain.M.loaded_segments (0x670cc : word) = Some W_670cc.
Proof. vm_refl. Qed.
Lemma D_670cc : decode_any W_670cc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670d0 : bv 32 := 0x00008067.
Lemma F_670d0 : fetch_word Plain.M.loaded_segments (0x670d0 : word) = Some W_670d0.
Proof. vm_refl. Qed.
Lemma D_670d0 : decode_any W_670d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670d4 : bv 32 := 0xfe010113.
Lemma F_670d4 : fetch_word Plain.M.loaded_segments (0x670d4 : word) = Some W_670d4.
Proof. vm_refl. Qed.
Lemma D_670d4 : decode_any W_670d4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670d8 : bv 32 := 0x00113c23.
Lemma F_670d8 : fetch_word Plain.M.loaded_segments (0x670d8 : word) = Some W_670d8.
Proof. vm_refl. Qed.
Lemma D_670d8 : decode_any W_670d8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670dc : bv 32 := 0x00813823.
Lemma F_670dc : fetch_word Plain.M.loaded_segments (0x670dc : word) = Some W_670dc.
Proof. vm_refl. Qed.
Lemma D_670dc : decode_any W_670dc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670e0 : bv 32 := 0x00913423.
Lemma F_670e0 : fetch_word Plain.M.loaded_segments (0x670e0 : word) = Some W_670e0.
Proof. vm_refl. Qed.
Lemma D_670e0 : decode_any W_670e0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670e4 : bv 32 := 0x01213023.
Lemma F_670e4 : fetch_word Plain.M.loaded_segments (0x670e4 : word) = Some W_670e4.
Proof. vm_refl. Qed.
Lemma D_670e4 : decode_any W_670e4 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670e8 : bv 32 := 0x00060413.
Lemma F_670e8 : fetch_word Plain.M.loaded_segments (0x670e8 : word) = Some W_670e8.
Proof. vm_refl. Qed.
Lemma D_670e8 : decode_any W_670e8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670ec : bv 32 := 0x00058493.
Lemma F_670ec : fetch_word Plain.M.loaded_segments (0x670ec : word) = Some W_670ec.
Proof. vm_refl. Qed.
Lemma D_670ec : decode_any W_670ec = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670f0 : bv 32 := 0x00050913.
Lemma F_670f0 : fetch_word Plain.M.loaded_segments (0x670f0 : word) = Some W_670f0.
Proof. vm_refl. Qed.
Lemma D_670f0 : decode_any W_670f0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670f4 : bv 32 := 0x00063583.
Lemma F_670f4 : fetch_word Plain.M.loaded_segments (0x670f4 : word) = Some W_670f4.
Proof. vm_refl. Qed.
Lemma D_670f4 : decode_any W_670f4 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670f8 : bv 32 := 0x00349513.
Lemma F_670f8 : fetch_word Plain.M.loaded_segments (0x670f8 : word) = Some W_670f8.
Proof. vm_refl. Qed.
Lemma D_670f8 : decode_any W_670f8 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670fc : bv 32 := 0x00a60533.
Lemma F_670fc : fetch_word Plain.M.loaded_segments (0x670fc : word) = Some W_670fc.
Proof. vm_refl. Qed.
Lemma D_670fc : decode_any W_670fc = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67100 : bv 32 := 0x00850513.
Lemma F_67100 : fetch_word Plain.M.loaded_segments (0x67100 : word) = Some W_67100.
Proof. vm_refl. Qed.
Lemma D_67100 : decode_any W_67100 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67104 : bv 32 := 0xd59ff0ef.
Lemma F_67104 : fetch_word Plain.M.loaded_segments (0x67104 : word) = Some W_67104.
Proof. vm_refl. Qed.
Lemma D_67104 : decode_any W_67104 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67108 : bv 32 := 0x00000517.
Lemma F_67108 : fetch_word Plain.M.loaded_segments (0x67108 : word) = Some W_67108.
Proof. vm_refl. Qed.
Lemma D_67108 : decode_any W_67108 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6710c : bv 32 := 0x02c50313.
Lemma F_6710c : fetch_word Plain.M.loaded_segments (0x6710c : word) = Some W_6710c.
Proof. vm_refl. Qed.
Lemma D_6710c : decode_any W_6710c = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67110 : bv 32 := 0x00090513.
Lemma F_67110 : fetch_word Plain.M.loaded_segments (0x67110 : word) = Some W_67110.
Proof. vm_refl. Qed.
Lemma D_67110 : decode_any W_67110 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67114 : bv 32 := 0x00048593.
Lemma F_67114 : fetch_word Plain.M.loaded_segments (0x67114 : word) = Some W_67114.
Proof. vm_refl. Qed.
Lemma D_67114 : decode_any W_67114 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67118 : bv 32 := 0x00040613.
Lemma F_67118 : fetch_word Plain.M.loaded_segments (0x67118 : word) = Some W_67118.
Proof. vm_refl. Qed.
Lemma D_67118 : decode_any W_67118 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6711c : bv 32 := 0x01813083.
Lemma F_6711c : fetch_word Plain.M.loaded_segments (0x6711c : word) = Some W_6711c.
Proof. vm_refl. Qed.
Lemma D_6711c : decode_any W_6711c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67120 : bv 32 := 0x01013403.
Lemma F_67120 : fetch_word Plain.M.loaded_segments (0x67120 : word) = Some W_67120.
Proof. vm_refl. Qed.
Lemma D_67120 : decode_any W_67120 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67124 : bv 32 := 0x00813483.
Lemma F_67124 : fetch_word Plain.M.loaded_segments (0x67124 : word) = Some W_67124.
Proof. vm_refl. Qed.
Lemma D_67124 : decode_any W_67124 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67128 : bv 32 := 0x00013903.
Lemma F_67128 : fetch_word Plain.M.loaded_segments (0x67128 : word) = Some W_67128.
Proof. vm_refl. Qed.
Lemma D_67128 : decode_any W_67128 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6712c : bv 32 := 0x02010113.
Lemma F_6712c : fetch_word Plain.M.loaded_segments (0x6712c : word) = Some W_6712c.
Proof. vm_refl. Qed.
Lemma D_6712c : decode_any W_6712c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67130 : bv 32 := 0x00030067.
Lemma F_67130 : fetch_word Plain.M.loaded_segments (0x67130 : word) = Some W_67130.
Proof. vm_refl. Qed.
Lemma D_67130 : decode_any W_67130 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67134 : bv 32 := 0xfd010113.
Lemma F_67134 : fetch_word Plain.M.loaded_segments (0x67134 : word) = Some W_67134.
Proof. vm_refl. Qed.
Lemma D_67134 : decode_any W_67134 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67138 : bv 32 := 0x02113423.
Lemma F_67138 : fetch_word Plain.M.loaded_segments (0x67138 : word) = Some W_67138.
Proof. vm_refl. Qed.
Lemma D_67138 : decode_any W_67138 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6713c : bv 32 := 0x02813023.
Lemma F_6713c : fetch_word Plain.M.loaded_segments (0x6713c : word) = Some W_6713c.
Proof. vm_refl. Qed.
Lemma D_6713c : decode_any W_6713c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67140 : bv 32 := 0x00913c23.
Lemma F_67140 : fetch_word Plain.M.loaded_segments (0x67140 : word) = Some W_67140.
Proof. vm_refl. Qed.
Lemma D_67140 : decode_any W_67140 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67144 : bv 32 := 0x01213823.
Lemma F_67144 : fetch_word Plain.M.loaded_segments (0x67144 : word) = Some W_67144.
Proof. vm_refl. Qed.
Lemma D_67144 : decode_any W_67144 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67148 : bv 32 := 0x01313423.
Lemma F_67148 : fetch_word Plain.M.loaded_segments (0x67148 : word) = Some W_67148.
Proof. vm_refl. Qed.
Lemma D_67148 : decode_any W_67148 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6714c : bv 32 := 0x00060413.
Lemma F_6714c : fetch_word Plain.M.loaded_segments (0x6714c : word) = Some W_6714c.
Proof. vm_refl. Qed.
Lemma D_6714c : decode_any W_6714c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67150 : bv 32 := 0x00058493.
Lemma F_67150 : fetch_word Plain.M.loaded_segments (0x67150 : word) = Some W_67150.
Proof. vm_refl. Qed.
Lemma D_67150 : decode_any W_67150 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67154 : bv 32 := 0x00050913.
Lemma F_67154 : fetch_word Plain.M.loaded_segments (0x67154 : word) = Some W_67154.
Proof. vm_refl. Qed.
Lemma D_67154 : decode_any W_67154 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67158 : bv 32 := 0x00359513.
Lemma F_67158 : fetch_word Plain.M.loaded_segments (0x67158 : word) = Some W_67158.
Proof. vm_refl. Qed.
Lemma D_67158 : decode_any W_67158 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6715c : bv 32 := 0x00a60533.
Lemma F_6715c : fetch_word Plain.M.loaded_segments (0x6715c : word) = Some W_6715c.
Proof. vm_refl. Qed.
Lemma D_6715c : decode_any W_6715c = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67160 : bv 32 := 0x00850993.
Lemma F_67160 : fetch_word Plain.M.loaded_segments (0x67160 : word) = Some W_67160.
Proof. vm_refl. Qed.
Lemma D_67160 : decode_any W_67160 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67164 : bv 32 := 0xf25ff0ef.
Lemma F_67164 : fetch_word Plain.M.loaded_segments (0x67164 : word) = Some W_67164.
Proof. vm_refl. Qed.
Lemma D_67164 : decode_any W_67164 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67168 : bv 32 := 0x00048513.
Lemma F_67168 : fetch_word Plain.M.loaded_segments (0x67168 : word) = Some W_67168.
Proof. vm_refl. Qed.
Lemma D_67168 : decode_any W_67168 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6716c : bv 32 := 0x00040593.
Lemma F_6716c : fetch_word Plain.M.loaded_segments (0x6716c : word) = Some W_6716c.
Proof. vm_refl. Qed.
Lemma D_6716c : decode_any W_6716c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67170 : bv 32 := 0x00098613.
Lemma F_67170 : fetch_word Plain.M.loaded_segments (0x67170 : word) = Some W_67170.
Proof. vm_refl. Qed.
Lemma D_67170 : decode_any W_67170 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67174 : bv 32 := 0x000900e7.
Lemma F_67174 : fetch_word Plain.M.loaded_segments (0x67174 : word) = Some W_67174.
Proof. vm_refl. Qed.
Lemma D_67174 : decode_any W_67174 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67178 : bv 32 := 0x700000ef.
Lemma F_67178 : fetch_word Plain.M.loaded_segments (0x67178 : word) = Some W_67178.
Proof. vm_refl. Qed.
Lemma D_67178 : decode_any W_67178 = Some (Jal 1 1792, 4%Z).
Proof. vm_refl. Qed.
