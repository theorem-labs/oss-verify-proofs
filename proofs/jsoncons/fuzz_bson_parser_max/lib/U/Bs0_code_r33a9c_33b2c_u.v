(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_33e6c : bv 32 := 0xff010113.
Lemma F_33e6c : fetch_word Ubsan.M.loaded_segments (0x341ec : word) = Some W_33e6c.
Proof. vm_refl. Qed.
Lemma D_33e6c : decode_any W_33e6c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e70 : bv 32 := 0x00113423.
Lemma F_33e70 : fetch_word Ubsan.M.loaded_segments (0x341f0 : word) = Some W_33e70.
Proof. vm_refl. Qed.
Lemma D_33e70 : decode_any W_33e70 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e74 : bv 32 := 0x00813023.
Lemma F_33e74 : fetch_word Ubsan.M.loaded_segments (0x341f4 : word) = Some W_33e74.
Proof. vm_refl. Qed.
Lemma D_33e74 : decode_any W_33e74 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e78 : bv 32 := 0x01010413.
Lemma F_33e78 : fetch_word Ubsan.M.loaded_segments (0x341f8 : word) = Some W_33e78.
Proof. vm_refl. Qed.
Lemma D_33e78 : decode_any W_33e78 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e7c : bv 32 := 0x00084517.
Lemma F_33e7c : fetch_word Ubsan.M.loaded_segments (0x341fc : word) = Some W_33e7c.
Proof. vm_refl. Qed.
Lemma D_33e7c : decode_any W_33e7c = Some (Auipc 10 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e80 : bv 32 := 0x34c50513.
Lemma F_33e80 : fetch_word Ubsan.M.loaded_segments (0x34200 : word) = Some W_33e80.
Proof. vm_refl. Qed.
Lemma D_33e80 : decode_any W_33e80 = Some (OpImm ALU_ADD 10 10 844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e84 : bv 32 := 0x00054503.
Lemma F_33e84 : fetch_word Ubsan.M.loaded_segments (0x34204 : word) = Some W_33e84.
Proof. vm_refl. Qed.
Lemma D_33e84 : decode_any W_33e84 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e88 : bv 32 := 0x00157513.
Lemma F_33e88 : fetch_word Ubsan.M.loaded_segments (0x34208 : word) = Some W_33e88.
Proof. vm_refl. Qed.
Lemma D_33e88 : decode_any W_33e88 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e8c : bv 32 := 0x00050663.
Lemma F_33e8c : fetch_word Ubsan.M.loaded_segments (0x3420c : word) = Some W_33e8c.
Proof. vm_refl. Qed.
Lemma D_33e8c : decode_any W_33e8c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e90 : bv 32 := 0x0040006f.
Lemma F_33e90 : fetch_word Ubsan.M.loaded_segments (0x34210 : word) = Some W_33e90.
Proof. vm_refl. Qed.
Lemma D_33e90 : decode_any W_33e90 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e94 : bv 32 := 0x0580006f.
Lemma F_33e94 : fetch_word Ubsan.M.loaded_segments (0x34214 : word) = Some W_33e94.
Proof. vm_refl. Qed.
Lemma D_33e94 : decode_any W_33e94 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e98 : bv 32 := 0x00084517.
Lemma F_33e98 : fetch_word Ubsan.M.loaded_segments (0x34218 : word) = Some W_33e98.
Proof. vm_refl. Qed.
Lemma D_33e98 : decode_any W_33e98 = Some (Auipc 10 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e9c : bv 32 := 0x33050593.
Lemma F_33e9c : fetch_word Ubsan.M.loaded_segments (0x3421c : word) = Some W_33e9c.
Proof. vm_refl. Qed.
Lemma D_33e9c : decode_any W_33e9c = Some (OpImm ALU_ADD 11 10 816, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ea0 : bv 32 := 0x00100513.
Lemma F_33ea0 : fetch_word Ubsan.M.loaded_segments (0x34220 : word) = Some W_33ea0.
Proof. vm_refl. Qed.
Lemma D_33ea0 : decode_any W_33ea0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ea4 : bv 32 := 0x00a58023.
Lemma F_33ea4 : fetch_word Ubsan.M.loaded_segments (0x34224 : word) = Some W_33ea4.
Proof. vm_refl. Qed.
Lemma D_33ea4 : decode_any W_33ea4 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ea8 : bv 32 := 0x00083517.
Lemma F_33ea8 : fetch_word Ubsan.M.loaded_segments (0x34228 : word) = Some W_33ea8.
Proof. vm_refl. Qed.
Lemma D_33ea8 : decode_any W_33ea8 = Some (Auipc 10 131, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33eac : bv 32 := 0xe5853503.
Lemma F_33eac : fetch_word Ubsan.M.loaded_segments (0x3422c : word) = Some W_33eac.
Proof. vm_refl. Qed.
Lemma D_33eac : decode_any W_33eac = Some (Load SZ8 true 10 10 3672, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33eb0 : bv 32 := 0x00050e63.
Lemma F_33eb0 : fetch_word Ubsan.M.loaded_segments (0x34230 : word) = Some W_33eb0.
Proof. vm_refl. Qed.
Lemma D_33eb0 : decode_any W_33eb0 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33eb4 : bv 32 := 0x0040006f.
Lemma F_33eb4 : fetch_word Ubsan.M.loaded_segments (0x34234 : word) = Some W_33eb4.
Proof. vm_refl. Qed.
Lemma D_33eb4 : decode_any W_33eb4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33eb8 : bv 32 := 0x00084517.
Lemma F_33eb8 : fetch_word Ubsan.M.loaded_segments (0x34238 : word) = Some W_33eb8.
Proof. vm_refl. Qed.
Lemma D_33eb8 : decode_any W_33eb8 = Some (Auipc 10 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ebc : bv 32 := 0xfe050513.
Lemma F_33ebc : fetch_word Ubsan.M.loaded_segments (0x3423c : word) = Some W_33ebc.
Proof. vm_refl. Qed.
Lemma D_33ebc : decode_any W_33ebc = Some (OpImm ALU_ADD 10 10 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ec0 : bv 32 := 0x00053503.
Lemma F_33ec0 : fetch_word Ubsan.M.loaded_segments (0x34240 : word) = Some W_33ec0.
Proof. vm_refl. Qed.
Lemma D_33ec0 : decode_any W_33ec0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ec4 : bv 32 := 0x1c9660ef.
Lemma F_33ec4 : fetch_word Ubsan.M.loaded_segments (0x34244 : word) = Some W_33ec4.
Proof. vm_refl. Qed.
Lemma D_33ec4 : decode_any W_33ec4 = Some (Jal 1 420296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ec8 : bv 32 := 0x0040006f.
Lemma F_33ec8 : fetch_word Ubsan.M.loaded_segments (0x34248 : word) = Some W_33ec8.
Proof. vm_refl. Qed.
Lemma D_33ec8 : decode_any W_33ec8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ecc : bv 32 := 0x00083517.
Lemma F_33ecc : fetch_word Ubsan.M.loaded_segments (0x3424c : word) = Some W_33ecc.
Proof. vm_refl. Qed.
Lemma D_33ecc : decode_any W_33ecc = Some (Auipc 10 131, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ed0 : bv 32 := 0xe3c53503.
Lemma F_33ed0 : fetch_word Ubsan.M.loaded_segments (0x34250 : word) = Some W_33ed0.
Proof. vm_refl. Qed.
Lemma D_33ed0 : decode_any W_33ed0 = Some (Load SZ8 true 10 10 3644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ed4 : bv 32 := 0x00050c63.
Lemma F_33ed4 : fetch_word Ubsan.M.loaded_segments (0x34254 : word) = Some W_33ed4.
Proof. vm_refl. Qed.
Lemma D_33ed4 : decode_any W_33ed4 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ed8 : bv 32 := 0x0040006f.
Lemma F_33ed8 : fetch_word Ubsan.M.loaded_segments (0x34258 : word) = Some W_33ed8.
Proof. vm_refl. Qed.
Lemma D_33ed8 : decode_any W_33ed8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33edc : bv 32 := 0xffff1517.
Lemma F_33edc : fetch_word Ubsan.M.loaded_segments (0x3425c : word) = Some W_33edc.
Proof. vm_refl. Qed.
Lemma D_33edc : decode_any W_33edc = Some (Auipc 10 1048561, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ee0 : bv 32 := 0x43450513.
Lemma F_33ee0 : fetch_word Ubsan.M.loaded_segments (0x34260 : word) = Some W_33ee0.
Proof. vm_refl. Qed.
Lemma D_33ee0 : decode_any W_33ee0 = Some (OpImm ALU_ADD 10 10 1076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ee4 : bv 32 := 0x000000ef.
Lemma F_33ee4 : fetch_word Ubsan.M.loaded_segments (0x34264 : word) = Some W_33ee4.
Proof. vm_refl. Qed.
Lemma D_33ee4 : decode_any W_33ee4 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ee8 : bv 32 := 0x0040006f.
Lemma F_33ee8 : fetch_word Ubsan.M.loaded_segments (0x34268 : word) = Some W_33ee8.
Proof. vm_refl. Qed.
Lemma D_33ee8 : decode_any W_33ee8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33eec : bv 32 := 0x00813083.
Lemma F_33eec : fetch_word Ubsan.M.loaded_segments (0x3426c : word) = Some W_33eec.
Proof. vm_refl. Qed.
Lemma D_33eec : decode_any W_33eec = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ef0 : bv 32 := 0x00013403.
Lemma F_33ef0 : fetch_word Ubsan.M.loaded_segments (0x34270 : word) = Some W_33ef0.
Proof. vm_refl. Qed.
Lemma D_33ef0 : decode_any W_33ef0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ef4 : bv 32 := 0x01010113.
Lemma F_33ef4 : fetch_word Ubsan.M.loaded_segments (0x34274 : word) = Some W_33ef4.
Proof. vm_refl. Qed.
Lemma D_33ef4 : decode_any W_33ef4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ef8 : bv 32 := 0x00008067.
Lemma F_33ef8 : fetch_word Ubsan.M.loaded_segments (0x34278 : word) = Some W_33ef8.
Proof. vm_refl. Qed.
Lemma D_33ef8 : decode_any W_33ef8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
