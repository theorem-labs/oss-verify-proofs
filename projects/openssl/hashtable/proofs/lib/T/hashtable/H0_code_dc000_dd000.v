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
Definition W_dcef8 : bv 32 := 0xfff34197.
Lemma F_dcef8 : fetch_word Plain.M.loaded_segments (0xdcf48 : word) = Some W_dcef8.
Proof. vm_refl. Qed.
Lemma D_dcef8 : decode_any W_dcef8 = Some (Auipc 3 1048372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcefc : bv 32 := 0x8b818193.
Lemma F_dcefc : fetch_word Plain.M.loaded_segments (0xdcf4c : word) = Some W_dcefc.
Proof. vm_refl. Qed.
Lemma D_dcefc : decode_any W_dcefc = Some (OpImm ALU_ADD 3 3 2232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf00 : bv 32 := 0x00010513.
Lemma F_dcf00 : fetch_word Plain.M.loaded_segments (0xdcf50 : word) = Some W_dcf00.
Proof. vm_refl. Qed.
Lemma D_dcf00 : decode_any W_dcf00 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf04 : bv 32 := 0xfff23597.
Lemma F_dcf04 : fetch_word Plain.M.loaded_segments (0xdcf54 : word) = Some W_dcf04.
Proof. vm_refl. Qed.
Lemma D_dcf04 : decode_any W_dcf04 = Some (Auipc 11 1048355, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf08 : bv 32 := 0x0ac58593.
Lemma F_dcf08 : fetch_word Plain.M.loaded_segments (0xdcf58 : word) = Some W_dcf08.
Proof. vm_refl. Qed.
Lemma D_dcf08 : decode_any W_dcf08 = Some (OpImm ALU_ADD 11 11 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf0c : bv 32 := 0xff017113.
Lemma F_dcf0c : fetch_word Plain.M.loaded_segments (0xdcf5c : word) = Some W_dcf0c.
Proof. vm_refl. Qed.
Lemma D_dcf0c : decode_any W_dcf0c = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf10 : bv 32 := 0x0040006f.
Lemma F_dcf10 : fetch_word Plain.M.loaded_segments (0xdcf60 : word) = Some W_dcf10.
Proof. vm_refl. Qed.
Lemma D_dcf10 : decode_any W_dcf10 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf14 : bv 32 := 0x00052583.
Lemma F_dcf14 : fetch_word Plain.M.loaded_segments (0xdcf64 : word) = Some W_dcf14.
Proof. vm_refl. Qed.
Lemma D_dcf14 : decode_any W_dcf14 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf18 : bv 32 := 0x001fa617.
Lemma F_dcf18 : fetch_word Plain.M.loaded_segments (0xdcf68 : word) = Some W_dcf18.
Proof. vm_refl. Qed.
Lemma D_dcf18 : decode_any W_dcf18 = Some (Auipc 12 506, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf1c : bv 32 := 0x001fa697.
Lemma F_dcf1c : fetch_word Plain.M.loaded_segments (0xdcf6c : word) = Some W_dcf1c.
Proof. vm_refl. Qed.
Lemma D_dcf1c : decode_any W_dcf1c = Some (Auipc 13 506, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf20 : bv 32 := 0x001fa717.
Lemma F_dcf20 : fetch_word Plain.M.loaded_segments (0xdcf70 : word) = Some W_dcf20.
Proof. vm_refl. Qed.
Lemma D_dcf20 : decode_any W_dcf20 = Some (Auipc 14 506, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf24 : bv 32 := 0x66063783.
Lemma F_dcf24 : fetch_word Plain.M.loaded_segments (0xdcf74 : word) = Some W_dcf24.
Proof. vm_refl. Qed.
Lemma D_dcf24 : decode_any W_dcf24 = Some (Load SZ8 true 15 12 1632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf28 : bv 32 := 0x6646b683.
Lemma F_dcf28 : fetch_word Plain.M.loaded_segments (0xdcf78 : word) = Some W_dcf28.
Proof. vm_refl. Qed.
Lemma D_dcf28 : decode_any W_dcf28 = Some (Load SZ8 true 13 13 1636, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf2c : bv 32 := 0x66873703.
Lemma F_dcf2c : fetch_word Plain.M.loaded_segments (0xdcf7c : word) = Some W_dcf2c.
Proof. vm_refl. Qed.
Lemma D_dcf2c : decode_any W_dcf2c = Some (Load SZ8 true 14 14 1640, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf30 : bv 32 := 0x00850613.
Lemma F_dcf30 : fetch_word Plain.M.loaded_segments (0xdcf80 : word) = Some W_dcf30.
Proof. vm_refl. Qed.
Lemma D_dcf30 : decode_any W_dcf30 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf34 : bv 32 := 0x00078513.
Lemma F_dcf34 : fetch_word Plain.M.loaded_segments (0xdcf84 : word) = Some W_dcf34.
Proof. vm_refl. Qed.
Lemma D_dcf34 : decode_any W_dcf34 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf38 : bv 32 := 0x00000793.
Lemma F_dcf38 : fetch_word Plain.M.loaded_segments (0xdcf88 : word) = Some W_dcf38.
Proof. vm_refl. Qed.
Lemma D_dcf38 : decode_any W_dcf38 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf3c : bv 32 := 0x0018e317.
Lemma F_dcf3c : fetch_word Plain.M.loaded_segments (0xdcf8c : word) = Some W_dcf3c.
Proof. vm_refl. Qed.
Lemma D_dcf3c : decode_any W_dcf3c = Some (Auipc 6 398, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf40 : bv 32 := 0x58030067.
Lemma F_dcf40 : fetch_word Plain.M.loaded_segments (0xdcf90 : word) = Some W_dcf40.
Proof. vm_refl. Qed.
Lemma D_dcf40 : decode_any W_dcf40 = Some (Jalr 0 6 1408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf44 : bv 32 := 0xff010113.
Lemma F_dcf44 : fetch_word Plain.M.loaded_segments (0xdcf94 : word) = Some W_dcf44.
Proof. vm_refl. Qed.
Lemma D_dcf44 : decode_any W_dcf44 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf48 : bv 32 := 0x00113423.
Lemma F_dcf48 : fetch_word Plain.M.loaded_segments (0xdcf98 : word) = Some W_dcf48.
Proof. vm_refl. Qed.
Lemma D_dcf48 : decode_any W_dcf48 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf4c : bv 32 := 0x00813023.
Lemma F_dcf4c : fetch_word Plain.M.loaded_segments (0xdcf9c : word) = Some W_dcf4c.
Proof. vm_refl. Qed.
Lemma D_dcf4c : decode_any W_dcf4c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf50 : bv 32 := 0x01010413.
Lemma F_dcf50 : fetch_word Plain.M.loaded_segments (0xdcfa0 : word) = Some W_dcf50.
Proof. vm_refl. Qed.
Lemma D_dcf50 : decode_any W_dcf50 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf54 : bv 32 := 0x001fc517.
Lemma F_dcf54 : fetch_word Plain.M.loaded_segments (0xdcfa4 : word) = Some W_dcf54.
Proof. vm_refl. Qed.
Lemma D_dcf54 : decode_any W_dcf54 = Some (Auipc 10 508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf58 : bv 32 := 0x38c50513.
Lemma F_dcf58 : fetch_word Plain.M.loaded_segments (0xdcfa8 : word) = Some W_dcf58.
Proof. vm_refl. Qed.
Lemma D_dcf58 : decode_any W_dcf58 = Some (OpImm ALU_ADD 10 10 908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf5c : bv 32 := 0x00054503.
Lemma F_dcf5c : fetch_word Plain.M.loaded_segments (0xdcfac : word) = Some W_dcf5c.
Proof. vm_refl. Qed.
Lemma D_dcf5c : decode_any W_dcf5c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf60 : bv 32 := 0x00157513.
Lemma F_dcf60 : fetch_word Plain.M.loaded_segments (0xdcfb0 : word) = Some W_dcf60.
Proof. vm_refl. Qed.
Lemma D_dcf60 : decode_any W_dcf60 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf64 : bv 32 := 0x00050663.
Lemma F_dcf64 : fetch_word Plain.M.loaded_segments (0xdcfb4 : word) = Some W_dcf64.
Proof. vm_refl. Qed.
Lemma D_dcf64 : decode_any W_dcf64 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf68 : bv 32 := 0x0040006f.
Lemma F_dcf68 : fetch_word Plain.M.loaded_segments (0xdcfb8 : word) = Some W_dcf68.
Proof. vm_refl. Qed.
Lemma D_dcf68 : decode_any W_dcf68 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf6c : bv 32 := 0x03c0006f.
Lemma F_dcf6c : fetch_word Plain.M.loaded_segments (0xdcfbc : word) = Some W_dcf6c.
Proof. vm_refl. Qed.
Lemma D_dcf6c : decode_any W_dcf6c = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf70 : bv 32 := 0x001fc517.
Lemma F_dcf70 : fetch_word Plain.M.loaded_segments (0xdcfc0 : word) = Some W_dcf70.
Proof. vm_refl. Qed.
Lemma D_dcf70 : decode_any W_dcf70 = Some (Auipc 10 508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf74 : bv 32 := 0x37050593.
Lemma F_dcf74 : fetch_word Plain.M.loaded_segments (0xdcfc4 : word) = Some W_dcf74.
Proof. vm_refl. Qed.
Lemma D_dcf74 : decode_any W_dcf74 = Some (OpImm ALU_ADD 11 10 880, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf78 : bv 32 := 0x00100513.
Lemma F_dcf78 : fetch_word Plain.M.loaded_segments (0xdcfc8 : word) = Some W_dcf78.
Proof. vm_refl. Qed.
Lemma D_dcf78 : decode_any W_dcf78 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf7c : bv 32 := 0x00a58023.
Lemma F_dcf7c : fetch_word Plain.M.loaded_segments (0xdcfcc : word) = Some W_dcf7c.
Proof. vm_refl. Qed.
Lemma D_dcf7c : decode_any W_dcf7c = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf80 : bv 32 := 0x001fa517.
Lemma F_dcf80 : fetch_word Plain.M.loaded_segments (0xdcfd0 : word) = Some W_dcf80.
Proof. vm_refl. Qed.
Lemma D_dcf80 : decode_any W_dcf80 = Some (Auipc 10 506, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf84 : bv 32 := 0x61053503.
Lemma F_dcf84 : fetch_word Plain.M.loaded_segments (0xdcfd4 : word) = Some W_dcf84.
Proof. vm_refl. Qed.
Lemma D_dcf84 : decode_any W_dcf84 = Some (Load SZ8 true 10 10 1552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf88 : bv 32 := 0x02050063.
Lemma F_dcf88 : fetch_word Plain.M.loaded_segments (0xdcfd8 : word) = Some W_dcf88.
Proof. vm_refl. Qed.
Lemma D_dcf88 : decode_any W_dcf88 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf8c : bv 32 := 0x0040006f.
Lemma F_dcf8c : fetch_word Plain.M.loaded_segments (0xdcfdc : word) = Some W_dcf8c.
Proof. vm_refl. Qed.
Lemma D_dcf8c : decode_any W_dcf8c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf90 : bv 32 := 0xfffa4517.
Lemma F_dcf90 : fetch_word Plain.M.loaded_segments (0xdcfe0 : word) = Some W_dcf90.
Proof. vm_refl. Qed.
Lemma D_dcf90 : decode_any W_dcf90 = Some (Auipc 10 1048484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf94 : bv 32 := 0x4e050513.
Lemma F_dcf94 : fetch_word Plain.M.loaded_segments (0xdcfe4 : word) = Some W_dcf94.
Proof. vm_refl. Qed.
Lemma D_dcf94 : decode_any W_dcf94 = Some (OpImm ALU_ADD 10 10 1248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf98 : bv 32 := 0x001fc597.
Lemma F_dcf98 : fetch_word Plain.M.loaded_segments (0xdcfe8 : word) = Some W_dcf98.
Proof. vm_refl. Qed.
Lemma D_dcf98 : decode_any W_dcf98 = Some (Auipc 11 508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf9c : bv 32 := 0x35058593.
Lemma F_dcf9c : fetch_word Plain.M.loaded_segments (0xdcfec : word) = Some W_dcf9c.
Proof. vm_refl. Qed.
Lemma D_dcf9c : decode_any W_dcf9c = Some (OpImm ALU_ADD 11 11 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfa0 : bv 32 := 0x000000ef.
Lemma F_dcfa0 : fetch_word Plain.M.loaded_segments (0xdcff0 : word) = Some W_dcfa0.
Proof. vm_refl. Qed.
Lemma D_dcfa0 : decode_any W_dcfa0 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfa4 : bv 32 := 0x0040006f.
Lemma F_dcfa4 : fetch_word Plain.M.loaded_segments (0xdcff4 : word) = Some W_dcfa4.
Proof. vm_refl. Qed.
Lemma D_dcfa4 : decode_any W_dcfa4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfa8 : bv 32 := 0x00813083.
Lemma F_dcfa8 : fetch_word Plain.M.loaded_segments (0xdcff8 : word) = Some W_dcfa8.
Proof. vm_refl. Qed.
Lemma D_dcfa8 : decode_any W_dcfa8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfac : bv 32 := 0x00013403.
Lemma F_dcfac : fetch_word Plain.M.loaded_segments (0xdcffc : word) = Some W_dcfac.
Proof. vm_refl. Qed.
Lemma D_dcfac : decode_any W_dcfac = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfb0 : bv 32 := 0x01010113.
Lemma F_dcfb0 : fetch_word Plain.M.loaded_segments (0xdd000 : word) = Some W_dcfb0.
Proof. vm_refl. Qed.
Lemma D_dcfb0 : decode_any W_dcfb0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfb4 : bv 32 := 0x00008067.
Lemma F_dcfb4 : fetch_word Plain.M.loaded_segments (0xdd004 : word) = Some W_dcfb4.
Proof. vm_refl. Qed.
Lemma D_dcfb4 : decode_any W_dcfb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfb8 : bv 32 := 0xff010113.
Lemma F_dcfb8 : fetch_word Plain.M.loaded_segments (0xdd008 : word) = Some W_dcfb8.
Proof. vm_refl. Qed.
Lemma D_dcfb8 : decode_any W_dcfb8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfbc : bv 32 := 0x00113423.
Lemma F_dcfbc : fetch_word Plain.M.loaded_segments (0xdd00c : word) = Some W_dcfbc.
Proof. vm_refl. Qed.
Lemma D_dcfbc : decode_any W_dcfbc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfc0 : bv 32 := 0x00813023.
Lemma F_dcfc0 : fetch_word Plain.M.loaded_segments (0xdd010 : word) = Some W_dcfc0.
Proof. vm_refl. Qed.
Lemma D_dcfc0 : decode_any W_dcfc0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfc4 : bv 32 := 0x01010413.
Lemma F_dcfc4 : fetch_word Plain.M.loaded_segments (0xdd014 : word) = Some W_dcfc4.
Proof. vm_refl. Qed.
Lemma D_dcfc4 : decode_any W_dcfc4 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfc8 : bv 32 := 0x001fc517.
Lemma F_dcfc8 : fetch_word Plain.M.loaded_segments (0xdd018 : word) = Some W_dcfc8.
Proof. vm_refl. Qed.
Lemma D_dcfc8 : decode_any W_dcfc8 = Some (Auipc 10 508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfcc : bv 32 := 0x36050513.
Lemma F_dcfcc : fetch_word Plain.M.loaded_segments (0xdd01c : word) = Some W_dcfcc.
Proof. vm_refl. Qed.
Lemma D_dcfcc : decode_any W_dcfcc = Some (OpImm ALU_ADD 10 10 864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfd0 : bv 32 := 0x00054503.
Lemma F_dcfd0 : fetch_word Plain.M.loaded_segments (0xdd020 : word) = Some W_dcfd0.
Proof. vm_refl. Qed.
Lemma D_dcfd0 : decode_any W_dcfd0 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfd4 : bv 32 := 0x00157513.
Lemma F_dcfd4 : fetch_word Plain.M.loaded_segments (0xdd024 : word) = Some W_dcfd4.
Proof. vm_refl. Qed.
Lemma D_dcfd4 : decode_any W_dcfd4 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfd8 : bv 32 := 0x00050663.
Lemma F_dcfd8 : fetch_word Plain.M.loaded_segments (0xdd028 : word) = Some W_dcfd8.
Proof. vm_refl. Qed.
Lemma D_dcfd8 : decode_any W_dcfd8 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfdc : bv 32 := 0x0040006f.
Lemma F_dcfdc : fetch_word Plain.M.loaded_segments (0xdd02c : word) = Some W_dcfdc.
Proof. vm_refl. Qed.
Lemma D_dcfdc : decode_any W_dcfdc = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfe0 : bv 32 := 0x05c0006f.
Lemma F_dcfe0 : fetch_word Plain.M.loaded_segments (0xdd030 : word) = Some W_dcfe0.
Proof. vm_refl. Qed.
Lemma D_dcfe0 : decode_any W_dcfe0 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfe4 : bv 32 := 0x001fc517.
Lemma F_dcfe4 : fetch_word Plain.M.loaded_segments (0xdd034 : word) = Some W_dcfe4.
Proof. vm_refl. Qed.
Lemma D_dcfe4 : decode_any W_dcfe4 = Some (Auipc 10 508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfe8 : bv 32 := 0x34450593.
Lemma F_dcfe8 : fetch_word Plain.M.loaded_segments (0xdd038 : word) = Some W_dcfe8.
Proof. vm_refl. Qed.
Lemma D_dcfe8 : decode_any W_dcfe8 = Some (OpImm ALU_ADD 11 10 836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfec : bv 32 := 0x00100513.
Lemma F_dcfec : fetch_word Plain.M.loaded_segments (0xdd03c : word) = Some W_dcfec.
Proof. vm_refl. Qed.
Lemma D_dcfec : decode_any W_dcfec = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcff0 : bv 32 := 0x00a58023.
Lemma F_dcff0 : fetch_word Plain.M.loaded_segments (0xdd040 : word) = Some W_dcff0.
Proof. vm_refl. Qed.
Lemma D_dcff0 : decode_any W_dcff0 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcff4 : bv 32 := 0x001fa517.
Lemma F_dcff4 : fetch_word Plain.M.loaded_segments (0xdd044 : word) = Some W_dcff4.
Proof. vm_refl. Qed.
Lemma D_dcff4 : decode_any W_dcff4 = Some (Auipc 10 506, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcff8 : bv 32 := 0x5a453503.
Lemma F_dcff8 : fetch_word Plain.M.loaded_segments (0xdd048 : word) = Some W_dcff8.
Proof. vm_refl. Qed.
Lemma D_dcff8 : decode_any W_dcff8 = Some (Load SZ8 true 10 10 1444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcffc : bv 32 := 0x02050063.
Lemma F_dcffc : fetch_word Plain.M.loaded_segments (0xdd04c : word) = Some W_dcffc.
Proof. vm_refl. Qed.
Lemma D_dcffc : decode_any W_dcffc = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.
