(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_957b4 : bv 32 := 0xfe010113.
Lemma F_957b4 : fetch_word AsanUbsan.M.loaded_segments (0x95bcc : word) = Some W_957b4.
Proof. vm_refl. Qed.
Lemma D_957b4 : decode_any W_957b4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957b8 : bv 32 := 0x00113c23.
Lemma F_957b8 : fetch_word AsanUbsan.M.loaded_segments (0x95bd0 : word) = Some W_957b8.
Proof. vm_refl. Qed.
Lemma D_957b8 : decode_any W_957b8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957bc : bv 32 := 0x00813823.
Lemma F_957bc : fetch_word AsanUbsan.M.loaded_segments (0x95bd4 : word) = Some W_957bc.
Proof. vm_refl. Qed.
Lemma D_957bc : decode_any W_957bc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957c0 : bv 32 := 0x00913423.
Lemma F_957c0 : fetch_word AsanUbsan.M.loaded_segments (0x95bd8 : word) = Some W_957c0.
Proof. vm_refl. Qed.
Lemma D_957c0 : decode_any W_957c0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957c4 : bv 32 := 0x01213023.
Lemma F_957c4 : fetch_word AsanUbsan.M.loaded_segments (0x95bdc : word) = Some W_957c4.
Proof. vm_refl. Qed.
Lemma D_957c4 : decode_any W_957c4 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957c8 : bv 32 := 0x00060413.
Lemma F_957c8 : fetch_word AsanUbsan.M.loaded_segments (0x95be0 : word) = Some W_957c8.
Proof. vm_refl. Qed.
Lemma D_957c8 : decode_any W_957c8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957cc : bv 32 := 0x00058493.
Lemma F_957cc : fetch_word AsanUbsan.M.loaded_segments (0x95be4 : word) = Some W_957cc.
Proof. vm_refl. Qed.
Lemma D_957cc : decode_any W_957cc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957d0 : bv 32 := 0x00058513.
Lemma F_957d0 : fetch_word AsanUbsan.M.loaded_segments (0x95be8 : word) = Some W_957d0.
Proof. vm_refl. Qed.
Lemma D_957d0 : decode_any W_957d0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957d4 : bv 32 := 0x00060593.
Lemma F_957d4 : fetch_word AsanUbsan.M.loaded_segments (0x95bec : word) = Some W_957d4.
Proof. vm_refl. Qed.
Lemma D_957d4 : decode_any W_957d4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957d8 : bv 32 := 0x00068613.
Lemma F_957d8 : fetch_word AsanUbsan.M.loaded_segments (0x95bf0 : word) = Some W_957d8.
Proof. vm_refl. Qed.
Lemma D_957d8 : decode_any W_957d8 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957dc : bv 32 := 0xf19f70ef.
Lemma F_957dc : fetch_word AsanUbsan.M.loaded_segments (0x95bf4 : word) = Some W_957dc.
Proof. vm_refl. Qed.
Lemma D_957dc : decode_any W_957dc = Some (Jal 1 2064152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957e0 : bv 32 := 0x00050e63.
Lemma F_957e0 : fetch_word AsanUbsan.M.loaded_segments (0x95bf8 : word) = Some W_957e0.
Proof. vm_refl. Qed.
Lemma D_957e0 : decode_any W_957e0 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957e4 : bv 32 := 0x01813083.
Lemma F_957e4 : fetch_word AsanUbsan.M.loaded_segments (0x95bfc : word) = Some W_957e4.
Proof. vm_refl. Qed.
Lemma D_957e4 : decode_any W_957e4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957e8 : bv 32 := 0x01013403.
Lemma F_957e8 : fetch_word AsanUbsan.M.loaded_segments (0x95c00 : word) = Some W_957e8.
Proof. vm_refl. Qed.
Lemma D_957e8 : decode_any W_957e8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957ec : bv 32 := 0x00813483.
Lemma F_957ec : fetch_word AsanUbsan.M.loaded_segments (0x95c04 : word) = Some W_957ec.
Proof. vm_refl. Qed.
Lemma D_957ec : decode_any W_957ec = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957f0 : bv 32 := 0x00013903.
Lemma F_957f0 : fetch_word AsanUbsan.M.loaded_segments (0x95c08 : word) = Some W_957f0.
Proof. vm_refl. Qed.
Lemma D_957f0 : decode_any W_957f0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957f4 : bv 32 := 0x02010113.
Lemma F_957f4 : fetch_word AsanUbsan.M.loaded_segments (0x95c0c : word) = Some W_957f4.
Proof. vm_refl. Qed.
Lemma D_957f4 : decode_any W_957f4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957f8 : bv 32 := 0x00008067.
Lemma F_957f8 : fetch_word AsanUbsan.M.loaded_segments (0x95c10 : word) = Some W_957f8.
Proof. vm_refl. Qed.
Lemma D_957f8 : decode_any W_957f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957fc : bv 32 := 0x00050913.
Lemma F_957fc : fetch_word AsanUbsan.M.loaded_segments (0x95c14 : word) = Some W_957fc.
Proof. vm_refl. Qed.
Lemma D_957fc : decode_any W_957fc = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95800 : bv 32 := 0x00048513.
Lemma F_95800 : fetch_word AsanUbsan.M.loaded_segments (0x95c18 : word) = Some W_95800.
Proof. vm_refl. Qed.
Lemma D_95800 : decode_any W_95800 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95804 : bv 32 := 0x00040593.
Lemma F_95804 : fetch_word AsanUbsan.M.loaded_segments (0x95c1c : word) = Some W_95804.
Proof. vm_refl. Qed.
Lemma D_95804 : decode_any W_95804 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95808 : bv 32 := 0x020000ef.
Lemma F_95808 : fetch_word AsanUbsan.M.loaded_segments (0x95c20 : word) = Some W_95808.
Proof. vm_refl. Qed.
Lemma D_95808 : decode_any W_95808 = Some (Jal 1 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9580c : bv 32 := 0x00090513.
Lemma F_9580c : fetch_word AsanUbsan.M.loaded_segments (0x95c24 : word) = Some W_9580c.
Proof. vm_refl. Qed.
Lemma D_9580c : decode_any W_9580c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95810 : bv 32 := 0x01813083.
Lemma F_95810 : fetch_word AsanUbsan.M.loaded_segments (0x95c28 : word) = Some W_95810.
Proof. vm_refl. Qed.
Lemma D_95810 : decode_any W_95810 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95814 : bv 32 := 0x01013403.
Lemma F_95814 : fetch_word AsanUbsan.M.loaded_segments (0x95c2c : word) = Some W_95814.
Proof. vm_refl. Qed.
Lemma D_95814 : decode_any W_95814 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95818 : bv 32 := 0x00813483.
Lemma F_95818 : fetch_word AsanUbsan.M.loaded_segments (0x95c30 : word) = Some W_95818.
Proof. vm_refl. Qed.
Lemma D_95818 : decode_any W_95818 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9581c : bv 32 := 0x00013903.
Lemma F_9581c : fetch_word AsanUbsan.M.loaded_segments (0x95c34 : word) = Some W_9581c.
Proof. vm_refl. Qed.
Lemma D_9581c : decode_any W_9581c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95820 : bv 32 := 0x02010113.
Lemma F_95820 : fetch_word AsanUbsan.M.loaded_segments (0x95c38 : word) = Some W_95820.
Proof. vm_refl. Qed.
Lemma D_95820 : decode_any W_95820 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95824 : bv 32 := 0x00008067.
Lemma F_95824 : fetch_word AsanUbsan.M.loaded_segments (0x95c3c : word) = Some W_95824.
Proof. vm_refl. Qed.
Lemma D_95824 : decode_any W_95824 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
