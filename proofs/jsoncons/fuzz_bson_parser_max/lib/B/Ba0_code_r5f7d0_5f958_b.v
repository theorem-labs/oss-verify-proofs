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
Definition W_79108 : bv 32 := 0xfe010113.
Lemma F_79108 : fetch_word AsanUbsan.M.loaded_segments (0x79520 : word) = Some W_79108.
Proof. vm_refl. Qed.
Lemma D_79108 : decode_any W_79108 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7910c : bv 32 := 0x00113c23.
Lemma F_7910c : fetch_word AsanUbsan.M.loaded_segments (0x79524 : word) = Some W_7910c.
Proof. vm_refl. Qed.
Lemma D_7910c : decode_any W_7910c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79110 : bv 32 := 0x00813823.
Lemma F_79110 : fetch_word AsanUbsan.M.loaded_segments (0x79528 : word) = Some W_79110.
Proof. vm_refl. Qed.
Lemma D_79110 : decode_any W_79110 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79114 : bv 32 := 0x00913423.
Lemma F_79114 : fetch_word AsanUbsan.M.loaded_segments (0x7952c : word) = Some W_79114.
Proof. vm_refl. Qed.
Lemma D_79114 : decode_any W_79114 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79118 : bv 32 := 0x01213023.
Lemma F_79118 : fetch_word AsanUbsan.M.loaded_segments (0x79530 : word) = Some W_79118.
Proof. vm_refl. Qed.
Lemma D_79118 : decode_any W_79118 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7911c : bv 32 := 0x00058413.
Lemma F_7911c : fetch_word AsanUbsan.M.loaded_segments (0x79534 : word) = Some W_7911c.
Proof. vm_refl. Qed.
Lemma D_7911c : decode_any W_7911c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79120 : bv 32 := 0x00050493.
Lemma F_79120 : fetch_word AsanUbsan.M.loaded_segments (0x79538 : word) = Some W_79120.
Proof. vm_refl. Qed.
Lemma D_79120 : decode_any W_79120 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79124 : bv 32 := 0x030000ef.
Lemma F_79124 : fetch_word AsanUbsan.M.loaded_segments (0x7953c : word) = Some W_79124.
Proof. vm_refl. Qed.
Lemma D_79124 : decode_any W_79124 = Some (Jal 1 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79128 : bv 32 := 0x00050913.
Lemma F_79128 : fetch_word AsanUbsan.M.loaded_segments (0x79540 : word) = Some W_79128.
Proof. vm_refl. Qed.
Lemma D_79128 : decode_any W_79128 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7912c : bv 32 := 0x00940533.
Lemma F_7912c : fetch_word AsanUbsan.M.loaded_segments (0x79544 : word) = Some W_7912c.
Proof. vm_refl. Qed.
Lemma D_7912c : decode_any W_7912c = Some (Op ALU_ADD 10 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79130 : bv 32 := 0x024000ef.
Lemma F_79130 : fetch_word AsanUbsan.M.loaded_segments (0x79548 : word) = Some W_79130.
Proof. vm_refl. Qed.
Lemma D_79130 : decode_any W_79130 = Some (Jal 1 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79134 : bv 32 := 0x00050593.
Lemma F_79134 : fetch_word AsanUbsan.M.loaded_segments (0x7954c : word) = Some W_79134.
Proof. vm_refl. Qed.
Lemma D_79134 : decode_any W_79134 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79138 : bv 32 := 0x00090513.
Lemma F_79138 : fetch_word AsanUbsan.M.loaded_segments (0x79550 : word) = Some W_79138.
Proof. vm_refl. Qed.
Lemma D_79138 : decode_any W_79138 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7913c : bv 32 := 0x01813083.
Lemma F_7913c : fetch_word AsanUbsan.M.loaded_segments (0x79554 : word) = Some W_7913c.
Proof. vm_refl. Qed.
Lemma D_7913c : decode_any W_7913c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79140 : bv 32 := 0x01013403.
Lemma F_79140 : fetch_word AsanUbsan.M.loaded_segments (0x79558 : word) = Some W_79140.
Proof. vm_refl. Qed.
Lemma D_79140 : decode_any W_79140 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79144 : bv 32 := 0x00813483.
Lemma F_79144 : fetch_word AsanUbsan.M.loaded_segments (0x7955c : word) = Some W_79144.
Proof. vm_refl. Qed.
Lemma D_79144 : decode_any W_79144 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79148 : bv 32 := 0x00013903.
Lemma F_79148 : fetch_word AsanUbsan.M.loaded_segments (0x79560 : word) = Some W_79148.
Proof. vm_refl. Qed.
Lemma D_79148 : decode_any W_79148 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7914c : bv 32 := 0x02010113.
Lemma F_7914c : fetch_word AsanUbsan.M.loaded_segments (0x79564 : word) = Some W_7914c.
Proof. vm_refl. Qed.
Lemma D_7914c : decode_any W_7914c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79150 : bv 32 := 0x3151b06f.
Lemma F_79150 : fetch_word AsanUbsan.M.loaded_segments (0x79568 : word) = Some W_79150.
Proof. vm_refl. Qed.
Lemma D_79150 : decode_any W_79150 = Some (Jal 0 113428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79154 : bv 32 := 0x000be597.
Lemma F_79154 : fetch_word AsanUbsan.M.loaded_segments (0x7956c : word) = Some W_79154.
Proof. vm_refl. Qed.
Lemma D_79154 : decode_any W_79154 = Some (Auipc 11 190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79158 : bv 32 := 0xf545b583.
Lemma F_79158 : fetch_word AsanUbsan.M.loaded_segments (0x79570 : word) = Some W_79158.
Proof. vm_refl. Qed.
Lemma D_79158 : decode_any W_79158 = Some (Load SZ8 true 11 11 3924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7915c : bv 32 := 0x0005b583.
Lemma F_7915c : fetch_word AsanUbsan.M.loaded_segments (0x79574 : word) = Some W_7915c.
Proof. vm_refl. Qed.
Lemma D_7915c : decode_any W_7915c = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79160 : bv 32 := 0xfff58613.
Lemma F_79160 : fetch_word AsanUbsan.M.loaded_segments (0x79578 : word) = Some W_79160.
Proof. vm_refl. Qed.
Lemma D_79160 : decode_any W_79160 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79164 : bv 32 := 0x00c5b6b3.
Lemma F_79164 : fetch_word AsanUbsan.M.loaded_segments (0x7957c : word) = Some W_79164.
Proof. vm_refl. Qed.
Lemma D_79164 : decode_any W_79164 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79168 : bv 32 := 0xfff68693.
Lemma F_79168 : fetch_word AsanUbsan.M.loaded_segments (0x79580 : word) = Some W_79168.
Proof. vm_refl. Qed.
Lemma D_79168 : decode_any W_79168 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7916c : bv 32 := 0x00c6f6b3.
Lemma F_7916c : fetch_word AsanUbsan.M.loaded_segments (0x79584 : word) = Some W_7916c.
Proof. vm_refl. Qed.
Lemma D_7916c : decode_any W_7916c = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79170 : bv 32 := 0x04a6f263.
Lemma F_79170 : fetch_word AsanUbsan.M.loaded_segments (0x79588 : word) = Some W_79170.
Proof. vm_refl. Qed.
Lemma D_79170 : decode_any W_79170 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79174 : bv 32 := 0x000be697.
Lemma F_79174 : fetch_word AsanUbsan.M.loaded_segments (0x7958c : word) = Some W_79174.
Proof. vm_refl. Qed.
Lemma D_79174 : decode_any W_79174 = Some (Auipc 13 190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79178 : bv 32 := 0xf3c6b683.
Lemma F_79178 : fetch_word AsanUbsan.M.loaded_segments (0x79590 : word) = Some W_79178.
Proof. vm_refl. Qed.
Lemma D_79178 : decode_any W_79178 = Some (Load SZ8 true 13 13 3900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7917c : bv 32 := 0x000be717.
Lemma F_7917c : fetch_word AsanUbsan.M.loaded_segments (0x79594 : word) = Some W_7917c.
Proof. vm_refl. Qed.
Lemma D_7917c : decode_any W_7917c = Some (Auipc 14 190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79180 : bv 32 := 0xf3c73703.
Lemma F_79180 : fetch_word AsanUbsan.M.loaded_segments (0x79598 : word) = Some W_79180.
Proof. vm_refl. Qed.
Lemma D_79180 : decode_any W_79180 = Some (Load SZ8 true 14 14 3900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79184 : bv 32 := 0x0006b803.
Lemma F_79184 : fetch_word AsanUbsan.M.loaded_segments (0x7959c : word) = Some W_79184.
Proof. vm_refl. Qed.
Lemma D_79184 : decode_any W_79184 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79188 : bv 32 := 0x00073683.
Lemma F_79188 : fetch_word AsanUbsan.M.loaded_segments (0x795a0 : word) = Some W_79188.
Proof. vm_refl. Qed.
Lemma D_79188 : decode_any W_79188 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7918c : bv 32 := 0xfff80793.
Lemma F_7918c : fetch_word AsanUbsan.M.loaded_segments (0x795a4 : word) = Some W_7918c.
Proof. vm_refl. Qed.
Lemma D_7918c : decode_any W_7918c = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79190 : bv 32 := 0x00a7f463.
Lemma F_79190 : fetch_word AsanUbsan.M.loaded_segments (0x795a8 : word) = Some W_79190.
Proof. vm_refl. Qed.
Lemma D_79190 : decode_any W_79190 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79198 : bv 32 := 0x000be717.
Lemma F_79198 : fetch_word AsanUbsan.M.loaded_segments (0x795b0 : word) = Some W_79198.
Proof. vm_refl. Qed.
Lemma D_79198 : decode_any W_79198 = Some (Auipc 14 190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7919c : bv 32 := 0xf2873703.
Lemma F_7919c : fetch_word AsanUbsan.M.loaded_segments (0x795b4 : word) = Some W_7919c.
Proof. vm_refl. Qed.
Lemma D_7919c : decode_any W_7919c = Some (Load SZ8 true 14 14 3880, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791a0 : bv 32 := 0x00073283.
Lemma F_791a0 : fetch_word AsanUbsan.M.loaded_segments (0x795b8 : word) = Some W_791a0.
Proof. vm_refl. Qed.
Lemma D_791a0 : decode_any W_791a0 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791a4 : bv 32 := 0x0032d713.
Lemma F_791a4 : fetch_word AsanUbsan.M.loaded_segments (0x795bc : word) = Some W_791a4.
Proof. vm_refl. Qed.
Lemma D_791a4 : decode_any W_791a4 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791a8 : bv 32 := 0x00b708b3.
Lemma F_791a8 : fetch_word AsanUbsan.M.loaded_segments (0x795c0 : word) = Some W_791a8.
Proof. vm_refl. Qed.
Lemma D_791a8 : decode_any W_791a8 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791ac : bv 32 := 0x00a2ea63.
Lemma F_791ac : fetch_word AsanUbsan.M.loaded_segments (0x795c4 : word) = Some W_791ac.
Proof. vm_refl. Qed.
Lemma D_791ac : decode_any W_791ac = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791b0 : bv 32 := 0x00a8f863.
Lemma F_791b0 : fetch_word AsanUbsan.M.loaded_segments (0x795c8 : word) = Some W_791b0.
Proof. vm_refl. Qed.
Lemma D_791b0 : decode_any W_791b0 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791b4 : bv 32 := 0x00355513.
Lemma F_791b4 : fetch_word AsanUbsan.M.loaded_segments (0x795cc : word) = Some W_791b4.
Proof. vm_refl. Qed.
Lemma D_791b4 : decode_any W_791b4 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791b8 : bv 32 := 0x00a58533.
Lemma F_791b8 : fetch_word AsanUbsan.M.loaded_segments (0x795d0 : word) = Some W_791b8.
Proof. vm_refl. Qed.
Lemma D_791b8 : decode_any W_791b8 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791bc : bv 32 := 0x00008067.
Lemma F_791bc : fetch_word AsanUbsan.M.loaded_segments (0x795d4 : word) = Some W_791bc.
Proof. vm_refl. Qed.
Lemma D_791bc : decode_any W_791bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
