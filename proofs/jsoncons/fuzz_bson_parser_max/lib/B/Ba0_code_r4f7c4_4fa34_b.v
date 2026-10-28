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
Definition W_65154 : bv 32 := 0x81010113.
Lemma F_65154 : fetch_word AsanUbsan.M.loaded_segments (0x6556c : word) = Some W_65154.
Proof. vm_refl. Qed.
Lemma D_65154 : decode_any W_65154 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65158 : bv 32 := 0x7e113423.
Lemma F_65158 : fetch_word AsanUbsan.M.loaded_segments (0x65570 : word) = Some W_65158.
Proof. vm_refl. Qed.
Lemma D_65158 : decode_any W_65158 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6515c : bv 32 := 0x7e813023.
Lemma F_6515c : fetch_word AsanUbsan.M.loaded_segments (0x65574 : word) = Some W_6515c.
Proof. vm_refl. Qed.
Lemma D_6515c : decode_any W_6515c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65160 : bv 32 := 0x7c913c23.
Lemma F_65160 : fetch_word AsanUbsan.M.loaded_segments (0x65578 : word) = Some W_65160.
Proof. vm_refl. Qed.
Lemma D_65160 : decode_any W_65160 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65164 : bv 32 := 0x7d213823.
Lemma F_65164 : fetch_word AsanUbsan.M.loaded_segments (0x6557c : word) = Some W_65164.
Proof. vm_refl. Qed.
Lemma D_65164 : decode_any W_65164 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65168 : bv 32 := 0x7d313423.
Lemma F_65168 : fetch_word AsanUbsan.M.loaded_segments (0x65580 : word) = Some W_65168.
Proof. vm_refl. Qed.
Lemma D_65168 : decode_any W_65168 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6516c : bv 32 := 0x7d413023.
Lemma F_6516c : fetch_word AsanUbsan.M.loaded_segments (0x65584 : word) = Some W_6516c.
Proof. vm_refl. Qed.
Lemma D_6516c : decode_any W_6516c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65170 : bv 32 := 0x7f010413.
Lemma F_65170 : fetch_word AsanUbsan.M.loaded_segments (0x65588 : word) = Some W_65170.
Proof. vm_refl. Qed.
Lemma D_65170 : decode_any W_65170 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65174 : bv 32 := 0xfa010113.
Lemma F_65174 : fetch_word AsanUbsan.M.loaded_segments (0x6558c : word) = Some W_65174.
Proof. vm_refl. Qed.
Lemma D_65174 : decode_any W_65174 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65178 : bv 32 := 0x00060913.
Lemma F_65178 : fetch_word AsanUbsan.M.loaded_segments (0x65590 : word) = Some W_65178.
Proof. vm_refl. Qed.
Lemma D_65178 : decode_any W_65178 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6517c : bv 32 := 0x00058493.
Lemma F_6517c : fetch_word AsanUbsan.M.loaded_segments (0x65594 : word) = Some W_6517c.
Proof. vm_refl. Qed.
Lemma D_6517c : decode_any W_6517c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65180 : bv 32 := 0x00050993.
Lemma F_65180 : fetch_word AsanUbsan.M.loaded_segments (0x65598 : word) = Some W_65180.
Proof. vm_refl. Qed.
Lemma D_65180 : decode_any W_65180 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65184 : bv 32 := 0x3491b0ef.
Lemma F_65184 : fetch_word AsanUbsan.M.loaded_segments (0x6559c : word) = Some W_65184.
Proof. vm_refl. Qed.
Lemma D_65184 : decode_any W_65184 = Some (Jal 1 113480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65188 : bv 32 := 0x000d4597.
Lemma F_65188 : fetch_word AsanUbsan.M.loaded_segments (0x655a0 : word) = Some W_65188.
Proof. vm_refl. Qed.
Lemma D_65188 : decode_any W_65188 = Some (Auipc 11 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6518c : bv 32 := 0xd785b683.
Lemma F_6518c : fetch_word AsanUbsan.M.loaded_segments (0x655a4 : word) = Some W_6518c.
Proof. vm_refl. Qed.
Lemma D_6518c : decode_any W_6518c = Some (Load SZ8 true 13 11 3448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65190 : bv 32 := 0x00050a13.
Lemma F_65190 : fetch_word AsanUbsan.M.loaded_segments (0x655a8 : word) = Some W_65190.
Proof. vm_refl. Qed.
Lemma D_65190 : decode_any W_65190 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65194 : bv 32 := 0x00098513.
Lemma F_65194 : fetch_word AsanUbsan.M.loaded_segments (0x655ac : word) = Some W_65194.
Proof. vm_refl. Qed.
Lemma D_65194 : decode_any W_65194 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65198 : bv 32 := 0x00048593.
Lemma F_65198 : fetch_word AsanUbsan.M.loaded_segments (0x655b0 : word) = Some W_65198.
Proof. vm_refl. Qed.
Lemma D_65198 : decode_any W_65198 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6519c : bv 32 := 0x00090613.
Lemma F_6519c : fetch_word AsanUbsan.M.loaded_segments (0x655b4 : word) = Some W_6519c.
Proof. vm_refl. Qed.
Lemma D_6519c : decode_any W_6519c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651a0 : bv 32 := 0x000680e7.
Lemma F_651a0 : fetch_word AsanUbsan.M.loaded_segments (0x655b8 : word) = Some W_651a0.
Proof. vm_refl. Qed.
Lemma D_651a0 : decode_any W_651a0 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651a4 : bv 32 := 0x060a0063.
Lemma F_651a4 : fetch_word AsanUbsan.M.loaded_segments (0x655bc : word) = Some W_651a4.
Proof. vm_refl. Qed.
Lemma D_651a4 : decode_any W_651a4 = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651a8 : bv 32 := 0x04a05e63.
Lemma F_651a8 : fetch_word AsanUbsan.M.loaded_segments (0x655c0 : word) = Some W_651a8.
Proof. vm_refl. Qed.
Lemma D_651a8 : decode_any W_651a8 = Some (Branch BC_GE 0 10 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651ac : bv 32 := 0xfff4c593.
Lemma F_651ac : fetch_word AsanUbsan.M.loaded_segments (0x655c4 : word) = Some W_651ac.
Proof. vm_refl. Qed.
Lemma D_651ac : decode_any W_651ac = Some (OpImm ALU_XOR 11 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651b0 : bv 32 := 0x80040a13.
Lemma F_651b0 : fetch_word AsanUbsan.M.loaded_segments (0x655c8 : word) = Some W_651b0.
Proof. vm_refl. Qed.
Lemma D_651b0 : decode_any W_651b0 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651b4 : bv 32 := 0xfb8a0a13.
Lemma F_651b4 : fetch_word AsanUbsan.M.loaded_segments (0x655cc : word) = Some W_651b4.
Proof. vm_refl. Qed.
Lemma D_651b4 : decode_any W_651b4 = Some (OpImm ALU_ADD 20 20 4024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651b8 : bv 32 := 0x06a5e863.
Lemma F_651b8 : fetch_word AsanUbsan.M.loaded_segments (0x655d0 : word) = Some W_651b8.
Proof. vm_refl. Qed.
Lemma D_651b8 : decode_any W_651b8 = Some (Branch BC_LTU 11 10 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651bc : bv 32 := 0xfbf50593.
Lemma F_651bc : fetch_word AsanUbsan.M.loaded_segments (0x655d4 : word) = Some W_651bc.
Proof. vm_refl. Qed.
Lemma D_651bc : decode_any W_651bc = Some (OpImm ALU_ADD 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651c0 : bv 32 := 0xfc000613.
Lemma F_651c0 : fetch_word AsanUbsan.M.loaded_segments (0x655d8 : word) = Some W_651c0.
Proof. vm_refl. Qed.
Lemma D_651c0 : decode_any W_651c0 = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651c4 : bv 32 := 0x0cc5ee63.
Lemma F_651c4 : fetch_word AsanUbsan.M.loaded_segments (0x655dc : word) = Some W_651c4.
Proof. vm_refl. Qed.
Lemma D_651c4 : decode_any W_651c4 = Some (Branch BC_LTU 11 12 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651c8 : bv 32 := 0x000d2597.
Lemma F_651c8 : fetch_word AsanUbsan.M.loaded_segments (0x655e0 : word) = Some W_651c8.
Proof. vm_refl. Qed.
Lemma D_651c8 : decode_any W_651c8 = Some (Auipc 11 210, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651cc : bv 32 := 0xee05b583.
Lemma F_651cc : fetch_word AsanUbsan.M.loaded_segments (0x655e4 : word) = Some W_651cc.
Proof. vm_refl. Qed.
Lemma D_651cc : decode_any W_651cc = Some (Load SZ8 true 11 11 3808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651d0 : bv 32 := 0x00a486b3.
Lemma F_651d0 : fetch_word AsanUbsan.M.loaded_segments (0x655e8 : word) = Some W_651d0.
Proof. vm_refl. Qed.
Lemma D_651d0 : decode_any W_651d0 = Some (Op ALU_ADD 13 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651d4 : bv 32 := 0x0005b603.
Lemma F_651d4 : fetch_word AsanUbsan.M.loaded_segments (0x655ec : word) = Some W_651d4.
Proof. vm_refl. Qed.
Lemma D_651d4 : decode_any W_651d4 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651d8 : bv 32 := 0x0034d593.
Lemma F_651d8 : fetch_word AsanUbsan.M.loaded_segments (0x655f0 : word) = Some W_651d8.
Proof. vm_refl. Qed.
Lemma D_651d8 : decode_any W_651d8 = Some (ShiftImm ALU_SRL 11 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651dc : bv 32 := 0xfff68693.
Lemma F_651dc : fetch_word AsanUbsan.M.loaded_segments (0x655f4 : word) = Some W_651dc.
Proof. vm_refl. Qed.
Lemma D_651dc : decode_any W_651dc = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651e0 : bv 32 := 0x0036d713.
Lemma F_651e0 : fetch_word AsanUbsan.M.loaded_segments (0x655f8 : word) = Some W_651e0.
Proof. vm_refl. Qed.
Lemma D_651e0 : decode_any W_651e0 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651e4 : bv 32 := 0x00b605b3.
Lemma F_651e4 : fetch_word AsanUbsan.M.loaded_segments (0x655fc : word) = Some W_651e4.
Proof. vm_refl. Qed.
Lemma D_651e4 : decode_any W_651e4 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651e8 : bv 32 := 0x00e60633.
Lemma F_651e8 : fetch_word AsanUbsan.M.loaded_segments (0x65600 : word) = Some W_651e8.
Proof. vm_refl. Qed.
Lemma D_651e8 : decode_any W_651e8 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651ec : bv 32 := 0xff85f713.
Lemma F_651ec : fetch_word AsanUbsan.M.loaded_segments (0x65604 : word) = Some W_651ec.
Proof. vm_refl. Qed.
Lemma D_651ec : decode_any W_651ec = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651f0 : bv 32 := 0xff867793.
Lemma F_651f0 : fetch_word AsanUbsan.M.loaded_segments (0x65608 : word) = Some W_651f0.
Proof. vm_refl. Qed.
Lemma D_651f0 : decode_any W_651f0 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651f4 : bv 32 := 0x00073703.
Lemma F_651f4 : fetch_word AsanUbsan.M.loaded_segments (0x6560c : word) = Some W_651f4.
Proof. vm_refl. Qed.
Lemma D_651f4 : decode_any W_651f4 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651f8 : bv 32 := 0x0007b783.
Lemma F_651f8 : fetch_word AsanUbsan.M.loaded_segments (0x65610 : word) = Some W_651f8.
Proof. vm_refl. Qed.
Lemma D_651f8 : decode_any W_651f8 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651fc : bv 32 := 0x00e7e733.
Lemma F_651fc : fetch_word AsanUbsan.M.loaded_segments (0x65614 : word) = Some W_651fc.
Proof. vm_refl. Qed.
Lemma D_651fc : decode_any W_651fc = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65200 : bv 32 := 0x14071663.
Lemma F_65200 : fetch_word AsanUbsan.M.loaded_segments (0x65618 : word) = Some W_65200.
Proof. vm_refl. Qed.
Lemma D_65200 : decode_any W_65200 = Some (Branch BC_NE 14 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65204 : bv 32 := 0x06010113.
Lemma F_65204 : fetch_word AsanUbsan.M.loaded_segments (0x6561c : word) = Some W_65204.
Proof. vm_refl. Qed.
Lemma D_65204 : decode_any W_65204 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65208 : bv 32 := 0x7e813083.
Lemma F_65208 : fetch_word AsanUbsan.M.loaded_segments (0x65620 : word) = Some W_65208.
Proof. vm_refl. Qed.
Lemma D_65208 : decode_any W_65208 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6520c : bv 32 := 0x7e013403.
Lemma F_6520c : fetch_word AsanUbsan.M.loaded_segments (0x65624 : word) = Some W_6520c.
Proof. vm_refl. Qed.
Lemma D_6520c : decode_any W_6520c = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65210 : bv 32 := 0x7d813483.
Lemma F_65210 : fetch_word AsanUbsan.M.loaded_segments (0x65628 : word) = Some W_65210.
Proof. vm_refl. Qed.
Lemma D_65210 : decode_any W_65210 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65214 : bv 32 := 0x7d013903.
Lemma F_65214 : fetch_word AsanUbsan.M.loaded_segments (0x6562c : word) = Some W_65214.
Proof. vm_refl. Qed.
Lemma D_65214 : decode_any W_65214 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65218 : bv 32 := 0x7c813983.
Lemma F_65218 : fetch_word AsanUbsan.M.loaded_segments (0x65630 : word) = Some W_65218.
Proof. vm_refl. Qed.
Lemma D_65218 : decode_any W_65218 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6521c : bv 32 := 0x7c013a03.
Lemma F_6521c : fetch_word AsanUbsan.M.loaded_segments (0x65634 : word) = Some W_6521c.
Proof. vm_refl. Qed.
Lemma D_6521c : decode_any W_6521c = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65220 : bv 32 := 0x7f010113.
Lemma F_65220 : fetch_word AsanUbsan.M.loaded_segments (0x65638 : word) = Some W_65220.
Proof. vm_refl. Qed.
Lemma D_65220 : decode_any W_65220 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65224 : bv 32 := 0x00008067.
Lemma F_65224 : fetch_word AsanUbsan.M.loaded_segments (0x6563c : word) = Some W_65224.
Proof. vm_refl. Qed.
Lemma D_65224 : decode_any W_65224 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_652a0 : bv 32 := 0x00050913.
Lemma F_652a0 : fetch_word AsanUbsan.M.loaded_segments (0x656b8 : word) = Some W_652a0.
Proof. vm_refl. Qed.
Lemma D_652a0 : decode_any W_652a0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_652a4 : bv 32 := 0x00048513.
Lemma F_652a4 : fetch_word AsanUbsan.M.loaded_segments (0x656bc : word) = Some W_652a4.
Proof. vm_refl. Qed.
Lemma D_652a4 : decode_any W_652a4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_652a8 : bv 32 := 0x00090593.
Lemma F_652a8 : fetch_word AsanUbsan.M.loaded_segments (0x656c0 : word) = Some W_652a8.
Proof. vm_refl. Qed.
Lemma D_652a8 : decode_any W_652a8 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_652ac : bv 32 := 0x5fd150ef.
Lemma F_652ac : fetch_word AsanUbsan.M.loaded_segments (0x656c4 : word) = Some W_652ac.
Proof. vm_refl. Qed.
Lemma D_652ac : decode_any W_652ac = Some (Jal 1 89596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_652b0 : bv 32 := 0x00050493.
Lemma F_652b0 : fetch_word AsanUbsan.M.loaded_segments (0x656c8 : word) = Some W_652b0.
Proof. vm_refl. Qed.
Lemma D_652b0 : decode_any W_652b0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_652b4 : bv 32 := 0x00090513.
Lemma F_652b4 : fetch_word AsanUbsan.M.loaded_segments (0x656cc : word) = Some W_652b4.
Proof. vm_refl. Qed.
Lemma D_652b4 : decode_any W_652b4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_652b8 : bv 32 := 0xf40486e3.
Lemma F_652b8 : fetch_word AsanUbsan.M.loaded_segments (0x656d0 : word) = Some W_652b8.
Proof. vm_refl. Qed.
Lemma D_652b8 : decode_any W_652b8 = Some (Branch BC_EQ 9 0 8012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6534c : bv 32 := 0x00060703.
Lemma F_6534c : fetch_word AsanUbsan.M.loaded_segments (0x65764 : word) = Some W_6534c.
Proof. vm_refl. Qed.
Lemma D_6534c : decode_any W_6534c = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65350 : bv 32 := 0x0076f693.
Lemma F_65350 : fetch_word AsanUbsan.M.loaded_segments (0x65768 : word) = Some W_65350.
Proof. vm_refl. Qed.
Lemma D_65350 : decode_any W_65350 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65354 : bv 32 := 0x00e037b3.
Lemma F_65354 : fetch_word AsanUbsan.M.loaded_segments (0x6576c : word) = Some W_65354.
Proof. vm_refl. Qed.
Lemma D_65354 : decode_any W_65354 = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65358 : bv 32 := 0x00e6a6b3.
Lemma F_65358 : fetch_word AsanUbsan.M.loaded_segments (0x65770 : word) = Some W_65358.
Proof. vm_refl. Qed.
Lemma D_65358 : decode_any W_65358 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6535c : bv 32 := 0x0016c693.
Lemma F_6535c : fetch_word AsanUbsan.M.loaded_segments (0x65774 : word) = Some W_6535c.
Proof. vm_refl. Qed.
Lemma D_6535c : decode_any W_6535c = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65360 : bv 32 := 0x00d7f6b3.
Lemma F_65360 : fetch_word AsanUbsan.M.loaded_segments (0x65778 : word) = Some W_65360.
Proof. vm_refl. Qed.
Lemma D_65360 : decode_any W_65360 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65364 : bv 32 := 0x00c5fa63.
Lemma F_65364 : fetch_word AsanUbsan.M.loaded_segments (0x6577c : word) = Some W_65364.
Proof. vm_refl. Qed.
Lemma D_65364 : decode_any W_65364 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65368 : bv 32 := 0x0005c703.
Lemma F_65368 : fetch_word AsanUbsan.M.loaded_segments (0x65780 : word) = Some W_65368.
Proof. vm_refl. Qed.
Lemma D_65368 : decode_any W_65368 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6536c : bv 32 := 0x00158593.
Lemma F_6536c : fetch_word AsanUbsan.M.loaded_segments (0x65784 : word) = Some W_6536c.
Proof. vm_refl. Qed.
Lemma D_6536c : decode_any W_6536c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65370 : bv 32 := 0x00d766b3.
Lemma F_65370 : fetch_word AsanUbsan.M.loaded_segments (0x65788 : word) = Some W_65370.
Proof. vm_refl. Qed.
Lemma D_65370 : decode_any W_65370 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65374 : bv 32 := 0xfec59ae3.
Lemma F_65374 : fetch_word AsanUbsan.M.loaded_segments (0x6578c : word) = Some W_65374.
Proof. vm_refl. Qed.
Lemma D_65374 : decode_any W_65374 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65378 : bv 32 := 0x0ff6f593.
Lemma F_65378 : fetch_word AsanUbsan.M.loaded_segments (0x65790 : word) = Some W_65378.
Proof. vm_refl. Qed.
Lemma D_65378 : decode_any W_65378 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6537c : bv 32 := 0xe80584e3.
Lemma F_6537c : fetch_word AsanUbsan.M.loaded_segments (0x65794 : word) = Some W_6537c.
Proof. vm_refl. Qed.
Lemma D_6537c : decode_any W_6537c = Some (Branch BC_EQ 11 0 7816, 4%Z).
Proof. vm_refl. Qed.
