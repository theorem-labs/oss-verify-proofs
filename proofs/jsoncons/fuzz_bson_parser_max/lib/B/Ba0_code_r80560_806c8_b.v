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
Definition W_9a530 : bv 32 := 0x00008513.
Lemma F_9a530 : fetch_word AsanUbsan.M.loaded_segments (0x9a948 : word) = Some W_9a530.
Proof. vm_refl. Qed.
Lemma D_9a530 : decode_any W_9a530 = Some (OpImm ALU_ADD 10 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a534 : bv 32 := 0x00008067.
Lemma F_9a534 : fetch_word AsanUbsan.M.loaded_segments (0x9a94c : word) = Some W_9a534.
Proof. vm_refl. Qed.
Lemma D_9a534 : decode_any W_9a534 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a538 : bv 32 := 0xfc010113.
Lemma F_9a538 : fetch_word AsanUbsan.M.loaded_segments (0x9a950 : word) = Some W_9a538.
Proof. vm_refl. Qed.
Lemma D_9a538 : decode_any W_9a538 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a53c : bv 32 := 0x02113c23.
Lemma F_9a53c : fetch_word AsanUbsan.M.loaded_segments (0x9a954 : word) = Some W_9a53c.
Proof. vm_refl. Qed.
Lemma D_9a53c : decode_any W_9a53c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a540 : bv 32 := 0x02813823.
Lemma F_9a540 : fetch_word AsanUbsan.M.loaded_segments (0x9a958 : word) = Some W_9a540.
Proof. vm_refl. Qed.
Lemma D_9a540 : decode_any W_9a540 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a544 : bv 32 := 0x02913423.
Lemma F_9a544 : fetch_word AsanUbsan.M.loaded_segments (0x9a95c : word) = Some W_9a544.
Proof. vm_refl. Qed.
Lemma D_9a544 : decode_any W_9a544 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a548 : bv 32 := 0x03213023.
Lemma F_9a548 : fetch_word AsanUbsan.M.loaded_segments (0x9a960 : word) = Some W_9a548.
Proof. vm_refl. Qed.
Lemma D_9a548 : decode_any W_9a548 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a54c : bv 32 := 0x01313c23.
Lemma F_9a54c : fetch_word AsanUbsan.M.loaded_segments (0x9a964 : word) = Some W_9a54c.
Proof. vm_refl. Qed.
Lemma D_9a54c : decode_any W_9a54c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a550 : bv 32 := 0x01413823.
Lemma F_9a550 : fetch_word AsanUbsan.M.loaded_segments (0x9a968 : word) = Some W_9a550.
Proof. vm_refl. Qed.
Lemma D_9a550 : decode_any W_9a550 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a554 : bv 32 := 0x01513423.
Lemma F_9a554 : fetch_word AsanUbsan.M.loaded_segments (0x9a96c : word) = Some W_9a554.
Proof. vm_refl. Qed.
Lemma D_9a554 : decode_any W_9a554 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a558 : bv 32 := 0x01613023.
Lemma F_9a558 : fetch_word AsanUbsan.M.loaded_segments (0x9a970 : word) = Some W_9a558.
Proof. vm_refl. Qed.
Lemma D_9a558 : decode_any W_9a558 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a55c : bv 32 := 0x00068493.
Lemma F_9a55c : fetch_word AsanUbsan.M.loaded_segments (0x9a974 : word) = Some W_9a55c.
Proof. vm_refl. Qed.
Lemma D_9a55c : decode_any W_9a55c = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a560 : bv 32 := 0x02079413.
Lemma F_9a560 : fetch_word AsanUbsan.M.loaded_segments (0x9a978 : word) = Some W_9a560.
Proof. vm_refl. Qed.
Lemma D_9a560 : decode_any W_9a560 = Some (ShiftImm ALU_SLL 8 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a564 : bv 32 := 0x00100693.
Lemma F_9a564 : fetch_word AsanUbsan.M.loaded_segments (0x9a97c : word) = Some W_9a564.
Proof. vm_refl. Qed.
Lemma D_9a564 : decode_any W_9a564 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a568 : bv 32 := 0x02045413.
Lemma F_9a568 : fetch_word AsanUbsan.M.loaded_segments (0x9a980 : word) = Some W_9a568.
Proof. vm_refl. Qed.
Lemma D_9a568 : decode_any W_9a568 = Some (ShiftImm ALU_SRL 8 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a56c : bv 32 := 0x0ef6f863.
Lemma F_9a56c : fetch_word AsanUbsan.M.loaded_segments (0x9a984 : word) = Some W_9a56c.
Proof. vm_refl. Qed.
Lemma D_9a56c : decode_any W_9a56c = Some (Branch BC_GEU 13 15 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a570 : bv 32 := 0x0009d697.
Lemma F_9a570 : fetch_word AsanUbsan.M.loaded_segments (0x9a988 : word) = Some W_9a570.
Proof. vm_refl. Qed.
Lemma D_9a570 : decode_any W_9a570 = Some (Auipc 13 157, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a574 : bv 32 := 0xb186b903.
Lemma F_9a574 : fetch_word AsanUbsan.M.loaded_segments (0x9a98c : word) = Some W_9a574.
Proof. vm_refl. Qed.
Lemma D_9a574 : decode_any W_9a574 = Some (Load SZ8 true 18 13 2840, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a578 : bv 32 := 0x00093683.
Lemma F_9a578 : fetch_word AsanUbsan.M.loaded_segments (0x9a990 : word) = Some W_9a578.
Proof. vm_refl. Qed.
Lemma D_9a578 : decode_any W_9a578 = Some (Load SZ8 true 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a57c : bv 32 := 0x00068e63.
Lemma F_9a57c : fetch_word AsanUbsan.M.loaded_segments (0x9a994 : word) = Some W_9a57c.
Proof. vm_refl. Qed.
Lemma D_9a57c : decode_any W_9a57c = Some (Branch BC_EQ 13 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a580 : bv 32 := 0x00100793.
Lemma F_9a580 : fetch_word AsanUbsan.M.loaded_segments (0x9a998 : word) = Some W_9a580.
Proof. vm_refl. Qed.
Lemma D_9a580 : decode_any W_9a580 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a584 : bv 32 := 0x00c4d813.
Lemma F_9a584 : fetch_word AsanUbsan.M.loaded_segments (0x9a99c : word) = Some W_9a584.
Proof. vm_refl. Qed.
Lemma D_9a584 : decode_any W_9a584 = Some (ShiftImm ALU_SRL 16 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a588 : bv 32 := 0x00f52423.
Lemma F_9a588 : fetch_word AsanUbsan.M.loaded_segments (0x9a9a0 : word) = Some W_9a588.
Proof. vm_refl. Qed.
Lemma D_9a588 : decode_any W_9a588 = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a58c : bv 32 := 0x00b53823.
Lemma F_9a58c : fetch_word AsanUbsan.M.loaded_segments (0x9a9a4 : word) = Some W_9a58c.
Proof. vm_refl. Qed.
Lemma D_9a58c : decode_any W_9a58c = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a590 : bv 32 := 0x04081463.
Lemma F_9a590 : fetch_word AsanUbsan.M.loaded_segments (0x9a9a8 : word) = Some W_9a590.
Proof. vm_refl. Qed.
Lemma D_9a590 : decode_any W_9a590 = Some (Branch BC_NE 16 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a5d8 : bv 32 := 0x0a977263.
Lemma F_9a5d8 : fetch_word AsanUbsan.M.loaded_segments (0x9a9f0 : word) = Some W_9a5d8.
Proof. vm_refl. Qed.
Lemma D_9a5d8 : decode_any W_9a5d8 = Some (Branch BC_GEU 14 9 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a5dc : bv 32 := 0x04c77c63.
Lemma F_9a5dc : fetch_word AsanUbsan.M.loaded_segments (0x9a9f4 : word) = Some W_9a5dc.
Proof. vm_refl. Qed.
Lemma D_9a5dc : decode_any W_9a5dc = Some (Branch BC_GEU 14 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a5e0 : bv 32 := 0xff048493.
Lemma F_9a5e0 : fetch_word AsanUbsan.M.loaded_segments (0x9a9f8 : word) = Some W_9a5e0.
Proof. vm_refl. Qed.
Lemma D_9a5e0 : decode_any W_9a5e0 = Some (OpImm ALU_ADD 9 9 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a5e4 : bv 32 := 0x04967863.
Lemma F_9a5e4 : fetch_word AsanUbsan.M.loaded_segments (0x9a9fc : word) = Some W_9a5e4.
Proof. vm_refl. Qed.
Lemma D_9a5e4 : decode_any W_9a5e4 = Some (Branch BC_GEU 12 9 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a5e8 : bv 32 := 0x00767713.
Lemma F_9a5e8 : fetch_word AsanUbsan.M.loaded_segments (0x9aa00 : word) = Some W_9a5e8.
Proof. vm_refl. Qed.
Lemma D_9a5e8 : decode_any W_9a5e8 = Some (OpImm ALU_AND 14 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a5ec : bv 32 := 0x04071463.
Lemma F_9a5ec : fetch_word AsanUbsan.M.loaded_segments (0x9aa04 : word) = Some W_9a5ec.
Proof. vm_refl. Qed.
Lemma D_9a5ec : decode_any W_9a5ec = Some (Branch BC_NE 14 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a5f0 : bv 32 := 0x01050713.
Lemma F_9a5f0 : fetch_word AsanUbsan.M.loaded_segments (0x9aa08 : word) = Some W_9a5f0.
Proof. vm_refl. Qed.
Lemma D_9a5f0 : decode_any W_9a5f0 = Some (OpImm ALU_ADD 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a5f4 : bv 32 := 0x00100793.
Lemma F_9a5f4 : fetch_word AsanUbsan.M.loaded_segments (0x9aa0c : word) = Some W_9a5f4.
Proof. vm_refl. Qed.
Lemma D_9a5f4 : decode_any W_9a5f4 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a5f8 : bv 32 := 0x0287fe63.
Lemma F_9a5f8 : fetch_word AsanUbsan.M.loaded_segments (0x9aa10 : word) = Some W_9a5f8.
Proof. vm_refl. Qed.
Lemma D_9a5f8 : decode_any W_9a5f8 = Some (Branch BC_GEU 15 8 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a5fc : bv 32 := 0xff863803.
Lemma F_9a5fc : fetch_word AsanUbsan.M.loaded_segments (0x9aa14 : word) = Some W_9a5fc.
Proof. vm_refl. Qed.
Lemma D_9a5fc : decode_any W_9a5fc = Some (Load SZ8 true 16 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a600 : bv 32 := 0x02d86a63.
Lemma F_9a600 : fetch_word AsanUbsan.M.loaded_segments (0x9aa18 : word) = Some W_9a600.
Proof. vm_refl. Qed.
Lemma D_9a600 : decode_any W_9a600 = Some (Branch BC_LTU 16 13 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a604 : bv 32 := 0x00b80c63.
Lemma F_9a604 : fetch_word AsanUbsan.M.loaded_segments (0x9aa1c : word) = Some W_9a604.
Proof. vm_refl. Qed.
Lemma D_9a604 : decode_any W_9a604 = Some (Branch BC_EQ 16 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a608 : bv 32 := 0x00379893.
Lemma F_9a608 : fetch_word AsanUbsan.M.loaded_segments (0x9aa20 : word) = Some W_9a608.
Proof. vm_refl. Qed.
Lemma D_9a608 : decode_any W_9a608 = Some (ShiftImm ALU_SLL 17 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a60c : bv 32 := 0x00178793.
Lemma F_9a60c : fetch_word AsanUbsan.M.loaded_segments (0x9aa24 : word) = Some W_9a60c.
Proof. vm_refl. Qed.
Lemma D_9a60c : decode_any W_9a60c = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a610 : bv 32 := 0x011708b3.
Lemma F_9a610 : fetch_word AsanUbsan.M.loaded_segments (0x9aa28 : word) = Some W_9a610.
Proof. vm_refl. Qed.
Lemma D_9a610 : decode_any W_9a610 = Some (Op ALU_ADD 17 14 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a614 : bv 32 := 0x00f52423.
Lemma F_9a614 : fetch_word AsanUbsan.M.loaded_segments (0x9aa2c : word) = Some W_9a614.
Proof. vm_refl. Qed.
Lemma D_9a614 : decode_any W_9a614 = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a618 : bv 32 := 0x0108b023.
Lemma F_9a618 : fetch_word AsanUbsan.M.loaded_segments (0x9aa30 : word) = Some W_9a618.
Proof. vm_refl. Qed.
Lemma D_9a618 : decode_any W_9a618 = Some (Store SZ8 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a61c : bv 32 := 0xff063803.
Lemma F_9a61c : fetch_word AsanUbsan.M.loaded_segments (0x9aa34 : word) = Some W_9a61c.
Proof. vm_refl. Qed.
Lemma D_9a61c : decode_any W_9a61c = Some (Load SZ8 true 16 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a620 : bv 32 := 0x01067a63.
Lemma F_9a620 : fetch_word AsanUbsan.M.loaded_segments (0x9aa38 : word) = Some W_9a620.
Proof. vm_refl. Qed.
Lemma D_9a620 : decode_any W_9a620 = Some (Branch BC_GEU 12 16 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a624 : bv 32 := 0x00987863.
Lemma F_9a624 : fetch_word AsanUbsan.M.loaded_segments (0x9aa3c : word) = Some W_9a624.
Proof. vm_refl. Qed.
Lemma D_9a624 : decode_any W_9a624 = Some (Branch BC_GEU 16 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a628 : bv 32 := 0x00787893.
Lemma F_9a628 : fetch_word AsanUbsan.M.loaded_segments (0x9aa40 : word) = Some W_9a628.
Proof. vm_refl. Qed.
Lemma D_9a628 : decode_any W_9a628 = Some (OpImm ALU_AND 17 16 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a62c : bv 32 := 0x00080613.
Lemma F_9a62c : fetch_word AsanUbsan.M.loaded_segments (0x9aa44 : word) = Some W_9a62c.
Proof. vm_refl. Qed.
Lemma D_9a62c : decode_any W_9a62c = Some (OpImm ALU_ADD 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a630 : bv 32 := 0xfc0884e3.
Lemma F_9a630 : fetch_word AsanUbsan.M.loaded_segments (0x9aa48 : word) = Some W_9a630.
Proof. vm_refl. Qed.
Lemma D_9a630 : decode_any W_9a630 = Some (Branch BC_EQ 17 0 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a634 : bv 32 := 0x03813083.
Lemma F_9a634 : fetch_word AsanUbsan.M.loaded_segments (0x9aa4c : word) = Some W_9a634.
Proof. vm_refl. Qed.
Lemma D_9a634 : decode_any W_9a634 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a638 : bv 32 := 0x03013403.
Lemma F_9a638 : fetch_word AsanUbsan.M.loaded_segments (0x9aa50 : word) = Some W_9a638.
Proof. vm_refl. Qed.
Lemma D_9a638 : decode_any W_9a638 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a63c : bv 32 := 0x02813483.
Lemma F_9a63c : fetch_word AsanUbsan.M.loaded_segments (0x9aa54 : word) = Some W_9a63c.
Proof. vm_refl. Qed.
Lemma D_9a63c : decode_any W_9a63c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a640 : bv 32 := 0x02013903.
Lemma F_9a640 : fetch_word AsanUbsan.M.loaded_segments (0x9aa58 : word) = Some W_9a640.
Proof. vm_refl. Qed.
Lemma D_9a640 : decode_any W_9a640 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a644 : bv 32 := 0x01813983.
Lemma F_9a644 : fetch_word AsanUbsan.M.loaded_segments (0x9aa5c : word) = Some W_9a644.
Proof. vm_refl. Qed.
Lemma D_9a644 : decode_any W_9a644 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a648 : bv 32 := 0x01013a03.
Lemma F_9a648 : fetch_word AsanUbsan.M.loaded_segments (0x9aa60 : word) = Some W_9a648.
Proof. vm_refl. Qed.
Lemma D_9a648 : decode_any W_9a648 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a64c : bv 32 := 0x00813a83.
Lemma F_9a64c : fetch_word AsanUbsan.M.loaded_segments (0x9aa64 : word) = Some W_9a64c.
Proof. vm_refl. Qed.
Lemma D_9a64c : decode_any W_9a64c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a650 : bv 32 := 0x00013b03.
Lemma F_9a650 : fetch_word AsanUbsan.M.loaded_segments (0x9aa68 : word) = Some W_9a650.
Proof. vm_refl. Qed.
Lemma D_9a650 : decode_any W_9a650 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a654 : bv 32 := 0x04010113.
Lemma F_9a654 : fetch_word AsanUbsan.M.loaded_segments (0x9aa6c : word) = Some W_9a654.
Proof. vm_refl. Qed.
Lemma D_9a654 : decode_any W_9a654 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a658 : bv 32 := 0x00008067.
Lemma F_9a658 : fetch_word AsanUbsan.M.loaded_segments (0x9aa70 : word) = Some W_9a658.
Proof. vm_refl. Qed.
Lemma D_9a658 : decode_any W_9a658 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
