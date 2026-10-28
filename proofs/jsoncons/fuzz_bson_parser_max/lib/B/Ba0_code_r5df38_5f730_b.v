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
Definition W_77870 : bv 32 := 0x2590006f.
Lemma F_77870 : fetch_word AsanUbsan.M.loaded_segments (0x77c88 : word) = Some W_77870.
Proof. vm_refl. Qed.
Lemma D_77870 : decode_any W_77870 = Some (Jal 0 2648, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77874 : bv 32 := 0x5450006f.
Lemma F_77874 : fetch_word AsanUbsan.M.loaded_segments (0x77c8c : word) = Some W_77874.
Proof. vm_refl. Qed.
Lemma D_77874 : decode_any W_77874 = Some (Jal 0 3396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77878 : bv 32 := 0x2000106f.
Lemma F_77878 : fetch_word AsanUbsan.M.loaded_segments (0x77c90 : word) = Some W_77878.
Proof. vm_refl. Qed.
Lemma D_77878 : decode_any W_77878 = Some (Jal 0 4608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7787c : bv 32 := 0x81010113.
Lemma F_7787c : fetch_word AsanUbsan.M.loaded_segments (0x77c94 : word) = Some W_7787c.
Proof. vm_refl. Qed.
Lemma D_7787c : decode_any W_7787c = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77880 : bv 32 := 0x7e113423.
Lemma F_77880 : fetch_word AsanUbsan.M.loaded_segments (0x77c98 : word) = Some W_77880.
Proof. vm_refl. Qed.
Lemma D_77880 : decode_any W_77880 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77884 : bv 32 := 0x7e813023.
Lemma F_77884 : fetch_word AsanUbsan.M.loaded_segments (0x77c9c : word) = Some W_77884.
Proof. vm_refl. Qed.
Lemma D_77884 : decode_any W_77884 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77888 : bv 32 := 0x7c913c23.
Lemma F_77888 : fetch_word AsanUbsan.M.loaded_segments (0x77ca0 : word) = Some W_77888.
Proof. vm_refl. Qed.
Lemma D_77888 : decode_any W_77888 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7788c : bv 32 := 0x7d213823.
Lemma F_7788c : fetch_word AsanUbsan.M.loaded_segments (0x77ca4 : word) = Some W_7788c.
Proof. vm_refl. Qed.
Lemma D_7788c : decode_any W_7788c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77890 : bv 32 := 0x7d313423.
Lemma F_77890 : fetch_word AsanUbsan.M.loaded_segments (0x77ca8 : word) = Some W_77890.
Proof. vm_refl. Qed.
Lemma D_77890 : decode_any W_77890 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77894 : bv 32 := 0x7d413023.
Lemma F_77894 : fetch_word AsanUbsan.M.loaded_segments (0x77cac : word) = Some W_77894.
Proof. vm_refl. Qed.
Lemma D_77894 : decode_any W_77894 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77898 : bv 32 := 0x7b513c23.
Lemma F_77898 : fetch_word AsanUbsan.M.loaded_segments (0x77cb0 : word) = Some W_77898.
Proof. vm_refl. Qed.
Lemma D_77898 : decode_any W_77898 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7789c : bv 32 := 0x7b613823.
Lemma F_7789c : fetch_word AsanUbsan.M.loaded_segments (0x77cb4 : word) = Some W_7789c.
Proof. vm_refl. Qed.
Lemma D_7789c : decode_any W_7789c = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778a0 : bv 32 := 0x7b713423.
Lemma F_778a0 : fetch_word AsanUbsan.M.loaded_segments (0x77cb8 : word) = Some W_778a0.
Proof. vm_refl. Qed.
Lemma D_778a0 : decode_any W_778a0 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778a4 : bv 32 := 0x7f010413.
Lemma F_778a4 : fetch_word AsanUbsan.M.loaded_segments (0x77cbc : word) = Some W_778a4.
Proof. vm_refl. Qed.
Lemma D_778a4 : decode_any W_778a4 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778a8 : bv 32 := 0xf9010113.
Lemma F_778a8 : fetch_word AsanUbsan.M.loaded_segments (0x77cc0 : word) = Some W_778a8.
Proof. vm_refl. Qed.
Lemma D_778a8 : decode_any W_778a8 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778ac : bv 32 := 0x000c0697.
Lemma F_778ac : fetch_word AsanUbsan.M.loaded_segments (0x77cc4 : word) = Some W_778ac.
Proof. vm_refl. Qed.
Lemma D_778ac : decode_any W_778ac = Some (Auipc 13 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778b0 : bv 32 := 0x3646b683.
Lemma F_778b0 : fetch_word AsanUbsan.M.loaded_segments (0x77cc8 : word) = Some W_778b0.
Proof. vm_refl. Qed.
Lemma D_778b0 : decode_any W_778b0 = Some (Load SZ8 true 13 13 868, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778b4 : bv 32 := 0x0006c683.
Lemma F_778b4 : fetch_word AsanUbsan.M.loaded_segments (0x77ccc : word) = Some W_778b4.
Proof. vm_refl. Qed.
Lemma D_778b4 : decode_any W_778b4 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778b8 : bv 32 := 0x0e068863.
Lemma F_778b8 : fetch_word AsanUbsan.M.loaded_segments (0x77cd0 : word) = Some W_778b8.
Proof. vm_refl. Qed.
Lemma D_778b8 : decode_any W_778b8 = Some (Branch BC_EQ 13 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778bc : bv 32 := 0x80040a13.
Lemma F_778bc : fetch_word AsanUbsan.M.loaded_segments (0x77cd4 : word) = Some W_778bc.
Proof. vm_refl. Qed.
Lemma D_778bc : decode_any W_778bc = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778c0 : bv 32 := 0xfa0a0a13.
Lemma F_778c0 : fetch_word AsanUbsan.M.loaded_segments (0x77cd8 : word) = Some W_778c0.
Proof. vm_refl. Qed.
Lemma D_778c0 : decode_any W_778c0 = Some (OpImm ALU_ADD 20 20 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778c4 : bv 32 := 0x00c58ab3.
Lemma F_778c4 : fetch_word AsanUbsan.M.loaded_segments (0x77cdc : word) = Some W_778c4.
Proof. vm_refl. Qed.
Lemma D_778c4 : decode_any W_778c4 = Some (Op ALU_ADD 21 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778c8 : bv 32 := 0x00c509b3.
Lemma F_778c8 : fetch_word AsanUbsan.M.loaded_segments (0x77ce0 : word) = Some W_778c8.
Proof. vm_refl. Qed.
Lemma D_778c8 : decode_any W_778c8 = Some (Op ALU_ADD 19 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778cc : bv 32 := 0x00b50663.
Lemma F_778cc : fetch_word AsanUbsan.M.loaded_segments (0x77ce4 : word) = Some W_778cc.
Proof. vm_refl. Qed.
Lemma D_778cc : decode_any W_778cc = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778d0 : bv 32 := 0x0135f463.
Lemma F_778d0 : fetch_word AsanUbsan.M.loaded_segments (0x77ce8 : word) = Some W_778d0.
Proof. vm_refl. Qed.
Lemma D_778d0 : decode_any W_778d0 = Some (Branch BC_GEU 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778d4 : bv 32 := 0x1b556a63.
Lemma F_778d4 : fetch_word AsanUbsan.M.loaded_segments (0x77cec : word) = Some W_778d4.
Proof. vm_refl. Qed.
Lemma D_778d4 : decode_any W_778d4 = Some (Branch BC_LTU 10 21 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778d8 : bv 32 := 0xfff5c693.
Lemma F_778d8 : fetch_word AsanUbsan.M.loaded_segments (0x77cf0 : word) = Some W_778d8.
Proof. vm_refl. Qed.
Lemma D_778d8 : decode_any W_778d8 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778dc : bv 32 := 0x26c6e463.
Lemma F_778dc : fetch_word AsanUbsan.M.loaded_segments (0x77cf4 : word) = Some W_778dc.
Proof. vm_refl. Qed.
Lemma D_778dc : decode_any W_778dc = Some (Branch BC_LTU 13 12 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778e0 : bv 32 := 0xfbf60b13.
Lemma F_778e0 : fetch_word AsanUbsan.M.loaded_segments (0x77cf8 : word) = Some W_778e0.
Proof. vm_refl. Qed.
Lemma D_778e0 : decode_any W_778e0 = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778e4 : bv 32 := 0xfbf00693.
Lemma F_778e4 : fetch_word AsanUbsan.M.loaded_segments (0x77cfc : word) = Some W_778e4.
Proof. vm_refl. Qed.
Lemma D_778e4 : decode_any W_778e4 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778e8 : bv 32 := 0x2f66f263.
Lemma F_778e8 : fetch_word AsanUbsan.M.loaded_segments (0x77d00 : word) = Some W_778e8.
Proof. vm_refl. Qed.
Lemma D_778e8 : decode_any W_778e8 = Some (Branch BC_GEU 13 22 740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778ec : bv 32 := 0x000bf697.
Lemma F_778ec : fetch_word AsanUbsan.M.loaded_segments (0x77d04 : word) = Some W_778ec.
Proof. vm_refl. Qed.
Lemma D_778ec : decode_any W_778ec = Some (Auipc 13 191, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778f0 : bv 32 := 0x7bc6b683.
Lemma F_778f0 : fetch_word AsanUbsan.M.loaded_segments (0x77d08 : word) = Some W_778f0.
Proof. vm_refl. Qed.
Lemma D_778f0 : decode_any W_778f0 = Some (Load SZ8 true 13 13 1980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778f4 : bv 32 := 0x0006b703.
Lemma F_778f4 : fetch_word AsanUbsan.M.loaded_segments (0x77d0c : word) = Some W_778f4.
Proof. vm_refl. Qed.
Lemma D_778f4 : decode_any W_778f4 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778f8 : bv 32 := 0xfffa8a93.
Lemma F_778f8 : fetch_word AsanUbsan.M.loaded_segments (0x77d10 : word) = Some W_778f8.
Proof. vm_refl. Qed.
Lemma D_778f8 : decode_any W_778f8 = Some (OpImm ALU_ADD 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_778fc : bv 32 := 0x0035d693.
Lemma F_778fc : fetch_word AsanUbsan.M.loaded_segments (0x77d14 : word) = Some W_778fc.
Proof. vm_refl. Qed.
Lemma D_778fc : decode_any W_778fc = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77900 : bv 32 := 0x003ad793.
Lemma F_77900 : fetch_word AsanUbsan.M.loaded_segments (0x77d18 : word) = Some W_77900.
Proof. vm_refl. Qed.
Lemma D_77900 : decode_any W_77900 = Some (ShiftImm ALU_SRL 15 21 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77904 : bv 32 := 0x00d706b3.
Lemma F_77904 : fetch_word AsanUbsan.M.loaded_segments (0x77d1c : word) = Some W_77904.
Proof. vm_refl. Qed.
Lemma D_77904 : decode_any W_77904 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77908 : bv 32 := 0x00f70733.
Lemma F_77908 : fetch_word AsanUbsan.M.loaded_segments (0x77d20 : word) = Some W_77908.
Proof. vm_refl. Qed.
Lemma D_77908 : decode_any W_77908 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7790c : bv 32 := 0xff86f793.
Lemma F_7790c : fetch_word AsanUbsan.M.loaded_segments (0x77d24 : word) = Some W_7790c.
Proof. vm_refl. Qed.
Lemma D_7790c : decode_any W_7790c = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77910 : bv 32 := 0xff877813.
Lemma F_77910 : fetch_word AsanUbsan.M.loaded_segments (0x77d28 : word) = Some W_77910.
Proof. vm_refl. Qed.
Lemma D_77910 : decode_any W_77910 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77914 : bv 32 := 0x0007b783.
Lemma F_77914 : fetch_word AsanUbsan.M.loaded_segments (0x77d2c : word) = Some W_77914.
Proof. vm_refl. Qed.
Lemma D_77914 : decode_any W_77914 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77918 : bv 32 := 0x00083803.
Lemma F_77918 : fetch_word AsanUbsan.M.loaded_segments (0x77d30 : word) = Some W_77918.
Proof. vm_refl. Qed.
Lemma D_77918 : decode_any W_77918 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7791c : bv 32 := 0x00f867b3.
Lemma F_7791c : fetch_word AsanUbsan.M.loaded_segments (0x77d34 : word) = Some W_7791c.
Proof. vm_refl. Qed.
Lemma D_7791c : decode_any W_7791c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77920 : bv 32 := 0x2a079a63.
Lemma F_77920 : fetch_word AsanUbsan.M.loaded_segments (0x77d38 : word) = Some W_77920.
Proof. vm_refl. Qed.
Lemma D_77920 : decode_any W_77920 = Some (Branch BC_NE 15 0 692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77924 : bv 32 := 0xfff54693.
Lemma F_77924 : fetch_word AsanUbsan.M.loaded_segments (0x77d3c : word) = Some W_77924.
Proof. vm_refl. Qed.
Lemma D_77924 : decode_any W_77924 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77928 : bv 32 := 0x0cc6ea63.
Lemma F_77928 : fetch_word AsanUbsan.M.loaded_segments (0x77d40 : word) = Some W_77928.
Proof. vm_refl. Qed.
Lemma D_77928 : decode_any W_77928 = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7792c : bv 32 := 0xfbf00693.
Lemma F_7792c : fetch_word AsanUbsan.M.loaded_segments (0x77d44 : word) = Some W_7792c.
Proof. vm_refl. Qed.
Lemma D_7792c : decode_any W_7792c = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77930 : bv 32 := 0x1566f863.
Lemma F_77930 : fetch_word AsanUbsan.M.loaded_segments (0x77d48 : word) = Some W_77930.
Proof. vm_refl. Qed.
Lemma D_77930 : decode_any W_77930 = Some (Branch BC_GEU 13 22 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77934 : bv 32 := 0x000bf697.
Lemma F_77934 : fetch_word AsanUbsan.M.loaded_segments (0x77d4c : word) = Some W_77934.
Proof. vm_refl. Qed.
Lemma D_77934 : decode_any W_77934 = Some (Auipc 13 191, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77938 : bv 32 := 0x7746b683.
Lemma F_77938 : fetch_word AsanUbsan.M.loaded_segments (0x77d50 : word) = Some W_77938.
Proof. vm_refl. Qed.
Lemma D_77938 : decode_any W_77938 = Some (Load SZ8 true 13 13 1908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7793c : bv 32 := 0x0006b703.
Lemma F_7793c : fetch_word AsanUbsan.M.loaded_segments (0x77d54 : word) = Some W_7793c.
Proof. vm_refl. Qed.
Lemma D_7793c : decode_any W_7793c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77940 : bv 32 := 0xfff98993.
Lemma F_77940 : fetch_word AsanUbsan.M.loaded_segments (0x77d58 : word) = Some W_77940.
Proof. vm_refl. Qed.
Lemma D_77940 : decode_any W_77940 = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77944 : bv 32 := 0x00355693.
Lemma F_77944 : fetch_word AsanUbsan.M.loaded_segments (0x77d5c : word) = Some W_77944.
Proof. vm_refl. Qed.
Lemma D_77944 : decode_any W_77944 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77948 : bv 32 := 0x0039d793.
Lemma F_77948 : fetch_word AsanUbsan.M.loaded_segments (0x77d60 : word) = Some W_77948.
Proof. vm_refl. Qed.
Lemma D_77948 : decode_any W_77948 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7794c : bv 32 := 0x00d706b3.
Lemma F_7794c : fetch_word AsanUbsan.M.loaded_segments (0x77d64 : word) = Some W_7794c.
Proof. vm_refl. Qed.
Lemma D_7794c : decode_any W_7794c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77950 : bv 32 := 0x00f70733.
Lemma F_77950 : fetch_word AsanUbsan.M.loaded_segments (0x77d68 : word) = Some W_77950.
Proof. vm_refl. Qed.
Lemma D_77950 : decode_any W_77950 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77954 : bv 32 := 0xff86f793.
Lemma F_77954 : fetch_word AsanUbsan.M.loaded_segments (0x77d6c : word) = Some W_77954.
Proof. vm_refl. Qed.
Lemma D_77954 : decode_any W_77954 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77958 : bv 32 := 0xff877813.
Lemma F_77958 : fetch_word AsanUbsan.M.loaded_segments (0x77d70 : word) = Some W_77958.
Proof. vm_refl. Qed.
Lemma D_77958 : decode_any W_77958 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7795c : bv 32 := 0x0007b783.
Lemma F_7795c : fetch_word AsanUbsan.M.loaded_segments (0x77d74 : word) = Some W_7795c.
Proof. vm_refl. Qed.
Lemma D_7795c : decode_any W_7795c = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77960 : bv 32 := 0x00083803.
Lemma F_77960 : fetch_word AsanUbsan.M.loaded_segments (0x77d78 : word) = Some W_77960.
Proof. vm_refl. Qed.
Lemma D_77960 : decode_any W_77960 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77964 : bv 32 := 0x00f867b3.
Lemma F_77964 : fetch_word AsanUbsan.M.loaded_segments (0x77d7c : word) = Some W_77964.
Proof. vm_refl. Qed.
Lemma D_77964 : decode_any W_77964 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77968 : bv 32 := 0x30079863.
Lemma F_77968 : fetch_word AsanUbsan.M.loaded_segments (0x77d80 : word) = Some W_77968.
Proof. vm_refl. Qed.
Lemma D_77968 : decode_any W_77968 = Some (Branch BC_NE 15 0 784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7796c : bv 32 := 0x000c1697.
Lemma F_7796c : fetch_word AsanUbsan.M.loaded_segments (0x77d84 : word) = Some W_7796c.
Proof. vm_refl. Qed.
Lemma D_7796c : decode_any W_7796c = Some (Auipc 13 193, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77970 : bv 32 := 0x7446b683.
Lemma F_77970 : fetch_word AsanUbsan.M.loaded_segments (0x77d88 : word) = Some W_77970.
Proof. vm_refl. Qed.
Lemma D_77970 : decode_any W_77970 = Some (Load SZ8 true 13 13 1860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77974 : bv 32 := 0x000680e7.
Lemma F_77974 : fetch_word AsanUbsan.M.loaded_segments (0x77d8c : word) = Some W_77974.
Proof. vm_refl. Qed.
Lemma D_77974 : decode_any W_77974 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77978 : bv 32 := 0x07010113.
Lemma F_77978 : fetch_word AsanUbsan.M.loaded_segments (0x77d90 : word) = Some W_77978.
Proof. vm_refl. Qed.
Lemma D_77978 : decode_any W_77978 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7797c : bv 32 := 0x7e813083.
Lemma F_7797c : fetch_word AsanUbsan.M.loaded_segments (0x77d94 : word) = Some W_7797c.
Proof. vm_refl. Qed.
Lemma D_7797c : decode_any W_7797c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77980 : bv 32 := 0x7e013403.
Lemma F_77980 : fetch_word AsanUbsan.M.loaded_segments (0x77d98 : word) = Some W_77980.
Proof. vm_refl. Qed.
Lemma D_77980 : decode_any W_77980 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77984 : bv 32 := 0x7d813483.
Lemma F_77984 : fetch_word AsanUbsan.M.loaded_segments (0x77d9c : word) = Some W_77984.
Proof. vm_refl. Qed.
Lemma D_77984 : decode_any W_77984 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77988 : bv 32 := 0x7d013903.
Lemma F_77988 : fetch_word AsanUbsan.M.loaded_segments (0x77da0 : word) = Some W_77988.
Proof. vm_refl. Qed.
Lemma D_77988 : decode_any W_77988 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7798c : bv 32 := 0x7c813983.
Lemma F_7798c : fetch_word AsanUbsan.M.loaded_segments (0x77da4 : word) = Some W_7798c.
Proof. vm_refl. Qed.
Lemma D_7798c : decode_any W_7798c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77990 : bv 32 := 0x7c013a03.
Lemma F_77990 : fetch_word AsanUbsan.M.loaded_segments (0x77da8 : word) = Some W_77990.
Proof. vm_refl. Qed.
Lemma D_77990 : decode_any W_77990 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77994 : bv 32 := 0x7b813a83.
Lemma F_77994 : fetch_word AsanUbsan.M.loaded_segments (0x77dac : word) = Some W_77994.
Proof. vm_refl. Qed.
Lemma D_77994 : decode_any W_77994 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77998 : bv 32 := 0x7b013b03.
Lemma F_77998 : fetch_word AsanUbsan.M.loaded_segments (0x77db0 : word) = Some W_77998.
Proof. vm_refl. Qed.
Lemma D_77998 : decode_any W_77998 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7799c : bv 32 := 0x7a813b83.
Lemma F_7799c : fetch_word AsanUbsan.M.loaded_segments (0x77db4 : word) = Some W_7799c.
Proof. vm_refl. Qed.
Lemma D_7799c : decode_any W_7799c = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_779a0 : bv 32 := 0x7f010113.
Lemma F_779a0 : fetch_word AsanUbsan.M.loaded_segments (0x77db8 : word) = Some W_779a0.
Proof. vm_refl. Qed.
Lemma D_779a0 : decode_any W_779a0 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_779a4 : bv 32 := 0x00008067.
Lemma F_779a4 : fetch_word AsanUbsan.M.loaded_segments (0x77dbc : word) = Some W_779a4.
Proof. vm_refl. Qed.
Lemma D_779a4 : decode_any W_779a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a80 : bv 32 := 0x22061663.
Lemma F_77a80 : fetch_word AsanUbsan.M.loaded_segments (0x77e98 : word) = Some W_77a80.
Proof. vm_refl. Qed.
Lemma D_77a80 : decode_any W_77a80 = Some (Branch BC_NE 12 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a84 : bv 32 := 0xee9ff06f.
Lemma F_77a84 : fetch_word AsanUbsan.M.loaded_segments (0x77e9c : word) = Some W_77a84.
Proof. vm_refl. Qed.
Lemma D_77a84 : decode_any W_77a84 = Some (Jal 0 2096872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bcc : bv 32 := 0x02061e63.
Lemma F_77bcc : fetch_word AsanUbsan.M.loaded_segments (0x77fe4 : word) = Some W_77bcc.
Proof. vm_refl. Qed.
Lemma D_77bcc : decode_any W_77bcc = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bd0 : bv 32 := 0xd55ff06f.
Lemma F_77bd0 : fetch_word AsanUbsan.M.loaded_segments (0x77fe8 : word) = Some W_77bd0.
Proof. vm_refl. Qed.
Lemma D_77bd0 : decode_any W_77bd0 = Some (Jal 0 2096468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bd4 : bv 32 := 0x00070783.
Lemma F_77bd4 : fetch_word AsanUbsan.M.loaded_segments (0x77fec : word) = Some W_77bd4.
Proof. vm_refl. Qed.
Lemma D_77bd4 : decode_any W_77bd4 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bd8 : bv 32 := 0x007af813.
Lemma F_77bd8 : fetch_word AsanUbsan.M.loaded_segments (0x77ff0 : word) = Some W_77bd8.
Proof. vm_refl. Qed.
Lemma D_77bd8 : decode_any W_77bd8 = Some (OpImm ALU_AND 16 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bdc : bv 32 := 0x00f038b3.
Lemma F_77bdc : fetch_word AsanUbsan.M.loaded_segments (0x77ff4 : word) = Some W_77bdc.
Proof. vm_refl. Qed.
Lemma D_77bdc : decode_any W_77bdc = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77be0 : bv 32 := 0x00f827b3.
Lemma F_77be0 : fetch_word AsanUbsan.M.loaded_segments (0x77ff8 : word) = Some W_77be0.
Proof. vm_refl. Qed.
Lemma D_77be0 : decode_any W_77be0 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77be4 : bv 32 := 0x0017c793.
Lemma F_77be4 : fetch_word AsanUbsan.M.loaded_segments (0x77ffc : word) = Some W_77be4.
Proof. vm_refl. Qed.
Lemma D_77be4 : decode_any W_77be4 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77be8 : bv 32 := 0x00f8f7b3.
Lemma F_77be8 : fetch_word AsanUbsan.M.loaded_segments (0x78000 : word) = Some W_77be8.
Proof. vm_refl. Qed.
Lemma D_77be8 : decode_any W_77be8 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bec : bv 32 := 0x00e6fa63.
Lemma F_77bec : fetch_word AsanUbsan.M.loaded_segments (0x78004 : word) = Some W_77bec.
Proof. vm_refl. Qed.
Lemma D_77bec : decode_any W_77bec = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bf0 : bv 32 := 0x0006c803.
Lemma F_77bf0 : fetch_word AsanUbsan.M.loaded_segments (0x78008 : word) = Some W_77bf0.
Proof. vm_refl. Qed.
Lemma D_77bf0 : decode_any W_77bf0 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bf4 : bv 32 := 0x00168693.
Lemma F_77bf4 : fetch_word AsanUbsan.M.loaded_segments (0x7800c : word) = Some W_77bf4.
Proof. vm_refl. Qed.
Lemma D_77bf4 : decode_any W_77bf4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bf8 : bv 32 := 0x00f867b3.
Lemma F_77bf8 : fetch_word AsanUbsan.M.loaded_segments (0x78010 : word) = Some W_77bf8.
Proof. vm_refl. Qed.
Lemma D_77bf8 : decode_any W_77bf8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bfc : bv 32 := 0xfee69ae3.
Lemma F_77bfc : fetch_word AsanUbsan.M.loaded_segments (0x78014 : word) = Some W_77bfc.
Proof. vm_refl. Qed.
Lemma D_77bfc : decode_any W_77bfc = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c00 : bv 32 := 0x0ff7f693.
Lemma F_77c00 : fetch_word AsanUbsan.M.loaded_segments (0x78018 : word) = Some W_77c00.
Proof. vm_refl. Qed.
Lemma D_77c00 : decode_any W_77c00 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c04 : bv 32 := 0xd20680e3.
Lemma F_77c04 : fetch_word AsanUbsan.M.loaded_segments (0x7801c : word) = Some W_77c04.
Proof. vm_refl. Qed.
Lemma D_77c04 : decode_any W_77c04 = Some (Branch BC_EQ 13 0 7456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c08 : bv 32 := 0x00050a93.
Lemma F_77c08 : fetch_word AsanUbsan.M.loaded_segments (0x78020 : word) = Some W_77c08.
Proof. vm_refl. Qed.
Lemma D_77c08 : decode_any W_77c08 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c0c : bv 32 := 0x00058513.
Lemma F_77c0c : fetch_word AsanUbsan.M.loaded_segments (0x78024 : word) = Some W_77c0c.
Proof. vm_refl. Qed.
Lemma D_77c0c : decode_any W_77c0c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c10 : bv 32 := 0x00058b93.
Lemma F_77c10 : fetch_word AsanUbsan.M.loaded_segments (0x78028 : word) = Some W_77c10.
Proof. vm_refl. Qed.
Lemma D_77c10 : decode_any W_77c10 = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c14 : bv 32 := 0x00060593.
Lemma F_77c14 : fetch_word AsanUbsan.M.loaded_segments (0x7802c : word) = Some W_77c14.
Proof. vm_refl. Qed.
Lemma D_77c14 : decode_any W_77c14 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c18 : bv 32 := 0x00060493.
Lemma F_77c18 : fetch_word AsanUbsan.M.loaded_segments (0x78030 : word) = Some W_77c18.
Proof. vm_refl. Qed.
Lemma D_77c18 : decode_any W_77c18 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c1c : bv 32 := 0x48c030ef.
Lemma F_77c1c : fetch_word AsanUbsan.M.loaded_segments (0x78034 : word) = Some W_77c1c.
Proof. vm_refl. Qed.
Lemma D_77c1c : decode_any W_77c1c = Some (Jal 1 13452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c20 : bv 32 := 0x000b8593.
Lemma F_77c20 : fetch_word AsanUbsan.M.loaded_segments (0x78038 : word) = Some W_77c20.
Proof. vm_refl. Qed.
Lemma D_77c20 : decode_any W_77c20 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c24 : bv 32 := 0x00048613.
Lemma F_77c24 : fetch_word AsanUbsan.M.loaded_segments (0x7803c : word) = Some W_77c24.
Proof. vm_refl. Qed.
Lemma D_77c24 : decode_any W_77c24 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c28 : bv 32 := 0x00050913.
Lemma F_77c28 : fetch_word AsanUbsan.M.loaded_segments (0x78040 : word) = Some W_77c28.
Proof. vm_refl. Qed.
Lemma D_77c28 : decode_any W_77c28 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c2c : bv 32 := 0x000a8513.
Lemma F_77c2c : fetch_word AsanUbsan.M.loaded_segments (0x78044 : word) = Some W_77c2c.
Proof. vm_refl. Qed.
Lemma D_77c2c : decode_any W_77c2c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c30 : bv 32 := 0xce090ae3.
Lemma F_77c30 : fetch_word AsanUbsan.M.loaded_segments (0x78048 : word) = Some W_77c30.
Proof. vm_refl. Qed.
Lemma D_77c30 : decode_any W_77c30 = Some (Branch BC_EQ 18 0 7412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c78 : bv 32 := 0x00070783.
Lemma F_77c78 : fetch_word AsanUbsan.M.loaded_segments (0x78090 : word) = Some W_77c78.
Proof. vm_refl. Qed.
Lemma D_77c78 : decode_any W_77c78 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c7c : bv 32 := 0x0079f813.
Lemma F_77c7c : fetch_word AsanUbsan.M.loaded_segments (0x78094 : word) = Some W_77c7c.
Proof. vm_refl. Qed.
Lemma D_77c7c : decode_any W_77c7c = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c80 : bv 32 := 0x00f038b3.
Lemma F_77c80 : fetch_word AsanUbsan.M.loaded_segments (0x78098 : word) = Some W_77c80.
Proof. vm_refl. Qed.
Lemma D_77c80 : decode_any W_77c80 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c84 : bv 32 := 0x00f827b3.
Lemma F_77c84 : fetch_word AsanUbsan.M.loaded_segments (0x7809c : word) = Some W_77c84.
Proof. vm_refl. Qed.
Lemma D_77c84 : decode_any W_77c84 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c88 : bv 32 := 0x0017c793.
Lemma F_77c88 : fetch_word AsanUbsan.M.loaded_segments (0x780a0 : word) = Some W_77c88.
Proof. vm_refl. Qed.
Lemma D_77c88 : decode_any W_77c88 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c8c : bv 32 := 0x00f8f7b3.
Lemma F_77c8c : fetch_word AsanUbsan.M.loaded_segments (0x780a4 : word) = Some W_77c8c.
Proof. vm_refl. Qed.
Lemma D_77c8c : decode_any W_77c8c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c90 : bv 32 := 0x00e6fa63.
Lemma F_77c90 : fetch_word AsanUbsan.M.loaded_segments (0x780a8 : word) = Some W_77c90.
Proof. vm_refl. Qed.
Lemma D_77c90 : decode_any W_77c90 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c94 : bv 32 := 0x0006c803.
Lemma F_77c94 : fetch_word AsanUbsan.M.loaded_segments (0x780ac : word) = Some W_77c94.
Proof. vm_refl. Qed.
Lemma D_77c94 : decode_any W_77c94 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c98 : bv 32 := 0x00168693.
Lemma F_77c98 : fetch_word AsanUbsan.M.loaded_segments (0x780b0 : word) = Some W_77c98.
Proof. vm_refl. Qed.
Lemma D_77c98 : decode_any W_77c98 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c9c : bv 32 := 0x00f867b3.
Lemma F_77c9c : fetch_word AsanUbsan.M.loaded_segments (0x780b4 : word) = Some W_77c9c.
Proof. vm_refl. Qed.
Lemma D_77c9c : decode_any W_77c9c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ca0 : bv 32 := 0xfee69ae3.
Lemma F_77ca0 : fetch_word AsanUbsan.M.loaded_segments (0x780b8 : word) = Some W_77ca0.
Proof. vm_refl. Qed.
Lemma D_77ca0 : decode_any W_77ca0 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ca4 : bv 32 := 0x0ff7f693.
Lemma F_77ca4 : fetch_word AsanUbsan.M.loaded_segments (0x780bc : word) = Some W_77ca4.
Proof. vm_refl. Qed.
Lemma D_77ca4 : decode_any W_77ca4 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ca8 : bv 32 := 0xcc0682e3.
Lemma F_77ca8 : fetch_word AsanUbsan.M.loaded_segments (0x780c0 : word) = Some W_77ca8.
Proof. vm_refl. Qed.
Lemma D_77ca8 : decode_any W_77ca8 = Some (Branch BC_EQ 13 0 7364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cac : bv 32 := 0x00050493.
Lemma F_77cac : fetch_word AsanUbsan.M.loaded_segments (0x780c4 : word) = Some W_77cac.
Proof. vm_refl. Qed.
Lemma D_77cac : decode_any W_77cac = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cb0 : bv 32 := 0x00058a93.
Lemma F_77cb0 : fetch_word AsanUbsan.M.loaded_segments (0x780c8 : word) = Some W_77cb0.
Proof. vm_refl. Qed.
Lemma D_77cb0 : decode_any W_77cb0 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cb4 : bv 32 := 0x00060593.
Lemma F_77cb4 : fetch_word AsanUbsan.M.loaded_segments (0x780cc : word) = Some W_77cb4.
Proof. vm_refl. Qed.
Lemma D_77cb4 : decode_any W_77cb4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cb8 : bv 32 := 0x00060913.
Lemma F_77cb8 : fetch_word AsanUbsan.M.loaded_segments (0x780d0 : word) = Some W_77cb8.
Proof. vm_refl. Qed.
Lemma D_77cb8 : decode_any W_77cb8 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cbc : bv 32 := 0x3ec030ef.
Lemma F_77cbc : fetch_word AsanUbsan.M.loaded_segments (0x780d4 : word) = Some W_77cbc.
Proof. vm_refl. Qed.
Lemma D_77cbc : decode_any W_77cbc = Some (Jal 1 13292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cc0 : bv 32 := 0x000a8593.
Lemma F_77cc0 : fetch_word AsanUbsan.M.loaded_segments (0x780d8 : word) = Some W_77cc0.
Proof. vm_refl. Qed.
Lemma D_77cc0 : decode_any W_77cc0 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cc4 : bv 32 := 0x00090613.
Lemma F_77cc4 : fetch_word AsanUbsan.M.loaded_segments (0x780dc : word) = Some W_77cc4.
Proof. vm_refl. Qed.
Lemma D_77cc4 : decode_any W_77cc4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cc8 : bv 32 := 0x00050993.
Lemma F_77cc8 : fetch_word AsanUbsan.M.loaded_segments (0x780e0 : word) = Some W_77cc8.
Proof. vm_refl. Qed.
Lemma D_77cc8 : decode_any W_77cc8 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ccc : bv 32 := 0x00048513.
Lemma F_77ccc : fetch_word AsanUbsan.M.loaded_segments (0x780e4 : word) = Some W_77ccc.
Proof. vm_refl. Qed.
Lemma D_77ccc : decode_any W_77ccc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cd0 : bv 32 := 0xc8098ee3.
Lemma F_77cd0 : fetch_word AsanUbsan.M.loaded_segments (0x780e8 : word) = Some W_77cd0.
Proof. vm_refl. Qed.
Lemma D_77cd0 : decode_any W_77cd0 = Some (Branch BC_EQ 19 0 7324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d18 : bv 32 := 0x81010113.
Lemma F_77d18 : fetch_word AsanUbsan.M.loaded_segments (0x78130 : word) = Some W_77d18.
Proof. vm_refl. Qed.
Lemma D_77d18 : decode_any W_77d18 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d1c : bv 32 := 0x7e113423.
Lemma F_77d1c : fetch_word AsanUbsan.M.loaded_segments (0x78134 : word) = Some W_77d1c.
Proof. vm_refl. Qed.
Lemma D_77d1c : decode_any W_77d1c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d20 : bv 32 := 0x7e813023.
Lemma F_77d20 : fetch_word AsanUbsan.M.loaded_segments (0x78138 : word) = Some W_77d20.
Proof. vm_refl. Qed.
Lemma D_77d20 : decode_any W_77d20 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d24 : bv 32 := 0x7c913c23.
Lemma F_77d24 : fetch_word AsanUbsan.M.loaded_segments (0x7813c : word) = Some W_77d24.
Proof. vm_refl. Qed.
Lemma D_77d24 : decode_any W_77d24 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d28 : bv 32 := 0x7d213823.
Lemma F_77d28 : fetch_word AsanUbsan.M.loaded_segments (0x78140 : word) = Some W_77d28.
Proof. vm_refl. Qed.
Lemma D_77d28 : decode_any W_77d28 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d2c : bv 32 := 0x7d313423.
Lemma F_77d2c : fetch_word AsanUbsan.M.loaded_segments (0x78144 : word) = Some W_77d2c.
Proof. vm_refl. Qed.
Lemma D_77d2c : decode_any W_77d2c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d30 : bv 32 := 0x7d413023.
Lemma F_77d30 : fetch_word AsanUbsan.M.loaded_segments (0x78148 : word) = Some W_77d30.
Proof. vm_refl. Qed.
Lemma D_77d30 : decode_any W_77d30 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d34 : bv 32 := 0x7b513c23.
Lemma F_77d34 : fetch_word AsanUbsan.M.loaded_segments (0x7814c : word) = Some W_77d34.
Proof. vm_refl. Qed.
Lemma D_77d34 : decode_any W_77d34 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d38 : bv 32 := 0x7f010413.
Lemma F_77d38 : fetch_word AsanUbsan.M.loaded_segments (0x78150 : word) = Some W_77d38.
Proof. vm_refl. Qed.
Lemma D_77d38 : decode_any W_77d38 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d3c : bv 32 := 0xfa010113.
Lemma F_77d3c : fetch_word AsanUbsan.M.loaded_segments (0x78154 : word) = Some W_77d3c.
Proof. vm_refl. Qed.
Lemma D_77d3c : decode_any W_77d3c = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d40 : bv 32 := 0x000c0697.
Lemma F_77d40 : fetch_word AsanUbsan.M.loaded_segments (0x78158 : word) = Some W_77d40.
Proof. vm_refl. Qed.
Lemma D_77d40 : decode_any W_77d40 = Some (Auipc 13 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d44 : bv 32 := 0xed06b683.
Lemma F_77d44 : fetch_word AsanUbsan.M.loaded_segments (0x7815c : word) = Some W_77d44.
Proof. vm_refl. Qed.
Lemma D_77d44 : decode_any W_77d44 = Some (Load SZ8 true 13 13 3792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d48 : bv 32 := 0x0006c683.
Lemma F_77d48 : fetch_word AsanUbsan.M.loaded_segments (0x78160 : word) = Some W_77d48.
Proof. vm_refl. Qed.
Lemma D_77d48 : decode_any W_77d48 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d4c : bv 32 := 0x08068863.
Lemma F_77d4c : fetch_word AsanUbsan.M.loaded_segments (0x78164 : word) = Some W_77d4c.
Proof. vm_refl. Qed.
Lemma D_77d4c : decode_any W_77d4c = Some (Branch BC_EQ 13 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d50 : bv 32 := 0xfff54693.
Lemma F_77d50 : fetch_word AsanUbsan.M.loaded_segments (0x78168 : word) = Some W_77d50.
Proof. vm_refl. Qed.
Lemma D_77d50 : decode_any W_77d50 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d54 : bv 32 := 0x80040a13.
Lemma F_77d54 : fetch_word AsanUbsan.M.loaded_segments (0x7816c : word) = Some W_77d54.
Proof. vm_refl. Qed.
Lemma D_77d54 : decode_any W_77d54 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d58 : bv 32 := 0xfb0a0a13.
Lemma F_77d58 : fetch_word AsanUbsan.M.loaded_segments (0x78170 : word) = Some W_77d58.
Proof. vm_refl. Qed.
Lemma D_77d58 : decode_any W_77d58 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d5c : bv 32 := 0x0cc6e663.
Lemma F_77d5c : fetch_word AsanUbsan.M.loaded_segments (0x78174 : word) = Some W_77d5c.
Proof. vm_refl. Qed.
Lemma D_77d5c : decode_any W_77d5c = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d60 : bv 32 := 0xfbf60693.
Lemma F_77d60 : fetch_word AsanUbsan.M.loaded_segments (0x78178 : word) = Some W_77d60.
Proof. vm_refl. Qed.
Lemma D_77d60 : decode_any W_77d60 = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d64 : bv 32 := 0xfbf00713.
Lemma F_77d64 : fetch_word AsanUbsan.M.loaded_segments (0x7817c : word) = Some W_77d64.
Proof. vm_refl. Qed.
Lemma D_77d64 : decode_any W_77d64 = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d68 : bv 32 := 0x14d77463.
Lemma F_77d68 : fetch_word AsanUbsan.M.loaded_segments (0x78180 : word) = Some W_77d68.
Proof. vm_refl. Qed.
Lemma D_77d68 : decode_any W_77d68 = Some (Branch BC_GEU 14 13 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d6c : bv 32 := 0x000bf697.
Lemma F_77d6c : fetch_word AsanUbsan.M.loaded_segments (0x78184 : word) = Some W_77d6c.
Proof. vm_refl. Qed.
Lemma D_77d6c : decode_any W_77d6c = Some (Auipc 13 191, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d70 : bv 32 := 0x33c6b683.
Lemma F_77d70 : fetch_word AsanUbsan.M.loaded_segments (0x78188 : word) = Some W_77d70.
Proof. vm_refl. Qed.
Lemma D_77d70 : decode_any W_77d70 = Some (Load SZ8 true 13 13 828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d74 : bv 32 := 0x00c507b3.
Lemma F_77d74 : fetch_word AsanUbsan.M.loaded_segments (0x7818c : word) = Some W_77d74.
Proof. vm_refl. Qed.
Lemma D_77d74 : decode_any W_77d74 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d78 : bv 32 := 0x0006b703.
Lemma F_77d78 : fetch_word AsanUbsan.M.loaded_segments (0x78190 : word) = Some W_77d78.
Proof. vm_refl. Qed.
Lemma D_77d78 : decode_any W_77d78 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d7c : bv 32 := 0x00355693.
Lemma F_77d7c : fetch_word AsanUbsan.M.loaded_segments (0x78194 : word) = Some W_77d7c.
Proof. vm_refl. Qed.
Lemma D_77d7c : decode_any W_77d7c = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d80 : bv 32 := 0xfff78793.
Lemma F_77d80 : fetch_word AsanUbsan.M.loaded_segments (0x78198 : word) = Some W_77d80.
Proof. vm_refl. Qed.
Lemma D_77d80 : decode_any W_77d80 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d84 : bv 32 := 0x0037d813.
Lemma F_77d84 : fetch_word AsanUbsan.M.loaded_segments (0x7819c : word) = Some W_77d84.
Proof. vm_refl. Qed.
Lemma D_77d84 : decode_any W_77d84 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d88 : bv 32 := 0x00d706b3.
Lemma F_77d88 : fetch_word AsanUbsan.M.loaded_segments (0x781a0 : word) = Some W_77d88.
Proof. vm_refl. Qed.
Lemma D_77d88 : decode_any W_77d88 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d8c : bv 32 := 0x01070733.
Lemma F_77d8c : fetch_word AsanUbsan.M.loaded_segments (0x781a4 : word) = Some W_77d8c.
Proof. vm_refl. Qed.
Lemma D_77d8c : decode_any W_77d8c = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d90 : bv 32 := 0xff86f813.
Lemma F_77d90 : fetch_word AsanUbsan.M.loaded_segments (0x781a8 : word) = Some W_77d90.
Proof. vm_refl. Qed.
Lemma D_77d90 : decode_any W_77d90 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d94 : bv 32 := 0xff877893.
Lemma F_77d94 : fetch_word AsanUbsan.M.loaded_segments (0x781ac : word) = Some W_77d94.
Proof. vm_refl. Qed.
Lemma D_77d94 : decode_any W_77d94 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d98 : bv 32 := 0x00083803.
Lemma F_77d98 : fetch_word AsanUbsan.M.loaded_segments (0x781b0 : word) = Some W_77d98.
Proof. vm_refl. Qed.
Lemma D_77d98 : decode_any W_77d98 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d9c : bv 32 := 0x0008b883.
Lemma F_77d9c : fetch_word AsanUbsan.M.loaded_segments (0x781b4 : word) = Some W_77d9c.
Proof. vm_refl. Qed.
Lemma D_77d9c : decode_any W_77d9c = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77da0 : bv 32 := 0x0108e833.
Lemma F_77da0 : fetch_word AsanUbsan.M.loaded_segments (0x781b8 : word) = Some W_77da0.
Proof. vm_refl. Qed.
Lemma D_77da0 : decode_any W_77da0 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77da4 : bv 32 := 0x10081a63.
Lemma F_77da4 : fetch_word AsanUbsan.M.loaded_segments (0x781bc : word) = Some W_77da4.
Proof. vm_refl. Qed.
Lemma D_77da4 : decode_any W_77da4 = Some (Branch BC_NE 16 0 276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77da8 : bv 32 := 0x000c1697.
Lemma F_77da8 : fetch_word AsanUbsan.M.loaded_segments (0x781c0 : word) = Some W_77da8.
Proof. vm_refl. Qed.
Lemma D_77da8 : decode_any W_77da8 = Some (Auipc 13 193, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77dac : bv 32 := 0x3106b683.
Lemma F_77dac : fetch_word AsanUbsan.M.loaded_segments (0x781c4 : word) = Some W_77dac.
Proof. vm_refl. Qed.
Lemma D_77dac : decode_any W_77dac = Some (Load SZ8 true 13 13 784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77db0 : bv 32 := 0x000680e7.
Lemma F_77db0 : fetch_word AsanUbsan.M.loaded_segments (0x781c8 : word) = Some W_77db0.
Proof. vm_refl. Qed.
Lemma D_77db0 : decode_any W_77db0 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77db4 : bv 32 := 0x06010113.
Lemma F_77db4 : fetch_word AsanUbsan.M.loaded_segments (0x781cc : word) = Some W_77db4.
Proof. vm_refl. Qed.
Lemma D_77db4 : decode_any W_77db4 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77db8 : bv 32 := 0x7e813083.
Lemma F_77db8 : fetch_word AsanUbsan.M.loaded_segments (0x781d0 : word) = Some W_77db8.
Proof. vm_refl. Qed.
Lemma D_77db8 : decode_any W_77db8 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77dbc : bv 32 := 0x7e013403.
Lemma F_77dbc : fetch_word AsanUbsan.M.loaded_segments (0x781d4 : word) = Some W_77dbc.
Proof. vm_refl. Qed.
Lemma D_77dbc : decode_any W_77dbc = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77dc0 : bv 32 := 0x7d813483.
Lemma F_77dc0 : fetch_word AsanUbsan.M.loaded_segments (0x781d8 : word) = Some W_77dc0.
Proof. vm_refl. Qed.
Lemma D_77dc0 : decode_any W_77dc0 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77dc4 : bv 32 := 0x7d013903.
Lemma F_77dc4 : fetch_word AsanUbsan.M.loaded_segments (0x781dc : word) = Some W_77dc4.
Proof. vm_refl. Qed.
Lemma D_77dc4 : decode_any W_77dc4 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77dc8 : bv 32 := 0x7c813983.
Lemma F_77dc8 : fetch_word AsanUbsan.M.loaded_segments (0x781e0 : word) = Some W_77dc8.
Proof. vm_refl. Qed.
Lemma D_77dc8 : decode_any W_77dc8 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77dcc : bv 32 := 0x7c013a03.
Lemma F_77dcc : fetch_word AsanUbsan.M.loaded_segments (0x781e4 : word) = Some W_77dcc.
Proof. vm_refl. Qed.
Lemma D_77dcc : decode_any W_77dcc = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77dd0 : bv 32 := 0x7b813a83.
Lemma F_77dd0 : fetch_word AsanUbsan.M.loaded_segments (0x781e8 : word) = Some W_77dd0.
Proof. vm_refl. Qed.
Lemma D_77dd0 : decode_any W_77dd0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77dd4 : bv 32 := 0x7f010113.
Lemma F_77dd4 : fetch_word AsanUbsan.M.loaded_segments (0x781ec : word) = Some W_77dd4.
Proof. vm_refl. Qed.
Lemma D_77dd4 : decode_any W_77dd4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77dd8 : bv 32 := 0x00008067.
Lemma F_77dd8 : fetch_word AsanUbsan.M.loaded_segments (0x781f0 : word) = Some W_77dd8.
Proof. vm_refl. Qed.
Lemma D_77dd8 : decode_any W_77dd8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77eb0 : bv 32 := 0x02061e63.
Lemma F_77eb0 : fetch_word AsanUbsan.M.loaded_segments (0x782c8 : word) = Some W_77eb0.
Proof. vm_refl. Qed.
Lemma D_77eb0 : decode_any W_77eb0 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77eb4 : bv 32 := 0xef5ff06f.
Lemma F_77eb4 : fetch_word AsanUbsan.M.loaded_segments (0x782cc : word) = Some W_77eb4.
Proof. vm_refl. Qed.
Lemma D_77eb4 : decode_any W_77eb4 = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77eb8 : bv 32 := 0x00070803.
Lemma F_77eb8 : fetch_word AsanUbsan.M.loaded_segments (0x782d0 : word) = Some W_77eb8.
Proof. vm_refl. Qed.
Lemma D_77eb8 : decode_any W_77eb8 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ebc : bv 32 := 0x0077f793.
Lemma F_77ebc : fetch_word AsanUbsan.M.loaded_segments (0x782d4 : word) = Some W_77ebc.
Proof. vm_refl. Qed.
Lemma D_77ebc : decode_any W_77ebc = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ec0 : bv 32 := 0x010038b3.
Lemma F_77ec0 : fetch_word AsanUbsan.M.loaded_segments (0x782d8 : word) = Some W_77ec0.
Proof. vm_refl. Qed.
Lemma D_77ec0 : decode_any W_77ec0 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ec4 : bv 32 := 0x0107a7b3.
Lemma F_77ec4 : fetch_word AsanUbsan.M.loaded_segments (0x782dc : word) = Some W_77ec4.
Proof. vm_refl. Qed.
Lemma D_77ec4 : decode_any W_77ec4 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ec8 : bv 32 := 0x0017c793.
Lemma F_77ec8 : fetch_word AsanUbsan.M.loaded_segments (0x782e0 : word) = Some W_77ec8.
Proof. vm_refl. Qed.
Lemma D_77ec8 : decode_any W_77ec8 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ecc : bv 32 := 0x00f8f7b3.
Lemma F_77ecc : fetch_word AsanUbsan.M.loaded_segments (0x782e4 : word) = Some W_77ecc.
Proof. vm_refl. Qed.
Lemma D_77ecc : decode_any W_77ecc = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ed0 : bv 32 := 0x00e6fa63.
Lemma F_77ed0 : fetch_word AsanUbsan.M.loaded_segments (0x782e8 : word) = Some W_77ed0.
Proof. vm_refl. Qed.
Lemma D_77ed0 : decode_any W_77ed0 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ed4 : bv 32 := 0x0006c803.
Lemma F_77ed4 : fetch_word AsanUbsan.M.loaded_segments (0x782ec : word) = Some W_77ed4.
Proof. vm_refl. Qed.
Lemma D_77ed4 : decode_any W_77ed4 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ed8 : bv 32 := 0x00168693.
Lemma F_77ed8 : fetch_word AsanUbsan.M.loaded_segments (0x782f0 : word) = Some W_77ed8.
Proof. vm_refl. Qed.
Lemma D_77ed8 : decode_any W_77ed8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77edc : bv 32 := 0x00f867b3.
Lemma F_77edc : fetch_word AsanUbsan.M.loaded_segments (0x782f4 : word) = Some W_77edc.
Proof. vm_refl. Qed.
Lemma D_77edc : decode_any W_77edc = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ee0 : bv 32 := 0xfee69ae3.
Lemma F_77ee0 : fetch_word AsanUbsan.M.loaded_segments (0x782f8 : word) = Some W_77ee0.
Proof. vm_refl. Qed.
Lemma D_77ee0 : decode_any W_77ee0 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ee4 : bv 32 := 0x0ff7f693.
Lemma F_77ee4 : fetch_word AsanUbsan.M.loaded_segments (0x782fc : word) = Some W_77ee4.
Proof. vm_refl. Qed.
Lemma D_77ee4 : decode_any W_77ee4 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ee8 : bv 32 := 0xec0680e3.
Lemma F_77ee8 : fetch_word AsanUbsan.M.loaded_segments (0x78300 : word) = Some W_77ee8.
Proof. vm_refl. Qed.
Lemma D_77ee8 : decode_any W_77ee8 = Some (Branch BC_EQ 13 0 7872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77eec : bv 32 := 0x00050493.
Lemma F_77eec : fetch_word AsanUbsan.M.loaded_segments (0x78304 : word) = Some W_77eec.
Proof. vm_refl. Qed.
Lemma D_77eec : decode_any W_77eec = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ef0 : bv 32 := 0x00058a93.
Lemma F_77ef0 : fetch_word AsanUbsan.M.loaded_segments (0x78308 : word) = Some W_77ef0.
Proof. vm_refl. Qed.
Lemma D_77ef0 : decode_any W_77ef0 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ef4 : bv 32 := 0x00060593.
Lemma F_77ef4 : fetch_word AsanUbsan.M.loaded_segments (0x7830c : word) = Some W_77ef4.
Proof. vm_refl. Qed.
Lemma D_77ef4 : decode_any W_77ef4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ef8 : bv 32 := 0x00060913.
Lemma F_77ef8 : fetch_word AsanUbsan.M.loaded_segments (0x78310 : word) = Some W_77ef8.
Proof. vm_refl. Qed.
Lemma D_77ef8 : decode_any W_77ef8 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77efc : bv 32 := 0x1ac030ef.
Lemma F_77efc : fetch_word AsanUbsan.M.loaded_segments (0x78314 : word) = Some W_77efc.
Proof. vm_refl. Qed.
Lemma D_77efc : decode_any W_77efc = Some (Jal 1 12716, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f00 : bv 32 := 0x000a8593.
Lemma F_77f00 : fetch_word AsanUbsan.M.loaded_segments (0x78318 : word) = Some W_77f00.
Proof. vm_refl. Qed.
Lemma D_77f00 : decode_any W_77f00 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f04 : bv 32 := 0x00090613.
Lemma F_77f04 : fetch_word AsanUbsan.M.loaded_segments (0x7831c : word) = Some W_77f04.
Proof. vm_refl. Qed.
Lemma D_77f04 : decode_any W_77f04 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f08 : bv 32 := 0x00050993.
Lemma F_77f08 : fetch_word AsanUbsan.M.loaded_segments (0x78320 : word) = Some W_77f08.
Proof. vm_refl. Qed.
Lemma D_77f08 : decode_any W_77f08 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f0c : bv 32 := 0x00048513.
Lemma F_77f0c : fetch_word AsanUbsan.M.loaded_segments (0x78324 : word) = Some W_77f0c.
Proof. vm_refl. Qed.
Lemma D_77f0c : decode_any W_77f0c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f10 : bv 32 := 0xe8098ce3.
Lemma F_77f10 : fetch_word AsanUbsan.M.loaded_segments (0x78328 : word) = Some W_77f10.
Proof. vm_refl. Qed.
Lemma D_77f10 : decode_any W_77f10 = Some (Branch BC_EQ 19 0 7832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f58 : bv 32 := 0x81010113.
Lemma F_77f58 : fetch_word AsanUbsan.M.loaded_segments (0x78370 : word) = Some W_77f58.
Proof. vm_refl. Qed.
Lemma D_77f58 : decode_any W_77f58 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f5c : bv 32 := 0x7e113423.
Lemma F_77f5c : fetch_word AsanUbsan.M.loaded_segments (0x78374 : word) = Some W_77f5c.
Proof. vm_refl. Qed.
Lemma D_77f5c : decode_any W_77f5c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f60 : bv 32 := 0x7e813023.
Lemma F_77f60 : fetch_word AsanUbsan.M.loaded_segments (0x78378 : word) = Some W_77f60.
Proof. vm_refl. Qed.
Lemma D_77f60 : decode_any W_77f60 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f64 : bv 32 := 0x7c913c23.
Lemma F_77f64 : fetch_word AsanUbsan.M.loaded_segments (0x7837c : word) = Some W_77f64.
Proof. vm_refl. Qed.
Lemma D_77f64 : decode_any W_77f64 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f68 : bv 32 := 0x7d213823.
Lemma F_77f68 : fetch_word AsanUbsan.M.loaded_segments (0x78380 : word) = Some W_77f68.
Proof. vm_refl. Qed.
Lemma D_77f68 : decode_any W_77f68 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f6c : bv 32 := 0x7d313423.
Lemma F_77f6c : fetch_word AsanUbsan.M.loaded_segments (0x78384 : word) = Some W_77f6c.
Proof. vm_refl. Qed.
Lemma D_77f6c : decode_any W_77f6c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f70 : bv 32 := 0x7d413023.
Lemma F_77f70 : fetch_word AsanUbsan.M.loaded_segments (0x78388 : word) = Some W_77f70.
Proof. vm_refl. Qed.
Lemma D_77f70 : decode_any W_77f70 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f74 : bv 32 := 0x7b513c23.
Lemma F_77f74 : fetch_word AsanUbsan.M.loaded_segments (0x7838c : word) = Some W_77f74.
Proof. vm_refl. Qed.
Lemma D_77f74 : decode_any W_77f74 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f78 : bv 32 := 0x7b613823.
Lemma F_77f78 : fetch_word AsanUbsan.M.loaded_segments (0x78390 : word) = Some W_77f78.
Proof. vm_refl. Qed.
Lemma D_77f78 : decode_any W_77f78 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f7c : bv 32 := 0x7f010413.
Lemma F_77f7c : fetch_word AsanUbsan.M.loaded_segments (0x78394 : word) = Some W_77f7c.
Proof. vm_refl. Qed.
Lemma D_77f7c : decode_any W_77f7c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f80 : bv 32 := 0xf9010113.
Lemma F_77f80 : fetch_word AsanUbsan.M.loaded_segments (0x78398 : word) = Some W_77f80.
Proof. vm_refl. Qed.
Lemma D_77f80 : decode_any W_77f80 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f84 : bv 32 := 0x000c0697.
Lemma F_77f84 : fetch_word AsanUbsan.M.loaded_segments (0x7839c : word) = Some W_77f84.
Proof. vm_refl. Qed.
Lemma D_77f84 : decode_any W_77f84 = Some (Auipc 13 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f88 : bv 32 := 0xc8c6b683.
Lemma F_77f88 : fetch_word AsanUbsan.M.loaded_segments (0x783a0 : word) = Some W_77f88.
Proof. vm_refl. Qed.
Lemma D_77f88 : decode_any W_77f88 = Some (Load SZ8 true 13 13 3212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f8c : bv 32 := 0x0006c683.
Lemma F_77f8c : fetch_word AsanUbsan.M.loaded_segments (0x783a4 : word) = Some W_77f8c.
Proof. vm_refl. Qed.
Lemma D_77f8c : decode_any W_77f8c = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f90 : bv 32 := 0x0a068463.
Lemma F_77f90 : fetch_word AsanUbsan.M.loaded_segments (0x783a8 : word) = Some W_77f90.
Proof. vm_refl. Qed.
Lemma D_77f90 : decode_any W_77f90 = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f94 : bv 32 := 0xfff5c693.
Lemma F_77f94 : fetch_word AsanUbsan.M.loaded_segments (0x783ac : word) = Some W_77f94.
Proof. vm_refl. Qed.
Lemma D_77f94 : decode_any W_77f94 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f98 : bv 32 := 0x80040a13.
Lemma F_77f98 : fetch_word AsanUbsan.M.loaded_segments (0x783b0 : word) = Some W_77f98.
Proof. vm_refl. Qed.
Lemma D_77f98 : decode_any W_77f98 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f9c : bv 32 := 0xfa8a0a13.
Lemma F_77f9c : fetch_word AsanUbsan.M.loaded_segments (0x783b4 : word) = Some W_77f9c.
Proof. vm_refl. Qed.
Lemma D_77f9c : decode_any W_77f9c = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fa0 : bv 32 := 0x0cc6e463.
Lemma F_77fa0 : fetch_word AsanUbsan.M.loaded_segments (0x783b8 : word) = Some W_77fa0.
Proof. vm_refl. Qed.
Lemma D_77fa0 : decode_any W_77fa0 = Some (Branch BC_LTU 13 12 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fa4 : bv 32 := 0xfbf60993.
Lemma F_77fa4 : fetch_word AsanUbsan.M.loaded_segments (0x783bc : word) = Some W_77fa4.
Proof. vm_refl. Qed.
Lemma D_77fa4 : decode_any W_77fa4 = Some (OpImm ALU_ADD 19 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fa8 : bv 32 := 0xfbf00693.
Lemma F_77fa8 : fetch_word AsanUbsan.M.loaded_segments (0x783c0 : word) = Some W_77fa8.
Proof. vm_refl. Qed.
Lemma D_77fa8 : decode_any W_77fa8 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fac : bv 32 := 0x1536f263.
Lemma F_77fac : fetch_word AsanUbsan.M.loaded_segments (0x783c4 : word) = Some W_77fac.
Proof. vm_refl. Qed.
Lemma D_77fac : decode_any W_77fac = Some (Branch BC_GEU 13 19 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fb0 : bv 32 := 0x000bf697.
Lemma F_77fb0 : fetch_word AsanUbsan.M.loaded_segments (0x783c8 : word) = Some W_77fb0.
Proof. vm_refl. Qed.
Lemma D_77fb0 : decode_any W_77fb0 = Some (Auipc 13 191, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fb4 : bv 32 := 0x0f86b683.
Lemma F_77fb4 : fetch_word AsanUbsan.M.loaded_segments (0x783cc : word) = Some W_77fb4.
Proof. vm_refl. Qed.
Lemma D_77fb4 : decode_any W_77fb4 = Some (Load SZ8 true 13 13 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fb8 : bv 32 := 0x00c587b3.
Lemma F_77fb8 : fetch_word AsanUbsan.M.loaded_segments (0x783d0 : word) = Some W_77fb8.
Proof. vm_refl. Qed.
Lemma D_77fb8 : decode_any W_77fb8 = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fbc : bv 32 := 0x0006b703.
Lemma F_77fbc : fetch_word AsanUbsan.M.loaded_segments (0x783d4 : word) = Some W_77fbc.
Proof. vm_refl. Qed.
Lemma D_77fbc : decode_any W_77fbc = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fc0 : bv 32 := 0x0035d693.
Lemma F_77fc0 : fetch_word AsanUbsan.M.loaded_segments (0x783d8 : word) = Some W_77fc0.
Proof. vm_refl. Qed.
Lemma D_77fc0 : decode_any W_77fc0 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fc4 : bv 32 := 0xfff78793.
Lemma F_77fc4 : fetch_word AsanUbsan.M.loaded_segments (0x783dc : word) = Some W_77fc4.
Proof. vm_refl. Qed.
Lemma D_77fc4 : decode_any W_77fc4 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fc8 : bv 32 := 0x0037d813.
Lemma F_77fc8 : fetch_word AsanUbsan.M.loaded_segments (0x783e0 : word) = Some W_77fc8.
Proof. vm_refl. Qed.
Lemma D_77fc8 : decode_any W_77fc8 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fcc : bv 32 := 0x00d706b3.
Lemma F_77fcc : fetch_word AsanUbsan.M.loaded_segments (0x783e4 : word) = Some W_77fcc.
Proof. vm_refl. Qed.
Lemma D_77fcc : decode_any W_77fcc = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fd0 : bv 32 := 0x01070733.
Lemma F_77fd0 : fetch_word AsanUbsan.M.loaded_segments (0x783e8 : word) = Some W_77fd0.
Proof. vm_refl. Qed.
Lemma D_77fd0 : decode_any W_77fd0 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fd4 : bv 32 := 0xff86f813.
Lemma F_77fd4 : fetch_word AsanUbsan.M.loaded_segments (0x783ec : word) = Some W_77fd4.
Proof. vm_refl. Qed.
Lemma D_77fd4 : decode_any W_77fd4 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fd8 : bv 32 := 0xff877893.
Lemma F_77fd8 : fetch_word AsanUbsan.M.loaded_segments (0x783f0 : word) = Some W_77fd8.
Proof. vm_refl. Qed.
Lemma D_77fd8 : decode_any W_77fd8 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fdc : bv 32 := 0x00083803.
Lemma F_77fdc : fetch_word AsanUbsan.M.loaded_segments (0x783f4 : word) = Some W_77fdc.
Proof. vm_refl. Qed.
Lemma D_77fdc : decode_any W_77fdc = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fe0 : bv 32 := 0x0008b883.
Lemma F_77fe0 : fetch_word AsanUbsan.M.loaded_segments (0x783f8 : word) = Some W_77fe0.
Proof. vm_refl. Qed.
Lemma D_77fe0 : decode_any W_77fe0 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fe4 : bv 32 := 0x0108e833.
Lemma F_77fe4 : fetch_word AsanUbsan.M.loaded_segments (0x783fc : word) = Some W_77fe4.
Proof. vm_refl. Qed.
Lemma D_77fe4 : decode_any W_77fe4 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fe8 : bv 32 := 0x18081e63.
Lemma F_77fe8 : fetch_word AsanUbsan.M.loaded_segments (0x78400 : word) = Some W_77fe8.
Proof. vm_refl. Qed.
Lemma D_77fe8 : decode_any W_77fe8 = Some (Branch BC_NE 16 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77fec : bv 32 := 0xfff54693.
Lemma F_77fec : fetch_word AsanUbsan.M.loaded_segments (0x78404 : word) = Some W_77fec.
Proof. vm_refl. Qed.
Lemma D_77fec : decode_any W_77fec = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ff0 : bv 32 := 0x10c6e463.
Lemma F_77ff0 : fetch_word AsanUbsan.M.loaded_segments (0x78408 : word) = Some W_77ff0.
Proof. vm_refl. Qed.
Lemma D_77ff0 : decode_any W_77ff0 = Some (Branch BC_LTU 13 12 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ff4 : bv 32 := 0xfbf00693.
Lemma F_77ff4 : fetch_word AsanUbsan.M.loaded_segments (0x7840c : word) = Some W_77ff4.
Proof. vm_refl. Qed.
Lemma D_77ff4 : decode_any W_77ff4 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ff8 : bv 32 := 0x1936f263.
Lemma F_77ff8 : fetch_word AsanUbsan.M.loaded_segments (0x78410 : word) = Some W_77ff8.
Proof. vm_refl. Qed.
Lemma D_77ff8 : decode_any W_77ff8 = Some (Branch BC_GEU 13 19 388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ffc : bv 32 := 0x000bf697.
Lemma F_77ffc : fetch_word AsanUbsan.M.loaded_segments (0x78414 : word) = Some W_77ffc.
Proof. vm_refl. Qed.
Lemma D_77ffc : decode_any W_77ffc = Some (Auipc 13 191, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78000 : bv 32 := 0x0ac6b683.
Lemma F_78000 : fetch_word AsanUbsan.M.loaded_segments (0x78418 : word) = Some W_78000.
Proof. vm_refl. Qed.
Lemma D_78000 : decode_any W_78000 = Some (Load SZ8 true 13 13 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78004 : bv 32 := 0x00c507b3.
Lemma F_78004 : fetch_word AsanUbsan.M.loaded_segments (0x7841c : word) = Some W_78004.
Proof. vm_refl. Qed.
Lemma D_78004 : decode_any W_78004 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78008 : bv 32 := 0x0006b703.
Lemma F_78008 : fetch_word AsanUbsan.M.loaded_segments (0x78420 : word) = Some W_78008.
Proof. vm_refl. Qed.
Lemma D_78008 : decode_any W_78008 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7800c : bv 32 := 0x00355693.
Lemma F_7800c : fetch_word AsanUbsan.M.loaded_segments (0x78424 : word) = Some W_7800c.
Proof. vm_refl. Qed.
Lemma D_7800c : decode_any W_7800c = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78010 : bv 32 := 0xfff78793.
Lemma F_78010 : fetch_word AsanUbsan.M.loaded_segments (0x78428 : word) = Some W_78010.
Proof. vm_refl. Qed.
Lemma D_78010 : decode_any W_78010 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78014 : bv 32 := 0x0037d813.
Lemma F_78014 : fetch_word AsanUbsan.M.loaded_segments (0x7842c : word) = Some W_78014.
Proof. vm_refl. Qed.
Lemma D_78014 : decode_any W_78014 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78018 : bv 32 := 0x00d706b3.
Lemma F_78018 : fetch_word AsanUbsan.M.loaded_segments (0x78430 : word) = Some W_78018.
Proof. vm_refl. Qed.
Lemma D_78018 : decode_any W_78018 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7801c : bv 32 := 0x01070733.
Lemma F_7801c : fetch_word AsanUbsan.M.loaded_segments (0x78434 : word) = Some W_7801c.
Proof. vm_refl. Qed.
Lemma D_7801c : decode_any W_7801c = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78020 : bv 32 := 0xff86f813.
Lemma F_78020 : fetch_word AsanUbsan.M.loaded_segments (0x78438 : word) = Some W_78020.
Proof. vm_refl. Qed.
Lemma D_78020 : decode_any W_78020 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78024 : bv 32 := 0xff877893.
Lemma F_78024 : fetch_word AsanUbsan.M.loaded_segments (0x7843c : word) = Some W_78024.
Proof. vm_refl. Qed.
Lemma D_78024 : decode_any W_78024 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78028 : bv 32 := 0x00083803.
Lemma F_78028 : fetch_word AsanUbsan.M.loaded_segments (0x78440 : word) = Some W_78028.
Proof. vm_refl. Qed.
Lemma D_78028 : decode_any W_78028 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7802c : bv 32 := 0x0008b883.
Lemma F_7802c : fetch_word AsanUbsan.M.loaded_segments (0x78444 : word) = Some W_7802c.
Proof. vm_refl. Qed.
Lemma D_7802c : decode_any W_7802c = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78030 : bv 32 := 0x0108e833.
Lemma F_78030 : fetch_word AsanUbsan.M.loaded_segments (0x78448 : word) = Some W_78030.
Proof. vm_refl. Qed.
Lemma D_78030 : decode_any W_78030 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78034 : bv 32 := 0x1e081a63.
Lemma F_78034 : fetch_word AsanUbsan.M.loaded_segments (0x7844c : word) = Some W_78034.
Proof. vm_refl. Qed.
Lemma D_78034 : decode_any W_78034 = Some (Branch BC_NE 16 0 500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78038 : bv 32 := 0x7b9120ef.
Lemma F_78038 : fetch_word AsanUbsan.M.loaded_segments (0x78450 : word) = Some W_78038.
Proof. vm_refl. Qed.
Lemma D_78038 : decode_any W_78038 = Some (Jal 1 77752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7803c : bv 32 := 0x07010113.
Lemma F_7803c : fetch_word AsanUbsan.M.loaded_segments (0x78454 : word) = Some W_7803c.
Proof. vm_refl. Qed.
Lemma D_7803c : decode_any W_7803c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78040 : bv 32 := 0x7e813083.
Lemma F_78040 : fetch_word AsanUbsan.M.loaded_segments (0x78458 : word) = Some W_78040.
Proof. vm_refl. Qed.
Lemma D_78040 : decode_any W_78040 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78044 : bv 32 := 0x7e013403.
Lemma F_78044 : fetch_word AsanUbsan.M.loaded_segments (0x7845c : word) = Some W_78044.
Proof. vm_refl. Qed.
Lemma D_78044 : decode_any W_78044 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78048 : bv 32 := 0x7d813483.
Lemma F_78048 : fetch_word AsanUbsan.M.loaded_segments (0x78460 : word) = Some W_78048.
Proof. vm_refl. Qed.
Lemma D_78048 : decode_any W_78048 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7804c : bv 32 := 0x7d013903.
Lemma F_7804c : fetch_word AsanUbsan.M.loaded_segments (0x78464 : word) = Some W_7804c.
Proof. vm_refl. Qed.
Lemma D_7804c : decode_any W_7804c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78050 : bv 32 := 0x7c813983.
Lemma F_78050 : fetch_word AsanUbsan.M.loaded_segments (0x78468 : word) = Some W_78050.
Proof. vm_refl. Qed.
Lemma D_78050 : decode_any W_78050 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78054 : bv 32 := 0x7c013a03.
Lemma F_78054 : fetch_word AsanUbsan.M.loaded_segments (0x7846c : word) = Some W_78054.
Proof. vm_refl. Qed.
Lemma D_78054 : decode_any W_78054 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78058 : bv 32 := 0x7b813a83.
Lemma F_78058 : fetch_word AsanUbsan.M.loaded_segments (0x78470 : word) = Some W_78058.
Proof. vm_refl. Qed.
Lemma D_78058 : decode_any W_78058 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7805c : bv 32 := 0x7b013b03.
Lemma F_7805c : fetch_word AsanUbsan.M.loaded_segments (0x78474 : word) = Some W_7805c.
Proof. vm_refl. Qed.
Lemma D_7805c : decode_any W_7805c = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78060 : bv 32 := 0x7f010113.
Lemma F_78060 : fetch_word AsanUbsan.M.loaded_segments (0x78478 : word) = Some W_78060.
Proof. vm_refl. Qed.
Lemma D_78060 : decode_any W_78060 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78064 : bv 32 := 0x00008067.
Lemma F_78064 : fetch_word AsanUbsan.M.loaded_segments (0x7847c : word) = Some W_78064.
Proof. vm_refl. Qed.
Lemma D_78064 : decode_any W_78064 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780f0 : bv 32 := 0x0c061463.
Lemma F_780f0 : fetch_word AsanUbsan.M.loaded_segments (0x78508 : word) = Some W_780f0.
Proof. vm_refl. Qed.
Lemma D_780f0 : decode_any W_780f0 = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780f4 : bv 32 := 0xef9ff06f.
Lemma F_780f4 : fetch_word AsanUbsan.M.loaded_segments (0x7850c : word) = Some W_780f4.
Proof. vm_refl. Qed.
Lemma D_780f4 : decode_any W_780f4 = Some (Jal 0 2096888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7817c : bv 32 := 0x0e061063.
Lemma F_7817c : fetch_word AsanUbsan.M.loaded_segments (0x78594 : word) = Some W_7817c.
Proof. vm_refl. Qed.
Lemma D_7817c : decode_any W_7817c = Some (Branch BC_NE 12 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78180 : bv 32 := 0xeb9ff06f.
Lemma F_78180 : fetch_word AsanUbsan.M.loaded_segments (0x78598 : word) = Some W_78180.
Proof. vm_refl. Qed.
Lemma D_78180 : decode_any W_78180 = Some (Jal 0 2096824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78184 : bv 32 := 0x00070803.
Lemma F_78184 : fetch_word AsanUbsan.M.loaded_segments (0x7859c : word) = Some W_78184.
Proof. vm_refl. Qed.
Lemma D_78184 : decode_any W_78184 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78188 : bv 32 := 0x0077f793.
Lemma F_78188 : fetch_word AsanUbsan.M.loaded_segments (0x785a0 : word) = Some W_78188.
Proof. vm_refl. Qed.
Lemma D_78188 : decode_any W_78188 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7818c : bv 32 := 0x010038b3.
Lemma F_7818c : fetch_word AsanUbsan.M.loaded_segments (0x785a4 : word) = Some W_7818c.
Proof. vm_refl. Qed.
Lemma D_7818c : decode_any W_7818c = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78190 : bv 32 := 0x0107a7b3.
Lemma F_78190 : fetch_word AsanUbsan.M.loaded_segments (0x785a8 : word) = Some W_78190.
Proof. vm_refl. Qed.
Lemma D_78190 : decode_any W_78190 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78194 : bv 32 := 0x0017c793.
Lemma F_78194 : fetch_word AsanUbsan.M.loaded_segments (0x785ac : word) = Some W_78194.
Proof. vm_refl. Qed.
Lemma D_78194 : decode_any W_78194 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78198 : bv 32 := 0x00f8f7b3.
Lemma F_78198 : fetch_word AsanUbsan.M.loaded_segments (0x785b0 : word) = Some W_78198.
Proof. vm_refl. Qed.
Lemma D_78198 : decode_any W_78198 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7819c : bv 32 := 0x00e6fa63.
Lemma F_7819c : fetch_word AsanUbsan.M.loaded_segments (0x785b4 : word) = Some W_7819c.
Proof. vm_refl. Qed.
Lemma D_7819c : decode_any W_7819c = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781a0 : bv 32 := 0x0006c803.
Lemma F_781a0 : fetch_word AsanUbsan.M.loaded_segments (0x785b8 : word) = Some W_781a0.
Proof. vm_refl. Qed.
Lemma D_781a0 : decode_any W_781a0 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781a4 : bv 32 := 0x00168693.
Lemma F_781a4 : fetch_word AsanUbsan.M.loaded_segments (0x785bc : word) = Some W_781a4.
Proof. vm_refl. Qed.
Lemma D_781a4 : decode_any W_781a4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781a8 : bv 32 := 0x00f867b3.
Lemma F_781a8 : fetch_word AsanUbsan.M.loaded_segments (0x785c0 : word) = Some W_781a8.
Proof. vm_refl. Qed.
Lemma D_781a8 : decode_any W_781a8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781ac : bv 32 := 0xfee69ae3.
Lemma F_781ac : fetch_word AsanUbsan.M.loaded_segments (0x785c4 : word) = Some W_781ac.
Proof. vm_refl. Qed.
Lemma D_781ac : decode_any W_781ac = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781b0 : bv 32 := 0x0ff7f693.
Lemma F_781b0 : fetch_word AsanUbsan.M.loaded_segments (0x785c8 : word) = Some W_781b0.
Proof. vm_refl. Qed.
Lemma D_781b0 : decode_any W_781b0 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781b4 : bv 32 := 0xe2068ce3.
Lemma F_781b4 : fetch_word AsanUbsan.M.loaded_segments (0x785cc : word) = Some W_781b4.
Proof. vm_refl. Qed.
Lemma D_781b4 : decode_any W_781b4 = Some (Branch BC_EQ 13 0 7736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781b8 : bv 32 := 0x00050a93.
Lemma F_781b8 : fetch_word AsanUbsan.M.loaded_segments (0x785d0 : word) = Some W_781b8.
Proof. vm_refl. Qed.
Lemma D_781b8 : decode_any W_781b8 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781bc : bv 32 := 0x00058513.
Lemma F_781bc : fetch_word AsanUbsan.M.loaded_segments (0x785d4 : word) = Some W_781bc.
Proof. vm_refl. Qed.
Lemma D_781bc : decode_any W_781bc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781c0 : bv 32 := 0x00058b13.
Lemma F_781c0 : fetch_word AsanUbsan.M.loaded_segments (0x785d8 : word) = Some W_781c0.
Proof. vm_refl. Qed.
Lemma D_781c0 : decode_any W_781c0 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781c4 : bv 32 := 0x00060593.
Lemma F_781c4 : fetch_word AsanUbsan.M.loaded_segments (0x785dc : word) = Some W_781c4.
Proof. vm_refl. Qed.
Lemma D_781c4 : decode_any W_781c4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781c8 : bv 32 := 0x00060493.
Lemma F_781c8 : fetch_word AsanUbsan.M.loaded_segments (0x785e0 : word) = Some W_781c8.
Proof. vm_refl. Qed.
Lemma D_781c8 : decode_any W_781c8 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781cc : bv 32 := 0x6dd020ef.
Lemma F_781cc : fetch_word AsanUbsan.M.loaded_segments (0x785e4 : word) = Some W_781cc.
Proof. vm_refl. Qed.
Lemma D_781cc : decode_any W_781cc = Some (Jal 1 11996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781d0 : bv 32 := 0x000b0593.
Lemma F_781d0 : fetch_word AsanUbsan.M.loaded_segments (0x785e8 : word) = Some W_781d0.
Proof. vm_refl. Qed.
Lemma D_781d0 : decode_any W_781d0 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781d4 : bv 32 := 0x00048613.
Lemma F_781d4 : fetch_word AsanUbsan.M.loaded_segments (0x785ec : word) = Some W_781d4.
Proof. vm_refl. Qed.
Lemma D_781d4 : decode_any W_781d4 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781d8 : bv 32 := 0x00050913.
Lemma F_781d8 : fetch_word AsanUbsan.M.loaded_segments (0x785f0 : word) = Some W_781d8.
Proof. vm_refl. Qed.
Lemma D_781d8 : decode_any W_781d8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781dc : bv 32 := 0x000a8513.
Lemma F_781dc : fetch_word AsanUbsan.M.loaded_segments (0x785f4 : word) = Some W_781dc.
Proof. vm_refl. Qed.
Lemma D_781dc : decode_any W_781dc = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781e0 : bv 32 := 0xe00906e3.
Lemma F_781e0 : fetch_word AsanUbsan.M.loaded_segments (0x785f8 : word) = Some W_781e0.
Proof. vm_refl. Qed.
Lemma D_781e0 : decode_any W_781e0 = Some (Branch BC_EQ 18 0 7692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78228 : bv 32 := 0x00070803.
Lemma F_78228 : fetch_word AsanUbsan.M.loaded_segments (0x78640 : word) = Some W_78228.
Proof. vm_refl. Qed.
Lemma D_78228 : decode_any W_78228 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7822c : bv 32 := 0x0077f793.
Lemma F_7822c : fetch_word AsanUbsan.M.loaded_segments (0x78644 : word) = Some W_7822c.
Proof. vm_refl. Qed.
Lemma D_7822c : decode_any W_7822c = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78230 : bv 32 := 0x010038b3.
Lemma F_78230 : fetch_word AsanUbsan.M.loaded_segments (0x78648 : word) = Some W_78230.
Proof. vm_refl. Qed.
Lemma D_78230 : decode_any W_78230 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78234 : bv 32 := 0x0107a7b3.
Lemma F_78234 : fetch_word AsanUbsan.M.loaded_segments (0x7864c : word) = Some W_78234.
Proof. vm_refl. Qed.
Lemma D_78234 : decode_any W_78234 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78238 : bv 32 := 0x0017c793.
Lemma F_78238 : fetch_word AsanUbsan.M.loaded_segments (0x78650 : word) = Some W_78238.
Proof. vm_refl. Qed.
Lemma D_78238 : decode_any W_78238 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7823c : bv 32 := 0x00f8f7b3.
Lemma F_7823c : fetch_word AsanUbsan.M.loaded_segments (0x78654 : word) = Some W_7823c.
Proof. vm_refl. Qed.
Lemma D_7823c : decode_any W_7823c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78240 : bv 32 := 0x00e6fa63.
Lemma F_78240 : fetch_word AsanUbsan.M.loaded_segments (0x78658 : word) = Some W_78240.
Proof. vm_refl. Qed.
Lemma D_78240 : decode_any W_78240 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78244 : bv 32 := 0x0006c803.
Lemma F_78244 : fetch_word AsanUbsan.M.loaded_segments (0x7865c : word) = Some W_78244.
Proof. vm_refl. Qed.
Lemma D_78244 : decode_any W_78244 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78248 : bv 32 := 0x00168693.
Lemma F_78248 : fetch_word AsanUbsan.M.loaded_segments (0x78660 : word) = Some W_78248.
Proof. vm_refl. Qed.
Lemma D_78248 : decode_any W_78248 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7824c : bv 32 := 0x00f867b3.
Lemma F_7824c : fetch_word AsanUbsan.M.loaded_segments (0x78664 : word) = Some W_7824c.
Proof. vm_refl. Qed.
Lemma D_7824c : decode_any W_7824c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78250 : bv 32 := 0xfee69ae3.
Lemma F_78250 : fetch_word AsanUbsan.M.loaded_segments (0x78668 : word) = Some W_78250.
Proof. vm_refl. Qed.
Lemma D_78250 : decode_any W_78250 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78254 : bv 32 := 0x0ff7f693.
Lemma F_78254 : fetch_word AsanUbsan.M.loaded_segments (0x7866c : word) = Some W_78254.
Proof. vm_refl. Qed.
Lemma D_78254 : decode_any W_78254 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78258 : bv 32 := 0xde0680e3.
Lemma F_78258 : fetch_word AsanUbsan.M.loaded_segments (0x78670 : word) = Some W_78258.
Proof. vm_refl. Qed.
Lemma D_78258 : decode_any W_78258 = Some (Branch BC_EQ 13 0 7648, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7825c : bv 32 := 0x00050493.
Lemma F_7825c : fetch_word AsanUbsan.M.loaded_segments (0x78674 : word) = Some W_7825c.
Proof. vm_refl. Qed.
Lemma D_7825c : decode_any W_7825c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78260 : bv 32 := 0x00058a93.
Lemma F_78260 : fetch_word AsanUbsan.M.loaded_segments (0x78678 : word) = Some W_78260.
Proof. vm_refl. Qed.
Lemma D_78260 : decode_any W_78260 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78264 : bv 32 := 0x00060593.
Lemma F_78264 : fetch_word AsanUbsan.M.loaded_segments (0x7867c : word) = Some W_78264.
Proof. vm_refl. Qed.
Lemma D_78264 : decode_any W_78264 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78268 : bv 32 := 0x00060913.
Lemma F_78268 : fetch_word AsanUbsan.M.loaded_segments (0x78680 : word) = Some W_78268.
Proof. vm_refl. Qed.
Lemma D_78268 : decode_any W_78268 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7826c : bv 32 := 0x63d020ef.
Lemma F_7826c : fetch_word AsanUbsan.M.loaded_segments (0x78684 : word) = Some W_7826c.
Proof. vm_refl. Qed.
Lemma D_7826c : decode_any W_7826c = Some (Jal 1 11836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78270 : bv 32 := 0x000a8593.
Lemma F_78270 : fetch_word AsanUbsan.M.loaded_segments (0x78688 : word) = Some W_78270.
Proof. vm_refl. Qed.
Lemma D_78270 : decode_any W_78270 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78274 : bv 32 := 0x00090613.
Lemma F_78274 : fetch_word AsanUbsan.M.loaded_segments (0x7868c : word) = Some W_78274.
Proof. vm_refl. Qed.
Lemma D_78274 : decode_any W_78274 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78278 : bv 32 := 0x00050993.
Lemma F_78278 : fetch_word AsanUbsan.M.loaded_segments (0x78690 : word) = Some W_78278.
Proof. vm_refl. Qed.
Lemma D_78278 : decode_any W_78278 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7827c : bv 32 := 0x00048513.
Lemma F_7827c : fetch_word AsanUbsan.M.loaded_segments (0x78694 : word) = Some W_7827c.
Proof. vm_refl. Qed.
Lemma D_7827c : decode_any W_7827c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78280 : bv 32 := 0xda098ce3.
Lemma F_78280 : fetch_word AsanUbsan.M.loaded_segments (0x78698 : word) = Some W_78280.
Proof. vm_refl. Qed.
Lemma D_78280 : decode_any W_78280 = Some (Branch BC_EQ 19 0 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782c8 : bv 32 := 0x81010113.
Lemma F_782c8 : fetch_word AsanUbsan.M.loaded_segments (0x786e0 : word) = Some W_782c8.
Proof. vm_refl. Qed.
Lemma D_782c8 : decode_any W_782c8 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782cc : bv 32 := 0x7e113423.
Lemma F_782cc : fetch_word AsanUbsan.M.loaded_segments (0x786e4 : word) = Some W_782cc.
Proof. vm_refl. Qed.
Lemma D_782cc : decode_any W_782cc = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782d0 : bv 32 := 0x7e813023.
Lemma F_782d0 : fetch_word AsanUbsan.M.loaded_segments (0x786e8 : word) = Some W_782d0.
Proof. vm_refl. Qed.
Lemma D_782d0 : decode_any W_782d0 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782d4 : bv 32 := 0x7c913c23.
Lemma F_782d4 : fetch_word AsanUbsan.M.loaded_segments (0x786ec : word) = Some W_782d4.
Proof. vm_refl. Qed.
Lemma D_782d4 : decode_any W_782d4 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782d8 : bv 32 := 0x7d213823.
Lemma F_782d8 : fetch_word AsanUbsan.M.loaded_segments (0x786f0 : word) = Some W_782d8.
Proof. vm_refl. Qed.
Lemma D_782d8 : decode_any W_782d8 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782dc : bv 32 := 0x7d313423.
Lemma F_782dc : fetch_word AsanUbsan.M.loaded_segments (0x786f4 : word) = Some W_782dc.
Proof. vm_refl. Qed.
Lemma D_782dc : decode_any W_782dc = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782e0 : bv 32 := 0x7d413023.
Lemma F_782e0 : fetch_word AsanUbsan.M.loaded_segments (0x786f8 : word) = Some W_782e0.
Proof. vm_refl. Qed.
Lemma D_782e0 : decode_any W_782e0 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782e4 : bv 32 := 0x7b513c23.
Lemma F_782e4 : fetch_word AsanUbsan.M.loaded_segments (0x786fc : word) = Some W_782e4.
Proof. vm_refl. Qed.
Lemma D_782e4 : decode_any W_782e4 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782e8 : bv 32 := 0x7b613823.
Lemma F_782e8 : fetch_word AsanUbsan.M.loaded_segments (0x78700 : word) = Some W_782e8.
Proof. vm_refl. Qed.
Lemma D_782e8 : decode_any W_782e8 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782ec : bv 32 := 0x7f010413.
Lemma F_782ec : fetch_word AsanUbsan.M.loaded_segments (0x78704 : word) = Some W_782ec.
Proof. vm_refl. Qed.
Lemma D_782ec : decode_any W_782ec = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782f0 : bv 32 := 0xf9010113.
Lemma F_782f0 : fetch_word AsanUbsan.M.loaded_segments (0x78708 : word) = Some W_782f0.
Proof. vm_refl. Qed.
Lemma D_782f0 : decode_any W_782f0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782f4 : bv 32 := 0x000c0697.
Lemma F_782f4 : fetch_word AsanUbsan.M.loaded_segments (0x7870c : word) = Some W_782f4.
Proof. vm_refl. Qed.
Lemma D_782f4 : decode_any W_782f4 = Some (Auipc 13 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782f8 : bv 32 := 0x91c6b683.
Lemma F_782f8 : fetch_word AsanUbsan.M.loaded_segments (0x78710 : word) = Some W_782f8.
Proof. vm_refl. Qed.
Lemma D_782f8 : decode_any W_782f8 = Some (Load SZ8 true 13 13 2332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782fc : bv 32 := 0x0006c683.
Lemma F_782fc : fetch_word AsanUbsan.M.loaded_segments (0x78714 : word) = Some W_782fc.
Proof. vm_refl. Qed.
Lemma D_782fc : decode_any W_782fc = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78300 : bv 32 := 0x08068a63.
Lemma F_78300 : fetch_word AsanUbsan.M.loaded_segments (0x78718 : word) = Some W_78300.
Proof. vm_refl. Qed.
Lemma D_78300 : decode_any W_78300 = Some (Branch BC_EQ 13 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78304 : bv 32 := 0xfff54693.
Lemma F_78304 : fetch_word AsanUbsan.M.loaded_segments (0x7871c : word) = Some W_78304.
Proof. vm_refl. Qed.
Lemma D_78304 : decode_any W_78304 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78308 : bv 32 := 0x80040a93.
Lemma F_78308 : fetch_word AsanUbsan.M.loaded_segments (0x78720 : word) = Some W_78308.
Proof. vm_refl. Qed.
Lemma D_78308 : decode_any W_78308 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7830c : bv 32 := 0xfa8a8a93.
Lemma F_7830c : fetch_word AsanUbsan.M.loaded_segments (0x78724 : word) = Some W_7830c.
Proof. vm_refl. Qed.
Lemma D_7830c : decode_any W_7830c = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78310 : bv 32 := 0x0cc6ea63.
Lemma F_78310 : fetch_word AsanUbsan.M.loaded_segments (0x78728 : word) = Some W_78310.
Proof. vm_refl. Qed.
Lemma D_78310 : decode_any W_78310 = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78314 : bv 32 := 0xfbf60693.
Lemma F_78314 : fetch_word AsanUbsan.M.loaded_segments (0x7872c : word) = Some W_78314.
Proof. vm_refl. Qed.
Lemma D_78314 : decode_any W_78314 = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78318 : bv 32 := 0xfbf00713.
Lemma F_78318 : fetch_word AsanUbsan.M.loaded_segments (0x78730 : word) = Some W_78318.
Proof. vm_refl. Qed.
Lemma D_78318 : decode_any W_78318 = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7831c : bv 32 := 0x14d77863.
Lemma F_7831c : fetch_word AsanUbsan.M.loaded_segments (0x78734 : word) = Some W_7831c.
Proof. vm_refl. Qed.
Lemma D_7831c : decode_any W_7831c = Some (Branch BC_GEU 14 13 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78320 : bv 32 := 0x000bf697.
Lemma F_78320 : fetch_word AsanUbsan.M.loaded_segments (0x78738 : word) = Some W_78320.
Proof. vm_refl. Qed.
Lemma D_78320 : decode_any W_78320 = Some (Auipc 13 191, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78324 : bv 32 := 0xd886b683.
Lemma F_78324 : fetch_word AsanUbsan.M.loaded_segments (0x7873c : word) = Some W_78324.
Proof. vm_refl. Qed.
Lemma D_78324 : decode_any W_78324 = Some (Load SZ8 true 13 13 3464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78328 : bv 32 := 0x00c507b3.
Lemma F_78328 : fetch_word AsanUbsan.M.loaded_segments (0x78740 : word) = Some W_78328.
Proof. vm_refl. Qed.
Lemma D_78328 : decode_any W_78328 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7832c : bv 32 := 0x0006b703.
Lemma F_7832c : fetch_word AsanUbsan.M.loaded_segments (0x78744 : word) = Some W_7832c.
Proof. vm_refl. Qed.
Lemma D_7832c : decode_any W_7832c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78330 : bv 32 := 0x00355693.
Lemma F_78330 : fetch_word AsanUbsan.M.loaded_segments (0x78748 : word) = Some W_78330.
Proof. vm_refl. Qed.
Lemma D_78330 : decode_any W_78330 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78334 : bv 32 := 0xfff78793.
Lemma F_78334 : fetch_word AsanUbsan.M.loaded_segments (0x7874c : word) = Some W_78334.
Proof. vm_refl. Qed.
Lemma D_78334 : decode_any W_78334 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78338 : bv 32 := 0x0037d813.
Lemma F_78338 : fetch_word AsanUbsan.M.loaded_segments (0x78750 : word) = Some W_78338.
Proof. vm_refl. Qed.
Lemma D_78338 : decode_any W_78338 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7833c : bv 32 := 0x00d706b3.
Lemma F_7833c : fetch_word AsanUbsan.M.loaded_segments (0x78754 : word) = Some W_7833c.
Proof. vm_refl. Qed.
Lemma D_7833c : decode_any W_7833c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78340 : bv 32 := 0x01070733.
Lemma F_78340 : fetch_word AsanUbsan.M.loaded_segments (0x78758 : word) = Some W_78340.
Proof. vm_refl. Qed.
Lemma D_78340 : decode_any W_78340 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78344 : bv 32 := 0xff86f813.
Lemma F_78344 : fetch_word AsanUbsan.M.loaded_segments (0x7875c : word) = Some W_78344.
Proof. vm_refl. Qed.
Lemma D_78344 : decode_any W_78344 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78348 : bv 32 := 0xff877893.
Lemma F_78348 : fetch_word AsanUbsan.M.loaded_segments (0x78760 : word) = Some W_78348.
Proof. vm_refl. Qed.
Lemma D_78348 : decode_any W_78348 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7834c : bv 32 := 0x00083803.
Lemma F_7834c : fetch_word AsanUbsan.M.loaded_segments (0x78764 : word) = Some W_7834c.
Proof. vm_refl. Qed.
Lemma D_7834c : decode_any W_7834c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78350 : bv 32 := 0x0008b883.
Lemma F_78350 : fetch_word AsanUbsan.M.loaded_segments (0x78768 : word) = Some W_78350.
Proof. vm_refl. Qed.
Lemma D_78350 : decode_any W_78350 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78354 : bv 32 := 0x0108e833.
Lemma F_78354 : fetch_word AsanUbsan.M.loaded_segments (0x7876c : word) = Some W_78354.
Proof. vm_refl. Qed.
Lemma D_78354 : decode_any W_78354 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78358 : bv 32 := 0x10081e63.
Lemma F_78358 : fetch_word AsanUbsan.M.loaded_segments (0x78770 : word) = Some W_78358.
Proof. vm_refl. Qed.
Lemma D_78358 : decode_any W_78358 = Some (Branch BC_NE 16 0 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7835c : bv 32 := 0x000c1697.
Lemma F_7835c : fetch_word AsanUbsan.M.loaded_segments (0x78774 : word) = Some W_7835c.
Proof. vm_refl. Qed.
Lemma D_7835c : decode_any W_7835c = Some (Auipc 13 193, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78360 : bv 32 := 0xd5c6b683.
Lemma F_78360 : fetch_word AsanUbsan.M.loaded_segments (0x78778 : word) = Some W_78360.
Proof. vm_refl. Qed.
Lemma D_78360 : decode_any W_78360 = Some (Load SZ8 true 13 13 3420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78364 : bv 32 := 0x000680e7.
Lemma F_78364 : fetch_word AsanUbsan.M.loaded_segments (0x7877c : word) = Some W_78364.
Proof. vm_refl. Qed.
Lemma D_78364 : decode_any W_78364 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78368 : bv 32 := 0x07010113.
Lemma F_78368 : fetch_word AsanUbsan.M.loaded_segments (0x78780 : word) = Some W_78368.
Proof. vm_refl. Qed.
Lemma D_78368 : decode_any W_78368 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7836c : bv 32 := 0x7e813083.
Lemma F_7836c : fetch_word AsanUbsan.M.loaded_segments (0x78784 : word) = Some W_7836c.
Proof. vm_refl. Qed.
Lemma D_7836c : decode_any W_7836c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78370 : bv 32 := 0x7e013403.
Lemma F_78370 : fetch_word AsanUbsan.M.loaded_segments (0x78788 : word) = Some W_78370.
Proof. vm_refl. Qed.
Lemma D_78370 : decode_any W_78370 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78374 : bv 32 := 0x7d813483.
Lemma F_78374 : fetch_word AsanUbsan.M.loaded_segments (0x7878c : word) = Some W_78374.
Proof. vm_refl. Qed.
Lemma D_78374 : decode_any W_78374 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78378 : bv 32 := 0x7d013903.
Lemma F_78378 : fetch_word AsanUbsan.M.loaded_segments (0x78790 : word) = Some W_78378.
Proof. vm_refl. Qed.
Lemma D_78378 : decode_any W_78378 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7837c : bv 32 := 0x7c813983.
Lemma F_7837c : fetch_word AsanUbsan.M.loaded_segments (0x78794 : word) = Some W_7837c.
Proof. vm_refl. Qed.
Lemma D_7837c : decode_any W_7837c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78380 : bv 32 := 0x7c013a03.
Lemma F_78380 : fetch_word AsanUbsan.M.loaded_segments (0x78798 : word) = Some W_78380.
Proof. vm_refl. Qed.
Lemma D_78380 : decode_any W_78380 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78384 : bv 32 := 0x7b813a83.
Lemma F_78384 : fetch_word AsanUbsan.M.loaded_segments (0x7879c : word) = Some W_78384.
Proof. vm_refl. Qed.
Lemma D_78384 : decode_any W_78384 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78388 : bv 32 := 0x7b013b03.
Lemma F_78388 : fetch_word AsanUbsan.M.loaded_segments (0x787a0 : word) = Some W_78388.
Proof. vm_refl. Qed.
Lemma D_78388 : decode_any W_78388 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7838c : bv 32 := 0x7f010113.
Lemma F_7838c : fetch_word AsanUbsan.M.loaded_segments (0x787a4 : word) = Some W_7838c.
Proof. vm_refl. Qed.
Lemma D_7838c : decode_any W_7838c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78390 : bv 32 := 0x00008067.
Lemma F_78390 : fetch_word AsanUbsan.M.loaded_segments (0x787a8 : word) = Some W_78390.
Proof. vm_refl. Qed.
Lemma D_78390 : decode_any W_78390 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7846c : bv 32 := 0x02061e63.
Lemma F_7846c : fetch_word AsanUbsan.M.loaded_segments (0x78884 : word) = Some W_7846c.
Proof. vm_refl. Qed.
Lemma D_7846c : decode_any W_7846c = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78470 : bv 32 := 0xeedff06f.
Lemma F_78470 : fetch_word AsanUbsan.M.loaded_segments (0x78888 : word) = Some W_78470.
Proof. vm_refl. Qed.
Lemma D_78470 : decode_any W_78470 = Some (Jal 0 2096876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78474 : bv 32 := 0x00070803.
Lemma F_78474 : fetch_word AsanUbsan.M.loaded_segments (0x7888c : word) = Some W_78474.
Proof. vm_refl. Qed.
Lemma D_78474 : decode_any W_78474 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78478 : bv 32 := 0x0077f793.
Lemma F_78478 : fetch_word AsanUbsan.M.loaded_segments (0x78890 : word) = Some W_78478.
Proof. vm_refl. Qed.
Lemma D_78478 : decode_any W_78478 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7847c : bv 32 := 0x010038b3.
Lemma F_7847c : fetch_word AsanUbsan.M.loaded_segments (0x78894 : word) = Some W_7847c.
Proof. vm_refl. Qed.
Lemma D_7847c : decode_any W_7847c = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78480 : bv 32 := 0x0107a7b3.
Lemma F_78480 : fetch_word AsanUbsan.M.loaded_segments (0x78898 : word) = Some W_78480.
Proof. vm_refl. Qed.
Lemma D_78480 : decode_any W_78480 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78484 : bv 32 := 0x0017c793.
Lemma F_78484 : fetch_word AsanUbsan.M.loaded_segments (0x7889c : word) = Some W_78484.
Proof. vm_refl. Qed.
Lemma D_78484 : decode_any W_78484 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78488 : bv 32 := 0x00f8f7b3.
Lemma F_78488 : fetch_word AsanUbsan.M.loaded_segments (0x788a0 : word) = Some W_78488.
Proof. vm_refl. Qed.
Lemma D_78488 : decode_any W_78488 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7848c : bv 32 := 0x00e6fa63.
Lemma F_7848c : fetch_word AsanUbsan.M.loaded_segments (0x788a4 : word) = Some W_7848c.
Proof. vm_refl. Qed.
Lemma D_7848c : decode_any W_7848c = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78490 : bv 32 := 0x0006c803.
Lemma F_78490 : fetch_word AsanUbsan.M.loaded_segments (0x788a8 : word) = Some W_78490.
Proof. vm_refl. Qed.
Lemma D_78490 : decode_any W_78490 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78494 : bv 32 := 0x00168693.
Lemma F_78494 : fetch_word AsanUbsan.M.loaded_segments (0x788ac : word) = Some W_78494.
Proof. vm_refl. Qed.
Lemma D_78494 : decode_any W_78494 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78498 : bv 32 := 0x00f867b3.
Lemma F_78498 : fetch_word AsanUbsan.M.loaded_segments (0x788b0 : word) = Some W_78498.
Proof. vm_refl. Qed.
Lemma D_78498 : decode_any W_78498 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7849c : bv 32 := 0xfee69ae3.
Lemma F_7849c : fetch_word AsanUbsan.M.loaded_segments (0x788b4 : word) = Some W_7849c.
Proof. vm_refl. Qed.
Lemma D_7849c : decode_any W_7849c = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_784a0 : bv 32 := 0x0ff7f693.
Lemma F_784a0 : fetch_word AsanUbsan.M.loaded_segments (0x788b8 : word) = Some W_784a0.
Proof. vm_refl. Qed.
Lemma D_784a0 : decode_any W_784a0 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_784a4 : bv 32 := 0xea068ce3.
Lemma F_784a4 : fetch_word AsanUbsan.M.loaded_segments (0x788bc : word) = Some W_784a4.
Proof. vm_refl. Qed.
Lemma D_784a4 : decode_any W_784a4 = Some (Branch BC_EQ 13 0 7864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_784a8 : bv 32 := 0x00050493.
Lemma F_784a8 : fetch_word AsanUbsan.M.loaded_segments (0x788c0 : word) = Some W_784a8.
Proof. vm_refl. Qed.
Lemma D_784a8 : decode_any W_784a8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_784ac : bv 32 := 0x00058b13.
Lemma F_784ac : fetch_word AsanUbsan.M.loaded_segments (0x788c4 : word) = Some W_784ac.
Proof. vm_refl. Qed.
Lemma D_784ac : decode_any W_784ac = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_784b0 : bv 32 := 0x00060593.
Lemma F_784b0 : fetch_word AsanUbsan.M.loaded_segments (0x788c8 : word) = Some W_784b0.
Proof. vm_refl. Qed.
Lemma D_784b0 : decode_any W_784b0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_784b4 : bv 32 := 0x00060913.
Lemma F_784b4 : fetch_word AsanUbsan.M.loaded_segments (0x788cc : word) = Some W_784b4.
Proof. vm_refl. Qed.
Lemma D_784b4 : decode_any W_784b4 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_784b8 : bv 32 := 0x3f1020ef.
Lemma F_784b8 : fetch_word AsanUbsan.M.loaded_segments (0x788d0 : word) = Some W_784b8.
Proof. vm_refl. Qed.
Lemma D_784b8 : decode_any W_784b8 = Some (Jal 1 11248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_784bc : bv 32 := 0x000b0593.
Lemma F_784bc : fetch_word AsanUbsan.M.loaded_segments (0x788d4 : word) = Some W_784bc.
Proof. vm_refl. Qed.
Lemma D_784bc : decode_any W_784bc = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_784c0 : bv 32 := 0x00090613.
Lemma F_784c0 : fetch_word AsanUbsan.M.loaded_segments (0x788d8 : word) = Some W_784c0.
Proof. vm_refl. Qed.
Lemma D_784c0 : decode_any W_784c0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_784c4 : bv 32 := 0x00050993.
Lemma F_784c4 : fetch_word AsanUbsan.M.loaded_segments (0x788dc : word) = Some W_784c4.
Proof. vm_refl. Qed.
Lemma D_784c4 : decode_any W_784c4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_784c8 : bv 32 := 0x00048513.
Lemma F_784c8 : fetch_word AsanUbsan.M.loaded_segments (0x788e0 : word) = Some W_784c8.
Proof. vm_refl. Qed.
Lemma D_784c8 : decode_any W_784c8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_784cc : bv 32 := 0xe80988e3.
Lemma F_784cc : fetch_word AsanUbsan.M.loaded_segments (0x788e4 : word) = Some W_784cc.
Proof. vm_refl. Qed.
Lemma D_784cc : decode_any W_784cc = Some (Branch BC_EQ 19 0 7824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785b8 : bv 32 := 0x81010113.
Lemma F_785b8 : fetch_word AsanUbsan.M.loaded_segments (0x789d0 : word) = Some W_785b8.
Proof. vm_refl. Qed.
Lemma D_785b8 : decode_any W_785b8 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785bc : bv 32 := 0x7e113423.
Lemma F_785bc : fetch_word AsanUbsan.M.loaded_segments (0x789d4 : word) = Some W_785bc.
Proof. vm_refl. Qed.
Lemma D_785bc : decode_any W_785bc = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785c0 : bv 32 := 0x7e813023.
Lemma F_785c0 : fetch_word AsanUbsan.M.loaded_segments (0x789d8 : word) = Some W_785c0.
Proof. vm_refl. Qed.
Lemma D_785c0 : decode_any W_785c0 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785c4 : bv 32 := 0x7c913c23.
Lemma F_785c4 : fetch_word AsanUbsan.M.loaded_segments (0x789dc : word) = Some W_785c4.
Proof. vm_refl. Qed.
Lemma D_785c4 : decode_any W_785c4 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785c8 : bv 32 := 0x7d213823.
Lemma F_785c8 : fetch_word AsanUbsan.M.loaded_segments (0x789e0 : word) = Some W_785c8.
Proof. vm_refl. Qed.
Lemma D_785c8 : decode_any W_785c8 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785cc : bv 32 := 0x7d313423.
Lemma F_785cc : fetch_word AsanUbsan.M.loaded_segments (0x789e4 : word) = Some W_785cc.
Proof. vm_refl. Qed.
Lemma D_785cc : decode_any W_785cc = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785d0 : bv 32 := 0x7d413023.
Lemma F_785d0 : fetch_word AsanUbsan.M.loaded_segments (0x789e8 : word) = Some W_785d0.
Proof. vm_refl. Qed.
Lemma D_785d0 : decode_any W_785d0 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785d4 : bv 32 := 0x7b513c23.
Lemma F_785d4 : fetch_word AsanUbsan.M.loaded_segments (0x789ec : word) = Some W_785d4.
Proof. vm_refl. Qed.
Lemma D_785d4 : decode_any W_785d4 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785d8 : bv 32 := 0x7b613823.
Lemma F_785d8 : fetch_word AsanUbsan.M.loaded_segments (0x789f0 : word) = Some W_785d8.
Proof. vm_refl. Qed.
Lemma D_785d8 : decode_any W_785d8 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785dc : bv 32 := 0x7b713423.
Lemma F_785dc : fetch_word AsanUbsan.M.loaded_segments (0x789f4 : word) = Some W_785dc.
Proof. vm_refl. Qed.
Lemma D_785dc : decode_any W_785dc = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785e0 : bv 32 := 0x7f010413.
Lemma F_785e0 : fetch_word AsanUbsan.M.loaded_segments (0x789f8 : word) = Some W_785e0.
Proof. vm_refl. Qed.
Lemma D_785e0 : decode_any W_785e0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785e4 : bv 32 := 0xf9010113.
Lemma F_785e4 : fetch_word AsanUbsan.M.loaded_segments (0x789fc : word) = Some W_785e4.
Proof. vm_refl. Qed.
Lemma D_785e4 : decode_any W_785e4 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785e8 : bv 32 := 0x000bf697.
Lemma F_785e8 : fetch_word AsanUbsan.M.loaded_segments (0x78a00 : word) = Some W_785e8.
Proof. vm_refl. Qed.
Lemma D_785e8 : decode_any W_785e8 = Some (Auipc 13 191, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785ec : bv 32 := 0x6286b683.
Lemma F_785ec : fetch_word AsanUbsan.M.loaded_segments (0x78a04 : word) = Some W_785ec.
Proof. vm_refl. Qed.
Lemma D_785ec : decode_any W_785ec = Some (Load SZ8 true 13 13 1576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785f0 : bv 32 := 0x0006c683.
Lemma F_785f0 : fetch_word AsanUbsan.M.loaded_segments (0x78a08 : word) = Some W_785f0.
Proof. vm_refl. Qed.
Lemma D_785f0 : decode_any W_785f0 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785f4 : bv 32 := 0x0a068463.
Lemma F_785f4 : fetch_word AsanUbsan.M.loaded_segments (0x78a0c : word) = Some W_785f4.
Proof. vm_refl. Qed.
Lemma D_785f4 : decode_any W_785f4 = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785f8 : bv 32 := 0xfff5c693.
Lemma F_785f8 : fetch_word AsanUbsan.M.loaded_segments (0x78a10 : word) = Some W_785f8.
Proof. vm_refl. Qed.
Lemma D_785f8 : decode_any W_785f8 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785fc : bv 32 := 0x80040a93.
Lemma F_785fc : fetch_word AsanUbsan.M.loaded_segments (0x78a14 : word) = Some W_785fc.
Proof. vm_refl. Qed.
Lemma D_785fc : decode_any W_785fc = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78600 : bv 32 := 0xfa0a8a93.
Lemma F_78600 : fetch_word AsanUbsan.M.loaded_segments (0x78a18 : word) = Some W_78600.
Proof. vm_refl. Qed.
Lemma D_78600 : decode_any W_78600 = Some (OpImm ALU_ADD 21 21 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78604 : bv 32 := 0x0cc6e663.
Lemma F_78604 : fetch_word AsanUbsan.M.loaded_segments (0x78a1c : word) = Some W_78604.
Proof. vm_refl. Qed.
Lemma D_78604 : decode_any W_78604 = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78608 : bv 32 := 0xfbf60a13.
Lemma F_78608 : fetch_word AsanUbsan.M.loaded_segments (0x78a20 : word) = Some W_78608.
Proof. vm_refl. Qed.
Lemma D_78608 : decode_any W_78608 = Some (OpImm ALU_ADD 20 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7860c : bv 32 := 0xfbf00693.
Lemma F_7860c : fetch_word AsanUbsan.M.loaded_segments (0x78a24 : word) = Some W_7860c.
Proof. vm_refl. Qed.
Lemma D_7860c : decode_any W_7860c = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78610 : bv 32 := 0x1546f463.
Lemma F_78610 : fetch_word AsanUbsan.M.loaded_segments (0x78a28 : word) = Some W_78610.
Proof. vm_refl. Qed.
Lemma D_78610 : decode_any W_78610 = Some (Branch BC_GEU 13 20 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78614 : bv 32 := 0x000bf697.
Lemma F_78614 : fetch_word AsanUbsan.M.loaded_segments (0x78a2c : word) = Some W_78614.
Proof. vm_refl. Qed.
Lemma D_78614 : decode_any W_78614 = Some (Auipc 13 191, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78618 : bv 32 := 0xa946b683.
Lemma F_78618 : fetch_word AsanUbsan.M.loaded_segments (0x78a30 : word) = Some W_78618.
Proof. vm_refl. Qed.
Lemma D_78618 : decode_any W_78618 = Some (Load SZ8 true 13 13 2708, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7861c : bv 32 := 0x00c587b3.
Lemma F_7861c : fetch_word AsanUbsan.M.loaded_segments (0x78a34 : word) = Some W_7861c.
Proof. vm_refl. Qed.
Lemma D_7861c : decode_any W_7861c = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78620 : bv 32 := 0x0006b703.
Lemma F_78620 : fetch_word AsanUbsan.M.loaded_segments (0x78a38 : word) = Some W_78620.
Proof. vm_refl. Qed.
Lemma D_78620 : decode_any W_78620 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78624 : bv 32 := 0x0035d693.
Lemma F_78624 : fetch_word AsanUbsan.M.loaded_segments (0x78a3c : word) = Some W_78624.
Proof. vm_refl. Qed.
Lemma D_78624 : decode_any W_78624 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78628 : bv 32 := 0xfff78793.
Lemma F_78628 : fetch_word AsanUbsan.M.loaded_segments (0x78a40 : word) = Some W_78628.
Proof. vm_refl. Qed.
Lemma D_78628 : decode_any W_78628 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7862c : bv 32 := 0x0037d813.
Lemma F_7862c : fetch_word AsanUbsan.M.loaded_segments (0x78a44 : word) = Some W_7862c.
Proof. vm_refl. Qed.
Lemma D_7862c : decode_any W_7862c = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78630 : bv 32 := 0x00d706b3.
Lemma F_78630 : fetch_word AsanUbsan.M.loaded_segments (0x78a48 : word) = Some W_78630.
Proof. vm_refl. Qed.
Lemma D_78630 : decode_any W_78630 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78634 : bv 32 := 0x01070733.
Lemma F_78634 : fetch_word AsanUbsan.M.loaded_segments (0x78a4c : word) = Some W_78634.
Proof. vm_refl. Qed.
Lemma D_78634 : decode_any W_78634 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78638 : bv 32 := 0xff86f813.
Lemma F_78638 : fetch_word AsanUbsan.M.loaded_segments (0x78a50 : word) = Some W_78638.
Proof. vm_refl. Qed.
Lemma D_78638 : decode_any W_78638 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7863c : bv 32 := 0xff877893.
Lemma F_7863c : fetch_word AsanUbsan.M.loaded_segments (0x78a54 : word) = Some W_7863c.
Proof. vm_refl. Qed.
Lemma D_7863c : decode_any W_7863c = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78640 : bv 32 := 0x00083803.
Lemma F_78640 : fetch_word AsanUbsan.M.loaded_segments (0x78a58 : word) = Some W_78640.
Proof. vm_refl. Qed.
Lemma D_78640 : decode_any W_78640 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78644 : bv 32 := 0x0008b883.
Lemma F_78644 : fetch_word AsanUbsan.M.loaded_segments (0x78a5c : word) = Some W_78644.
Proof. vm_refl. Qed.
Lemma D_78644 : decode_any W_78644 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78648 : bv 32 := 0x0108e833.
Lemma F_78648 : fetch_word AsanUbsan.M.loaded_segments (0x78a60 : word) = Some W_78648.
Proof. vm_refl. Qed.
Lemma D_78648 : decode_any W_78648 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7864c : bv 32 := 0x1a081063.
Lemma F_7864c : fetch_word AsanUbsan.M.loaded_segments (0x78a64 : word) = Some W_7864c.
Proof. vm_refl. Qed.
Lemma D_7864c : decode_any W_7864c = Some (Branch BC_NE 16 0 416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78650 : bv 32 := 0xfff54693.
Lemma F_78650 : fetch_word AsanUbsan.M.loaded_segments (0x78a68 : word) = Some W_78650.
Proof. vm_refl. Qed.
Lemma D_78650 : decode_any W_78650 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78654 : bv 32 := 0x10c6e663.
Lemma F_78654 : fetch_word AsanUbsan.M.loaded_segments (0x78a6c : word) = Some W_78654.
Proof. vm_refl. Qed.
Lemma D_78654 : decode_any W_78654 = Some (Branch BC_LTU 13 12 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78658 : bv 32 := 0xfbf00693.
Lemma F_78658 : fetch_word AsanUbsan.M.loaded_segments (0x78a70 : word) = Some W_78658.
Proof. vm_refl. Qed.
Lemma D_78658 : decode_any W_78658 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7865c : bv 32 := 0x1946f463.
Lemma F_7865c : fetch_word AsanUbsan.M.loaded_segments (0x78a74 : word) = Some W_7865c.
Proof. vm_refl. Qed.
Lemma D_7865c : decode_any W_7865c = Some (Branch BC_GEU 13 20 392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78660 : bv 32 := 0x000bf697.
Lemma F_78660 : fetch_word AsanUbsan.M.loaded_segments (0x78a78 : word) = Some W_78660.
Proof. vm_refl. Qed.
Lemma D_78660 : decode_any W_78660 = Some (Auipc 13 191, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78664 : bv 32 := 0xa486b683.
Lemma F_78664 : fetch_word AsanUbsan.M.loaded_segments (0x78a7c : word) = Some W_78664.
Proof. vm_refl. Qed.
Lemma D_78664 : decode_any W_78664 = Some (Load SZ8 true 13 13 2632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78668 : bv 32 := 0x00c507b3.
Lemma F_78668 : fetch_word AsanUbsan.M.loaded_segments (0x78a80 : word) = Some W_78668.
Proof. vm_refl. Qed.
Lemma D_78668 : decode_any W_78668 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7866c : bv 32 := 0x0006b703.
Lemma F_7866c : fetch_word AsanUbsan.M.loaded_segments (0x78a84 : word) = Some W_7866c.
Proof. vm_refl. Qed.
Lemma D_7866c : decode_any W_7866c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78670 : bv 32 := 0x00355693.
Lemma F_78670 : fetch_word AsanUbsan.M.loaded_segments (0x78a88 : word) = Some W_78670.
Proof. vm_refl. Qed.
Lemma D_78670 : decode_any W_78670 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78674 : bv 32 := 0xfff78793.
Lemma F_78674 : fetch_word AsanUbsan.M.loaded_segments (0x78a8c : word) = Some W_78674.
Proof. vm_refl. Qed.
Lemma D_78674 : decode_any W_78674 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78678 : bv 32 := 0x0037d813.
Lemma F_78678 : fetch_word AsanUbsan.M.loaded_segments (0x78a90 : word) = Some W_78678.
Proof. vm_refl. Qed.
Lemma D_78678 : decode_any W_78678 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7867c : bv 32 := 0x00d706b3.
Lemma F_7867c : fetch_word AsanUbsan.M.loaded_segments (0x78a94 : word) = Some W_7867c.
Proof. vm_refl. Qed.
Lemma D_7867c : decode_any W_7867c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78680 : bv 32 := 0x01070733.
Lemma F_78680 : fetch_word AsanUbsan.M.loaded_segments (0x78a98 : word) = Some W_78680.
Proof. vm_refl. Qed.
Lemma D_78680 : decode_any W_78680 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78684 : bv 32 := 0xff86f813.
Lemma F_78684 : fetch_word AsanUbsan.M.loaded_segments (0x78a9c : word) = Some W_78684.
Proof. vm_refl. Qed.
Lemma D_78684 : decode_any W_78684 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78688 : bv 32 := 0xff877893.
Lemma F_78688 : fetch_word AsanUbsan.M.loaded_segments (0x78aa0 : word) = Some W_78688.
Proof. vm_refl. Qed.
Lemma D_78688 : decode_any W_78688 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7868c : bv 32 := 0x00083803.
Lemma F_7868c : fetch_word AsanUbsan.M.loaded_segments (0x78aa4 : word) = Some W_7868c.
Proof. vm_refl. Qed.
Lemma D_7868c : decode_any W_7868c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78690 : bv 32 := 0x0008b883.
Lemma F_78690 : fetch_word AsanUbsan.M.loaded_segments (0x78aa8 : word) = Some W_78690.
Proof. vm_refl. Qed.
Lemma D_78690 : decode_any W_78690 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78694 : bv 32 := 0x0108e833.
Lemma F_78694 : fetch_word AsanUbsan.M.loaded_segments (0x78aac : word) = Some W_78694.
Proof. vm_refl. Qed.
Lemma D_78694 : decode_any W_78694 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78698 : bv 32 := 0x24081a63.
Lemma F_78698 : fetch_word AsanUbsan.M.loaded_segments (0x78ab0 : word) = Some W_78698.
Proof. vm_refl. Qed.
Lemma D_78698 : decode_any W_78698 = Some (Branch BC_NE 16 0 596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7869c : bv 32 := 0x155120ef.
Lemma F_7869c : fetch_word AsanUbsan.M.loaded_segments (0x78ab4 : word) = Some W_7869c.
Proof. vm_refl. Qed.
Lemma D_7869c : decode_any W_7869c = Some (Jal 1 76116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_786a0 : bv 32 := 0x07010113.
Lemma F_786a0 : fetch_word AsanUbsan.M.loaded_segments (0x78ab8 : word) = Some W_786a0.
Proof. vm_refl. Qed.
Lemma D_786a0 : decode_any W_786a0 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_786a4 : bv 32 := 0x7e813083.
Lemma F_786a4 : fetch_word AsanUbsan.M.loaded_segments (0x78abc : word) = Some W_786a4.
Proof. vm_refl. Qed.
Lemma D_786a4 : decode_any W_786a4 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_786a8 : bv 32 := 0x7e013403.
Lemma F_786a8 : fetch_word AsanUbsan.M.loaded_segments (0x78ac0 : word) = Some W_786a8.
Proof. vm_refl. Qed.
Lemma D_786a8 : decode_any W_786a8 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_786ac : bv 32 := 0x7d813483.
Lemma F_786ac : fetch_word AsanUbsan.M.loaded_segments (0x78ac4 : word) = Some W_786ac.
Proof. vm_refl. Qed.
Lemma D_786ac : decode_any W_786ac = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_786b0 : bv 32 := 0x7d013903.
Lemma F_786b0 : fetch_word AsanUbsan.M.loaded_segments (0x78ac8 : word) = Some W_786b0.
Proof. vm_refl. Qed.
Lemma D_786b0 : decode_any W_786b0 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_786b4 : bv 32 := 0x7c813983.
Lemma F_786b4 : fetch_word AsanUbsan.M.loaded_segments (0x78acc : word) = Some W_786b4.
Proof. vm_refl. Qed.
Lemma D_786b4 : decode_any W_786b4 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_786b8 : bv 32 := 0x7c013a03.
Lemma F_786b8 : fetch_word AsanUbsan.M.loaded_segments (0x78ad0 : word) = Some W_786b8.
Proof. vm_refl. Qed.
Lemma D_786b8 : decode_any W_786b8 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_786bc : bv 32 := 0x7b813a83.
Lemma F_786bc : fetch_word AsanUbsan.M.loaded_segments (0x78ad4 : word) = Some W_786bc.
Proof. vm_refl. Qed.
Lemma D_786bc : decode_any W_786bc = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_786c0 : bv 32 := 0x7b013b03.
Lemma F_786c0 : fetch_word AsanUbsan.M.loaded_segments (0x78ad8 : word) = Some W_786c0.
Proof. vm_refl. Qed.
Lemma D_786c0 : decode_any W_786c0 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_786c4 : bv 32 := 0x7a813b83.
Lemma F_786c4 : fetch_word AsanUbsan.M.loaded_segments (0x78adc : word) = Some W_786c4.
Proof. vm_refl. Qed.
Lemma D_786c4 : decode_any W_786c4 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_786c8 : bv 32 := 0x7f010113.
Lemma F_786c8 : fetch_word AsanUbsan.M.loaded_segments (0x78ae0 : word) = Some W_786c8.
Proof. vm_refl. Qed.
Lemma D_786c8 : decode_any W_786c8 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_786cc : bv 32 := 0x00008067.
Lemma F_786cc : fetch_word AsanUbsan.M.loaded_segments (0x78ae4 : word) = Some W_786cc.
Proof. vm_refl. Qed.
Lemma D_786cc : decode_any W_786cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78758 : bv 32 := 0x0c061463.
Lemma F_78758 : fetch_word AsanUbsan.M.loaded_segments (0x78b70 : word) = Some W_78758.
Proof. vm_refl. Qed.
Lemma D_78758 : decode_any W_78758 = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7875c : bv 32 := 0xef5ff06f.
Lemma F_7875c : fetch_word AsanUbsan.M.loaded_segments (0x78b74 : word) = Some W_7875c.
Proof. vm_refl. Qed.
Lemma D_7875c : decode_any W_7875c = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_787e4 : bv 32 := 0x12061e63.
Lemma F_787e4 : fetch_word AsanUbsan.M.loaded_segments (0x78bfc : word) = Some W_787e4.
Proof. vm_refl. Qed.
Lemma D_787e4 : decode_any W_787e4 = Some (Branch BC_NE 12 0 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_787e8 : bv 32 := 0xeb5ff06f.
Lemma F_787e8 : fetch_word AsanUbsan.M.loaded_segments (0x78c00 : word) = Some W_787e8.
Proof. vm_refl. Qed.
Lemma D_787e8 : decode_any W_787e8 = Some (Jal 0 2096820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_787ec : bv 32 := 0x00070803.
Lemma F_787ec : fetch_word AsanUbsan.M.loaded_segments (0x78c04 : word) = Some W_787ec.
Proof. vm_refl. Qed.
Lemma D_787ec : decode_any W_787ec = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_787f0 : bv 32 := 0x0077f793.
Lemma F_787f0 : fetch_word AsanUbsan.M.loaded_segments (0x78c08 : word) = Some W_787f0.
Proof. vm_refl. Qed.
Lemma D_787f0 : decode_any W_787f0 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_787f4 : bv 32 := 0x010038b3.
Lemma F_787f4 : fetch_word AsanUbsan.M.loaded_segments (0x78c0c : word) = Some W_787f4.
Proof. vm_refl. Qed.
Lemma D_787f4 : decode_any W_787f4 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_787f8 : bv 32 := 0x0107a7b3.
Lemma F_787f8 : fetch_word AsanUbsan.M.loaded_segments (0x78c10 : word) = Some W_787f8.
Proof. vm_refl. Qed.
Lemma D_787f8 : decode_any W_787f8 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_787fc : bv 32 := 0x0017c793.
Lemma F_787fc : fetch_word AsanUbsan.M.loaded_segments (0x78c14 : word) = Some W_787fc.
Proof. vm_refl. Qed.
Lemma D_787fc : decode_any W_787fc = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78800 : bv 32 := 0x00f8f7b3.
Lemma F_78800 : fetch_word AsanUbsan.M.loaded_segments (0x78c18 : word) = Some W_78800.
Proof. vm_refl. Qed.
Lemma D_78800 : decode_any W_78800 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78804 : bv 32 := 0x00e6fa63.
Lemma F_78804 : fetch_word AsanUbsan.M.loaded_segments (0x78c1c : word) = Some W_78804.
Proof. vm_refl. Qed.
Lemma D_78804 : decode_any W_78804 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78808 : bv 32 := 0x0006c803.
Lemma F_78808 : fetch_word AsanUbsan.M.loaded_segments (0x78c20 : word) = Some W_78808.
Proof. vm_refl. Qed.
Lemma D_78808 : decode_any W_78808 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7880c : bv 32 := 0x00168693.
Lemma F_7880c : fetch_word AsanUbsan.M.loaded_segments (0x78c24 : word) = Some W_7880c.
Proof. vm_refl. Qed.
Lemma D_7880c : decode_any W_7880c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78810 : bv 32 := 0x00f867b3.
Lemma F_78810 : fetch_word AsanUbsan.M.loaded_segments (0x78c28 : word) = Some W_78810.
Proof. vm_refl. Qed.
Lemma D_78810 : decode_any W_78810 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78814 : bv 32 := 0xfee69ae3.
Lemma F_78814 : fetch_word AsanUbsan.M.loaded_segments (0x78c2c : word) = Some W_78814.
Proof. vm_refl. Qed.
Lemma D_78814 : decode_any W_78814 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78818 : bv 32 := 0x0ff7f693.
Lemma F_78818 : fetch_word AsanUbsan.M.loaded_segments (0x78c30 : word) = Some W_78818.
Proof. vm_refl. Qed.
Lemma D_78818 : decode_any W_78818 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7881c : bv 32 := 0xe2068ae3.
Lemma F_7881c : fetch_word AsanUbsan.M.loaded_segments (0x78c34 : word) = Some W_7881c.
Proof. vm_refl. Qed.
Lemma D_7881c : decode_any W_7881c = Some (Branch BC_EQ 13 0 7732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78820 : bv 32 := 0x00050b13.
Lemma F_78820 : fetch_word AsanUbsan.M.loaded_segments (0x78c38 : word) = Some W_78820.
Proof. vm_refl. Qed.
Lemma D_78820 : decode_any W_78820 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78824 : bv 32 := 0x00058513.
Lemma F_78824 : fetch_word AsanUbsan.M.loaded_segments (0x78c3c : word) = Some W_78824.
Proof. vm_refl. Qed.
Lemma D_78824 : decode_any W_78824 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78828 : bv 32 := 0x00058b93.
Lemma F_78828 : fetch_word AsanUbsan.M.loaded_segments (0x78c40 : word) = Some W_78828.
Proof. vm_refl. Qed.
Lemma D_78828 : decode_any W_78828 = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7882c : bv 32 := 0x00060593.
Lemma F_7882c : fetch_word AsanUbsan.M.loaded_segments (0x78c44 : word) = Some W_7882c.
Proof. vm_refl. Qed.
Lemma D_7882c : decode_any W_7882c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78830 : bv 32 := 0x00060493.
Lemma F_78830 : fetch_word AsanUbsan.M.loaded_segments (0x78c48 : word) = Some W_78830.
Proof. vm_refl. Qed.
Lemma D_78830 : decode_any W_78830 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78834 : bv 32 := 0x075020ef.
Lemma F_78834 : fetch_word AsanUbsan.M.loaded_segments (0x78c4c : word) = Some W_78834.
Proof. vm_refl. Qed.
Lemma D_78834 : decode_any W_78834 = Some (Jal 1 10356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78838 : bv 32 := 0x000b8593.
Lemma F_78838 : fetch_word AsanUbsan.M.loaded_segments (0x78c50 : word) = Some W_78838.
Proof. vm_refl. Qed.
Lemma D_78838 : decode_any W_78838 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7883c : bv 32 := 0x00048613.
Lemma F_7883c : fetch_word AsanUbsan.M.loaded_segments (0x78c54 : word) = Some W_7883c.
Proof. vm_refl. Qed.
Lemma D_7883c : decode_any W_7883c = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78840 : bv 32 := 0x00050913.
Lemma F_78840 : fetch_word AsanUbsan.M.loaded_segments (0x78c58 : word) = Some W_78840.
Proof. vm_refl. Qed.
Lemma D_78840 : decode_any W_78840 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78844 : bv 32 := 0x000b0513.
Lemma F_78844 : fetch_word AsanUbsan.M.loaded_segments (0x78c5c : word) = Some W_78844.
Proof. vm_refl. Qed.
Lemma D_78844 : decode_any W_78844 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78848 : bv 32 := 0xe00904e3.
Lemma F_78848 : fetch_word AsanUbsan.M.loaded_segments (0x78c60 : word) = Some W_78848.
Proof. vm_refl. Qed.
Lemma D_78848 : decode_any W_78848 = Some (Branch BC_EQ 18 0 7688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788ec : bv 32 := 0x00070803.
Lemma F_788ec : fetch_word AsanUbsan.M.loaded_segments (0x78d04 : word) = Some W_788ec.
Proof. vm_refl. Qed.
Lemma D_788ec : decode_any W_788ec = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788f0 : bv 32 := 0x0077f793.
Lemma F_788f0 : fetch_word AsanUbsan.M.loaded_segments (0x78d08 : word) = Some W_788f0.
Proof. vm_refl. Qed.
Lemma D_788f0 : decode_any W_788f0 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788f4 : bv 32 := 0x010038b3.
Lemma F_788f4 : fetch_word AsanUbsan.M.loaded_segments (0x78d0c : word) = Some W_788f4.
Proof. vm_refl. Qed.
Lemma D_788f4 : decode_any W_788f4 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788f8 : bv 32 := 0x0107a7b3.
Lemma F_788f8 : fetch_word AsanUbsan.M.loaded_segments (0x78d10 : word) = Some W_788f8.
Proof. vm_refl. Qed.
Lemma D_788f8 : decode_any W_788f8 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788fc : bv 32 := 0x0017c793.
Lemma F_788fc : fetch_word AsanUbsan.M.loaded_segments (0x78d14 : word) = Some W_788fc.
Proof. vm_refl. Qed.
Lemma D_788fc : decode_any W_788fc = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78900 : bv 32 := 0x00f8f7b3.
Lemma F_78900 : fetch_word AsanUbsan.M.loaded_segments (0x78d18 : word) = Some W_78900.
Proof. vm_refl. Qed.
Lemma D_78900 : decode_any W_78900 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78904 : bv 32 := 0x00e6fa63.
Lemma F_78904 : fetch_word AsanUbsan.M.loaded_segments (0x78d1c : word) = Some W_78904.
Proof. vm_refl. Qed.
Lemma D_78904 : decode_any W_78904 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78908 : bv 32 := 0x0006c803.
Lemma F_78908 : fetch_word AsanUbsan.M.loaded_segments (0x78d20 : word) = Some W_78908.
Proof. vm_refl. Qed.
Lemma D_78908 : decode_any W_78908 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7890c : bv 32 := 0x00168693.
Lemma F_7890c : fetch_word AsanUbsan.M.loaded_segments (0x78d24 : word) = Some W_7890c.
Proof. vm_refl. Qed.
Lemma D_7890c : decode_any W_7890c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78910 : bv 32 := 0x00f867b3.
Lemma F_78910 : fetch_word AsanUbsan.M.loaded_segments (0x78d28 : word) = Some W_78910.
Proof. vm_refl. Qed.
Lemma D_78910 : decode_any W_78910 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78914 : bv 32 := 0xfee69ae3.
Lemma F_78914 : fetch_word AsanUbsan.M.loaded_segments (0x78d2c : word) = Some W_78914.
Proof. vm_refl. Qed.
Lemma D_78914 : decode_any W_78914 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78918 : bv 32 := 0x0ff7f693.
Lemma F_78918 : fetch_word AsanUbsan.M.loaded_segments (0x78d30 : word) = Some W_78918.
Proof. vm_refl. Qed.
Lemma D_78918 : decode_any W_78918 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7891c : bv 32 := 0xd80680e3.
Lemma F_7891c : fetch_word AsanUbsan.M.loaded_segments (0x78d34 : word) = Some W_7891c.
Proof. vm_refl. Qed.
Lemma D_7891c : decode_any W_7891c = Some (Branch BC_EQ 13 0 7552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78920 : bv 32 := 0x00050493.
Lemma F_78920 : fetch_word AsanUbsan.M.loaded_segments (0x78d38 : word) = Some W_78920.
Proof. vm_refl. Qed.
Lemma D_78920 : decode_any W_78920 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78924 : bv 32 := 0x00058b13.
Lemma F_78924 : fetch_word AsanUbsan.M.loaded_segments (0x78d3c : word) = Some W_78924.
Proof. vm_refl. Qed.
Lemma D_78924 : decode_any W_78924 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78928 : bv 32 := 0x00060593.
Lemma F_78928 : fetch_word AsanUbsan.M.loaded_segments (0x78d40 : word) = Some W_78928.
Proof. vm_refl. Qed.
Lemma D_78928 : decode_any W_78928 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7892c : bv 32 := 0x00060913.
Lemma F_7892c : fetch_word AsanUbsan.M.loaded_segments (0x78d44 : word) = Some W_7892c.
Proof. vm_refl. Qed.
Lemma D_7892c : decode_any W_7892c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78930 : bv 32 := 0x778020ef.
Lemma F_78930 : fetch_word AsanUbsan.M.loaded_segments (0x78d48 : word) = Some W_78930.
Proof. vm_refl. Qed.
Lemma D_78930 : decode_any W_78930 = Some (Jal 1 10104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78934 : bv 32 := 0x000b0593.
Lemma F_78934 : fetch_word AsanUbsan.M.loaded_segments (0x78d4c : word) = Some W_78934.
Proof. vm_refl. Qed.
Lemma D_78934 : decode_any W_78934 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78938 : bv 32 := 0x00090613.
Lemma F_78938 : fetch_word AsanUbsan.M.loaded_segments (0x78d50 : word) = Some W_78938.
Proof. vm_refl. Qed.
Lemma D_78938 : decode_any W_78938 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7893c : bv 32 := 0x00050993.
Lemma F_7893c : fetch_word AsanUbsan.M.loaded_segments (0x78d54 : word) = Some W_7893c.
Proof. vm_refl. Qed.
Lemma D_7893c : decode_any W_7893c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78940 : bv 32 := 0x00048513.
Lemma F_78940 : fetch_word AsanUbsan.M.loaded_segments (0x78d58 : word) = Some W_78940.
Proof. vm_refl. Qed.
Lemma D_78940 : decode_any W_78940 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78944 : bv 32 := 0xd4098ce3.
Lemma F_78944 : fetch_word AsanUbsan.M.loaded_segments (0x78d5c : word) = Some W_78944.
Proof. vm_refl. Qed.
Lemma D_78944 : decode_any W_78944 = Some (Branch BC_EQ 19 0 7512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78a78 : bv 32 := 0x81010113.
Lemma F_78a78 : fetch_word AsanUbsan.M.loaded_segments (0x78e90 : word) = Some W_78a78.
Proof. vm_refl. Qed.
Lemma D_78a78 : decode_any W_78a78 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78a7c : bv 32 := 0x7e113423.
Lemma F_78a7c : fetch_word AsanUbsan.M.loaded_segments (0x78e94 : word) = Some W_78a7c.
Proof. vm_refl. Qed.
Lemma D_78a7c : decode_any W_78a7c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78a80 : bv 32 := 0x7e813023.
Lemma F_78a80 : fetch_word AsanUbsan.M.loaded_segments (0x78e98 : word) = Some W_78a80.
Proof. vm_refl. Qed.
Lemma D_78a80 : decode_any W_78a80 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78a84 : bv 32 := 0x7c913c23.
Lemma F_78a84 : fetch_word AsanUbsan.M.loaded_segments (0x78e9c : word) = Some W_78a84.
Proof. vm_refl. Qed.
Lemma D_78a84 : decode_any W_78a84 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78a88 : bv 32 := 0x7d213823.
Lemma F_78a88 : fetch_word AsanUbsan.M.loaded_segments (0x78ea0 : word) = Some W_78a88.
Proof. vm_refl. Qed.
Lemma D_78a88 : decode_any W_78a88 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78a8c : bv 32 := 0x7d313423.
Lemma F_78a8c : fetch_word AsanUbsan.M.loaded_segments (0x78ea4 : word) = Some W_78a8c.
Proof. vm_refl. Qed.
Lemma D_78a8c : decode_any W_78a8c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78a90 : bv 32 := 0x7d413023.
Lemma F_78a90 : fetch_word AsanUbsan.M.loaded_segments (0x78ea8 : word) = Some W_78a90.
Proof. vm_refl. Qed.
Lemma D_78a90 : decode_any W_78a90 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78a94 : bv 32 := 0x7b513c23.
Lemma F_78a94 : fetch_word AsanUbsan.M.loaded_segments (0x78eac : word) = Some W_78a94.
Proof. vm_refl. Qed.
Lemma D_78a94 : decode_any W_78a94 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78a98 : bv 32 := 0x7b613823.
Lemma F_78a98 : fetch_word AsanUbsan.M.loaded_segments (0x78eb0 : word) = Some W_78a98.
Proof. vm_refl. Qed.
Lemma D_78a98 : decode_any W_78a98 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78a9c : bv 32 := 0x7b713423.
Lemma F_78a9c : fetch_word AsanUbsan.M.loaded_segments (0x78eb4 : word) = Some W_78a9c.
Proof. vm_refl. Qed.
Lemma D_78a9c : decode_any W_78a9c = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78aa0 : bv 32 := 0x7b813023.
Lemma F_78aa0 : fetch_word AsanUbsan.M.loaded_segments (0x78eb8 : word) = Some W_78aa0.
Proof. vm_refl. Qed.
Lemma D_78aa0 : decode_any W_78aa0 = Some (Store SZ8 2 24 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78aa4 : bv 32 := 0x7f010413.
Lemma F_78aa4 : fetch_word AsanUbsan.M.loaded_segments (0x78ebc : word) = Some W_78aa4.
Proof. vm_refl. Qed.
Lemma D_78aa4 : decode_any W_78aa4 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78aa8 : bv 32 := 0xf8010113.
Lemma F_78aa8 : fetch_word AsanUbsan.M.loaded_segments (0x78ec0 : word) = Some W_78aa8.
Proof. vm_refl. Qed.
Lemma D_78aa8 : decode_any W_78aa8 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78aac : bv 32 := 0x000bf697.
Lemma F_78aac : fetch_word AsanUbsan.M.loaded_segments (0x78ec4 : word) = Some W_78aac.
Proof. vm_refl. Qed.
Lemma D_78aac : decode_any W_78aac = Some (Auipc 13 191, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ab0 : bv 32 := 0x1646b683.
Lemma F_78ab0 : fetch_word AsanUbsan.M.loaded_segments (0x78ec8 : word) = Some W_78ab0.
Proof. vm_refl. Qed.
Lemma D_78ab0 : decode_any W_78ab0 = Some (Load SZ8 true 13 13 356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ab4 : bv 32 := 0x0006c683.
Lemma F_78ab4 : fetch_word AsanUbsan.M.loaded_segments (0x78ecc : word) = Some W_78ab4.
Proof. vm_refl. Qed.
Lemma D_78ab4 : decode_any W_78ab4 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ab8 : bv 32 := 0x0e068a63.
Lemma F_78ab8 : fetch_word AsanUbsan.M.loaded_segments (0x78ed0 : word) = Some W_78ab8.
Proof. vm_refl. Qed.
Lemma D_78ab8 : decode_any W_78ab8 = Some (Branch BC_EQ 13 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78abc : bv 32 := 0x80040a93.
Lemma F_78abc : fetch_word AsanUbsan.M.loaded_segments (0x78ed4 : word) = Some W_78abc.
Proof. vm_refl. Qed.
Lemma D_78abc : decode_any W_78abc = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ac0 : bv 32 := 0xf98a8a93.
Lemma F_78ac0 : fetch_word AsanUbsan.M.loaded_segments (0x78ed8 : word) = Some W_78ac0.
Proof. vm_refl. Qed.
Lemma D_78ac0 : decode_any W_78ac0 = Some (OpImm ALU_ADD 21 21 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ac4 : bv 32 := 0x00c589b3.
Lemma F_78ac4 : fetch_word AsanUbsan.M.loaded_segments (0x78edc : word) = Some W_78ac4.
Proof. vm_refl. Qed.
Lemma D_78ac4 : decode_any W_78ac4 = Some (Op ALU_ADD 19 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ac8 : bv 32 := 0x00c50a33.
Lemma F_78ac8 : fetch_word AsanUbsan.M.loaded_segments (0x78ee0 : word) = Some W_78ac8.
Proof. vm_refl. Qed.
Lemma D_78ac8 : decode_any W_78ac8 = Some (Op ALU_ADD 20 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78acc : bv 32 := 0x00b50663.
Lemma F_78acc : fetch_word AsanUbsan.M.loaded_segments (0x78ee4 : word) = Some W_78acc.
Proof. vm_refl. Qed.
Lemma D_78acc : decode_any W_78acc = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ad0 : bv 32 := 0x0145f463.
Lemma F_78ad0 : fetch_word AsanUbsan.M.loaded_segments (0x78ee8 : word) = Some W_78ad0.
Proof. vm_refl. Qed.
Lemma D_78ad0 : decode_any W_78ad0 = Some (Branch BC_GEU 11 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ad4 : bv 32 := 0x1b356e63.
Lemma F_78ad4 : fetch_word AsanUbsan.M.loaded_segments (0x78eec : word) = Some W_78ad4.
Proof. vm_refl. Qed.
Lemma D_78ad4 : decode_any W_78ad4 = Some (Branch BC_LTU 10 19 444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ad8 : bv 32 := 0xfff5c693.
Lemma F_78ad8 : fetch_word AsanUbsan.M.loaded_segments (0x78ef0 : word) = Some W_78ad8.
Proof. vm_refl. Qed.
Lemma D_78ad8 : decode_any W_78ad8 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78adc : bv 32 := 0x26c6e863.
Lemma F_78adc : fetch_word AsanUbsan.M.loaded_segments (0x78ef4 : word) = Some W_78adc.
Proof. vm_refl. Qed.
Lemma D_78adc : decode_any W_78adc = Some (Branch BC_LTU 13 12 624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ae0 : bv 32 := 0xfbf60b13.
Lemma F_78ae0 : fetch_word AsanUbsan.M.loaded_segments (0x78ef8 : word) = Some W_78ae0.
Proof. vm_refl. Qed.
Lemma D_78ae0 : decode_any W_78ae0 = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ae4 : bv 32 := 0xfbf00693.
Lemma F_78ae4 : fetch_word AsanUbsan.M.loaded_segments (0x78efc : word) = Some W_78ae4.
Proof. vm_refl. Qed.
Lemma D_78ae4 : decode_any W_78ae4 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ae8 : bv 32 := 0x2f66f663.
Lemma F_78ae8 : fetch_word AsanUbsan.M.loaded_segments (0x78f00 : word) = Some W_78ae8.
Proof. vm_refl. Qed.
Lemma D_78ae8 : decode_any W_78ae8 = Some (Branch BC_GEU 13 22 748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78aec : bv 32 := 0x000be697.
Lemma F_78aec : fetch_word AsanUbsan.M.loaded_segments (0x78f04 : word) = Some W_78aec.
Proof. vm_refl. Qed.
Lemma D_78aec : decode_any W_78aec = Some (Auipc 13 190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78af0 : bv 32 := 0x5bc6b683.
Lemma F_78af0 : fetch_word AsanUbsan.M.loaded_segments (0x78f08 : word) = Some W_78af0.
Proof. vm_refl. Qed.
Lemma D_78af0 : decode_any W_78af0 = Some (Load SZ8 true 13 13 1468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78af4 : bv 32 := 0x0006b703.
Lemma F_78af4 : fetch_word AsanUbsan.M.loaded_segments (0x78f0c : word) = Some W_78af4.
Proof. vm_refl. Qed.
Lemma D_78af4 : decode_any W_78af4 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78af8 : bv 32 := 0xfff98993.
Lemma F_78af8 : fetch_word AsanUbsan.M.loaded_segments (0x78f10 : word) = Some W_78af8.
Proof. vm_refl. Qed.
Lemma D_78af8 : decode_any W_78af8 = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78afc : bv 32 := 0x0035d693.
Lemma F_78afc : fetch_word AsanUbsan.M.loaded_segments (0x78f14 : word) = Some W_78afc.
Proof. vm_refl. Qed.
Lemma D_78afc : decode_any W_78afc = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b00 : bv 32 := 0x0039d793.
Lemma F_78b00 : fetch_word AsanUbsan.M.loaded_segments (0x78f18 : word) = Some W_78b00.
Proof. vm_refl. Qed.
Lemma D_78b00 : decode_any W_78b00 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b04 : bv 32 := 0x00d706b3.
Lemma F_78b04 : fetch_word AsanUbsan.M.loaded_segments (0x78f1c : word) = Some W_78b04.
Proof. vm_refl. Qed.
Lemma D_78b04 : decode_any W_78b04 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b08 : bv 32 := 0x00f70733.
Lemma F_78b08 : fetch_word AsanUbsan.M.loaded_segments (0x78f20 : word) = Some W_78b08.
Proof. vm_refl. Qed.
Lemma D_78b08 : decode_any W_78b08 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b0c : bv 32 := 0xff86f793.
Lemma F_78b0c : fetch_word AsanUbsan.M.loaded_segments (0x78f24 : word) = Some W_78b0c.
Proof. vm_refl. Qed.
Lemma D_78b0c : decode_any W_78b0c = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b10 : bv 32 := 0xff877813.
Lemma F_78b10 : fetch_word AsanUbsan.M.loaded_segments (0x78f28 : word) = Some W_78b10.
Proof. vm_refl. Qed.
Lemma D_78b10 : decode_any W_78b10 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b14 : bv 32 := 0x0007b783.
Lemma F_78b14 : fetch_word AsanUbsan.M.loaded_segments (0x78f2c : word) = Some W_78b14.
Proof. vm_refl. Qed.
Lemma D_78b14 : decode_any W_78b14 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b18 : bv 32 := 0x00083803.
Lemma F_78b18 : fetch_word AsanUbsan.M.loaded_segments (0x78f30 : word) = Some W_78b18.
Proof. vm_refl. Qed.
Lemma D_78b18 : decode_any W_78b18 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b1c : bv 32 := 0x00f867b3.
Lemma F_78b1c : fetch_word AsanUbsan.M.loaded_segments (0x78f34 : word) = Some W_78b1c.
Proof. vm_refl. Qed.
Lemma D_78b1c : decode_any W_78b1c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b20 : bv 32 := 0x2a079e63.
Lemma F_78b20 : fetch_word AsanUbsan.M.loaded_segments (0x78f38 : word) = Some W_78b20.
Proof. vm_refl. Qed.
Lemma D_78b20 : decode_any W_78b20 = Some (Branch BC_NE 15 0 700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b24 : bv 32 := 0xfff54693.
Lemma F_78b24 : fetch_word AsanUbsan.M.loaded_segments (0x78f3c : word) = Some W_78b24.
Proof. vm_refl. Qed.
Lemma D_78b24 : decode_any W_78b24 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b28 : bv 32 := 0x0cc6ee63.
Lemma F_78b28 : fetch_word AsanUbsan.M.loaded_segments (0x78f40 : word) = Some W_78b28.
Proof. vm_refl. Qed.
Lemma D_78b28 : decode_any W_78b28 = Some (Branch BC_LTU 13 12 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b2c : bv 32 := 0xfbf00693.
Lemma F_78b2c : fetch_word AsanUbsan.M.loaded_segments (0x78f44 : word) = Some W_78b2c.
Proof. vm_refl. Qed.
Lemma D_78b2c : decode_any W_78b2c = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b30 : bv 32 := 0x1566fc63.
Lemma F_78b30 : fetch_word AsanUbsan.M.loaded_segments (0x78f48 : word) = Some W_78b30.
Proof. vm_refl. Qed.
Lemma D_78b30 : decode_any W_78b30 = Some (Branch BC_GEU 13 22 344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b34 : bv 32 := 0x000be697.
Lemma F_78b34 : fetch_word AsanUbsan.M.loaded_segments (0x78f4c : word) = Some W_78b34.
Proof. vm_refl. Qed.
Lemma D_78b34 : decode_any W_78b34 = Some (Auipc 13 190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b38 : bv 32 := 0x5746b683.
Lemma F_78b38 : fetch_word AsanUbsan.M.loaded_segments (0x78f50 : word) = Some W_78b38.
Proof. vm_refl. Qed.
Lemma D_78b38 : decode_any W_78b38 = Some (Load SZ8 true 13 13 1396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b3c : bv 32 := 0x0006b703.
Lemma F_78b3c : fetch_word AsanUbsan.M.loaded_segments (0x78f54 : word) = Some W_78b3c.
Proof. vm_refl. Qed.
Lemma D_78b3c : decode_any W_78b3c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b40 : bv 32 := 0xfffa0a13.
Lemma F_78b40 : fetch_word AsanUbsan.M.loaded_segments (0x78f58 : word) = Some W_78b40.
Proof. vm_refl. Qed.
Lemma D_78b40 : decode_any W_78b40 = Some (OpImm ALU_ADD 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b44 : bv 32 := 0x00355693.
Lemma F_78b44 : fetch_word AsanUbsan.M.loaded_segments (0x78f5c : word) = Some W_78b44.
Proof. vm_refl. Qed.
Lemma D_78b44 : decode_any W_78b44 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b48 : bv 32 := 0x003a5793.
Lemma F_78b48 : fetch_word AsanUbsan.M.loaded_segments (0x78f60 : word) = Some W_78b48.
Proof. vm_refl. Qed.
Lemma D_78b48 : decode_any W_78b48 = Some (ShiftImm ALU_SRL 15 20 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b4c : bv 32 := 0x00d706b3.
Lemma F_78b4c : fetch_word AsanUbsan.M.loaded_segments (0x78f64 : word) = Some W_78b4c.
Proof. vm_refl. Qed.
Lemma D_78b4c : decode_any W_78b4c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b50 : bv 32 := 0x00f70733.
Lemma F_78b50 : fetch_word AsanUbsan.M.loaded_segments (0x78f68 : word) = Some W_78b50.
Proof. vm_refl. Qed.
Lemma D_78b50 : decode_any W_78b50 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b54 : bv 32 := 0xff86f793.
Lemma F_78b54 : fetch_word AsanUbsan.M.loaded_segments (0x78f6c : word) = Some W_78b54.
Proof. vm_refl. Qed.
Lemma D_78b54 : decode_any W_78b54 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b58 : bv 32 := 0xff877813.
Lemma F_78b58 : fetch_word AsanUbsan.M.loaded_segments (0x78f70 : word) = Some W_78b58.
Proof. vm_refl. Qed.
Lemma D_78b58 : decode_any W_78b58 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b5c : bv 32 := 0x0007b783.
Lemma F_78b5c : fetch_word AsanUbsan.M.loaded_segments (0x78f74 : word) = Some W_78b5c.
Proof. vm_refl. Qed.
Lemma D_78b5c : decode_any W_78b5c = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b60 : bv 32 := 0x00083803.
Lemma F_78b60 : fetch_word AsanUbsan.M.loaded_segments (0x78f78 : word) = Some W_78b60.
Proof. vm_refl. Qed.
Lemma D_78b60 : decode_any W_78b60 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b64 : bv 32 := 0x00f867b3.
Lemma F_78b64 : fetch_word AsanUbsan.M.loaded_segments (0x78f7c : word) = Some W_78b64.
Proof. vm_refl. Qed.
Lemma D_78b64 : decode_any W_78b64 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b68 : bv 32 := 0x36079a63.
Lemma F_78b68 : fetch_word AsanUbsan.M.loaded_segments (0x78f80 : word) = Some W_78b68.
Proof. vm_refl. Qed.
Lemma D_78b68 : decode_any W_78b68 = Some (Branch BC_NE 15 0 884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b6c : bv 32 := 0x000c0697.
Lemma F_78b6c : fetch_word AsanUbsan.M.loaded_segments (0x78f84 : word) = Some W_78b6c.
Proof. vm_refl. Qed.
Lemma D_78b6c : decode_any W_78b6c = Some (Auipc 13 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b70 : bv 32 := 0x5446b683.
Lemma F_78b70 : fetch_word AsanUbsan.M.loaded_segments (0x78f88 : word) = Some W_78b70.
Proof. vm_refl. Qed.
Lemma D_78b70 : decode_any W_78b70 = Some (Load SZ8 true 13 13 1348, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b74 : bv 32 := 0x000680e7.
Lemma F_78b74 : fetch_word AsanUbsan.M.loaded_segments (0x78f8c : word) = Some W_78b74.
Proof. vm_refl. Qed.
Lemma D_78b74 : decode_any W_78b74 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b78 : bv 32 := 0x08010113.
Lemma F_78b78 : fetch_word AsanUbsan.M.loaded_segments (0x78f90 : word) = Some W_78b78.
Proof. vm_refl. Qed.
Lemma D_78b78 : decode_any W_78b78 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b7c : bv 32 := 0x7e813083.
Lemma F_78b7c : fetch_word AsanUbsan.M.loaded_segments (0x78f94 : word) = Some W_78b7c.
Proof. vm_refl. Qed.
Lemma D_78b7c : decode_any W_78b7c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b80 : bv 32 := 0x7e013403.
Lemma F_78b80 : fetch_word AsanUbsan.M.loaded_segments (0x78f98 : word) = Some W_78b80.
Proof. vm_refl. Qed.
Lemma D_78b80 : decode_any W_78b80 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b84 : bv 32 := 0x7d813483.
Lemma F_78b84 : fetch_word AsanUbsan.M.loaded_segments (0x78f9c : word) = Some W_78b84.
Proof. vm_refl. Qed.
Lemma D_78b84 : decode_any W_78b84 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b88 : bv 32 := 0x7d013903.
Lemma F_78b88 : fetch_word AsanUbsan.M.loaded_segments (0x78fa0 : word) = Some W_78b88.
Proof. vm_refl. Qed.
Lemma D_78b88 : decode_any W_78b88 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b8c : bv 32 := 0x7c813983.
Lemma F_78b8c : fetch_word AsanUbsan.M.loaded_segments (0x78fa4 : word) = Some W_78b8c.
Proof. vm_refl. Qed.
Lemma D_78b8c : decode_any W_78b8c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b90 : bv 32 := 0x7c013a03.
Lemma F_78b90 : fetch_word AsanUbsan.M.loaded_segments (0x78fa8 : word) = Some W_78b90.
Proof. vm_refl. Qed.
Lemma D_78b90 : decode_any W_78b90 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b94 : bv 32 := 0x7b813a83.
Lemma F_78b94 : fetch_word AsanUbsan.M.loaded_segments (0x78fac : word) = Some W_78b94.
Proof. vm_refl. Qed.
Lemma D_78b94 : decode_any W_78b94 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b98 : bv 32 := 0x7b013b03.
Lemma F_78b98 : fetch_word AsanUbsan.M.loaded_segments (0x78fb0 : word) = Some W_78b98.
Proof. vm_refl. Qed.
Lemma D_78b98 : decode_any W_78b98 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b9c : bv 32 := 0x7a813b83.
Lemma F_78b9c : fetch_word AsanUbsan.M.loaded_segments (0x78fb4 : word) = Some W_78b9c.
Proof. vm_refl. Qed.
Lemma D_78b9c : decode_any W_78b9c = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ba0 : bv 32 := 0x7a013c03.
Lemma F_78ba0 : fetch_word AsanUbsan.M.loaded_segments (0x78fb8 : word) = Some W_78ba0.
Proof. vm_refl. Qed.
Lemma D_78ba0 : decode_any W_78ba0 = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ba4 : bv 32 := 0x7f010113.
Lemma F_78ba4 : fetch_word AsanUbsan.M.loaded_segments (0x78fbc : word) = Some W_78ba4.
Proof. vm_refl. Qed.
Lemma D_78ba4 : decode_any W_78ba4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ba8 : bv 32 := 0x00008067.
Lemma F_78ba8 : fetch_word AsanUbsan.M.loaded_segments (0x78fc0 : word) = Some W_78ba8.
Proof. vm_refl. Qed.
Lemma D_78ba8 : decode_any W_78ba8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c88 : bv 32 := 0x28061463.
Lemma F_78c88 : fetch_word AsanUbsan.M.loaded_segments (0x790a0 : word) = Some W_78c88.
Proof. vm_refl. Qed.
Lemma D_78c88 : decode_any W_78c88 = Some (Branch BC_NE 12 0 648, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c8c : bv 32 := 0xee1ff06f.
Lemma F_78c8c : fetch_word AsanUbsan.M.loaded_segments (0x790a4 : word) = Some W_78c8c.
Proof. vm_refl. Qed.
Lemma D_78c8c : decode_any W_78c8c = Some (Jal 0 2096864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dd4 : bv 32 := 0x02061e63.
Lemma F_78dd4 : fetch_word AsanUbsan.M.loaded_segments (0x791ec : word) = Some W_78dd4.
Proof. vm_refl. Qed.
Lemma D_78dd4 : decode_any W_78dd4 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dd8 : bv 32 := 0xd4dff06f.
Lemma F_78dd8 : fetch_word AsanUbsan.M.loaded_segments (0x791f0 : word) = Some W_78dd8.
Proof. vm_refl. Qed.
Lemma D_78dd8 : decode_any W_78dd8 = Some (Jal 0 2096460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ddc : bv 32 := 0x00070783.
Lemma F_78ddc : fetch_word AsanUbsan.M.loaded_segments (0x791f4 : word) = Some W_78ddc.
Proof. vm_refl. Qed.
Lemma D_78ddc : decode_any W_78ddc = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78de0 : bv 32 := 0x0079f813.
Lemma F_78de0 : fetch_word AsanUbsan.M.loaded_segments (0x791f8 : word) = Some W_78de0.
Proof. vm_refl. Qed.
Lemma D_78de0 : decode_any W_78de0 = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78de4 : bv 32 := 0x00f038b3.
Lemma F_78de4 : fetch_word AsanUbsan.M.loaded_segments (0x791fc : word) = Some W_78de4.
Proof. vm_refl. Qed.
Lemma D_78de4 : decode_any W_78de4 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78de8 : bv 32 := 0x00f827b3.
Lemma F_78de8 : fetch_word AsanUbsan.M.loaded_segments (0x79200 : word) = Some W_78de8.
Proof. vm_refl. Qed.
Lemma D_78de8 : decode_any W_78de8 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dec : bv 32 := 0x0017c793.
Lemma F_78dec : fetch_word AsanUbsan.M.loaded_segments (0x79204 : word) = Some W_78dec.
Proof. vm_refl. Qed.
Lemma D_78dec : decode_any W_78dec = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78df0 : bv 32 := 0x00f8f7b3.
Lemma F_78df0 : fetch_word AsanUbsan.M.loaded_segments (0x79208 : word) = Some W_78df0.
Proof. vm_refl. Qed.
Lemma D_78df0 : decode_any W_78df0 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78df4 : bv 32 := 0x00e6fa63.
Lemma F_78df4 : fetch_word AsanUbsan.M.loaded_segments (0x7920c : word) = Some W_78df4.
Proof. vm_refl. Qed.
Lemma D_78df4 : decode_any W_78df4 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78df8 : bv 32 := 0x0006c803.
Lemma F_78df8 : fetch_word AsanUbsan.M.loaded_segments (0x79210 : word) = Some W_78df8.
Proof. vm_refl. Qed.
Lemma D_78df8 : decode_any W_78df8 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dfc : bv 32 := 0x00168693.
Lemma F_78dfc : fetch_word AsanUbsan.M.loaded_segments (0x79214 : word) = Some W_78dfc.
Proof. vm_refl. Qed.
Lemma D_78dfc : decode_any W_78dfc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e00 : bv 32 := 0x00f867b3.
Lemma F_78e00 : fetch_word AsanUbsan.M.loaded_segments (0x79218 : word) = Some W_78e00.
Proof. vm_refl. Qed.
Lemma D_78e00 : decode_any W_78e00 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e04 : bv 32 := 0xfee69ae3.
Lemma F_78e04 : fetch_word AsanUbsan.M.loaded_segments (0x7921c : word) = Some W_78e04.
Proof. vm_refl. Qed.
Lemma D_78e04 : decode_any W_78e04 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e08 : bv 32 := 0x0ff7f693.
Lemma F_78e08 : fetch_word AsanUbsan.M.loaded_segments (0x79220 : word) = Some W_78e08.
Proof. vm_refl. Qed.
Lemma D_78e08 : decode_any W_78e08 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e0c : bv 32 := 0xd0068ce3.
Lemma F_78e0c : fetch_word AsanUbsan.M.loaded_segments (0x79224 : word) = Some W_78e0c.
Proof. vm_refl. Qed.
Lemma D_78e0c : decode_any W_78e0c = Some (Branch BC_EQ 13 0 7448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e10 : bv 32 := 0x00050b93.
Lemma F_78e10 : fetch_word AsanUbsan.M.loaded_segments (0x79228 : word) = Some W_78e10.
Proof. vm_refl. Qed.
Lemma D_78e10 : decode_any W_78e10 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e14 : bv 32 := 0x00058513.
Lemma F_78e14 : fetch_word AsanUbsan.M.loaded_segments (0x7922c : word) = Some W_78e14.
Proof. vm_refl. Qed.
Lemma D_78e14 : decode_any W_78e14 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e18 : bv 32 := 0x00058c13.
Lemma F_78e18 : fetch_word AsanUbsan.M.loaded_segments (0x79230 : word) = Some W_78e18.
Proof. vm_refl. Qed.
Lemma D_78e18 : decode_any W_78e18 = Some (OpImm ALU_ADD 24 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e1c : bv 32 := 0x00060593.
Lemma F_78e1c : fetch_word AsanUbsan.M.loaded_segments (0x79234 : word) = Some W_78e1c.
Proof. vm_refl. Qed.
Lemma D_78e1c : decode_any W_78e1c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e20 : bv 32 := 0x00060493.
Lemma F_78e20 : fetch_word AsanUbsan.M.loaded_segments (0x79238 : word) = Some W_78e20.
Proof. vm_refl. Qed.
Lemma D_78e20 : decode_any W_78e20 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e24 : bv 32 := 0x284020ef.
Lemma F_78e24 : fetch_word AsanUbsan.M.loaded_segments (0x7923c : word) = Some W_78e24.
Proof. vm_refl. Qed.
Lemma D_78e24 : decode_any W_78e24 = Some (Jal 1 8836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e28 : bv 32 := 0x000c0593.
Lemma F_78e28 : fetch_word AsanUbsan.M.loaded_segments (0x79240 : word) = Some W_78e28.
Proof. vm_refl. Qed.
Lemma D_78e28 : decode_any W_78e28 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e2c : bv 32 := 0x00048613.
Lemma F_78e2c : fetch_word AsanUbsan.M.loaded_segments (0x79244 : word) = Some W_78e2c.
Proof. vm_refl. Qed.
Lemma D_78e2c : decode_any W_78e2c = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e30 : bv 32 := 0x00050913.
Lemma F_78e30 : fetch_word AsanUbsan.M.loaded_segments (0x79248 : word) = Some W_78e30.
Proof. vm_refl. Qed.
Lemma D_78e30 : decode_any W_78e30 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e34 : bv 32 := 0x000b8513.
Lemma F_78e34 : fetch_word AsanUbsan.M.loaded_segments (0x7924c : word) = Some W_78e34.
Proof. vm_refl. Qed.
Lemma D_78e34 : decode_any W_78e34 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e38 : bv 32 := 0xce0906e3.
Lemma F_78e38 : fetch_word AsanUbsan.M.loaded_segments (0x79250 : word) = Some W_78e38.
Proof. vm_refl. Qed.
Lemma D_78e38 : decode_any W_78e38 = Some (Branch BC_EQ 18 0 7404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78edc : bv 32 := 0x00070783.
Lemma F_78edc : fetch_word AsanUbsan.M.loaded_segments (0x792f4 : word) = Some W_78edc.
Proof. vm_refl. Qed.
Lemma D_78edc : decode_any W_78edc = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ee0 : bv 32 := 0x007a7813.
Lemma F_78ee0 : fetch_word AsanUbsan.M.loaded_segments (0x792f8 : word) = Some W_78ee0.
Proof. vm_refl. Qed.
Lemma D_78ee0 : decode_any W_78ee0 = Some (OpImm ALU_AND 16 20 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ee4 : bv 32 := 0x00f038b3.
Lemma F_78ee4 : fetch_word AsanUbsan.M.loaded_segments (0x792fc : word) = Some W_78ee4.
Proof. vm_refl. Qed.
Lemma D_78ee4 : decode_any W_78ee4 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ee8 : bv 32 := 0x00f827b3.
Lemma F_78ee8 : fetch_word AsanUbsan.M.loaded_segments (0x79300 : word) = Some W_78ee8.
Proof. vm_refl. Qed.
Lemma D_78ee8 : decode_any W_78ee8 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78eec : bv 32 := 0x0017c793.
Lemma F_78eec : fetch_word AsanUbsan.M.loaded_segments (0x79304 : word) = Some W_78eec.
Proof. vm_refl. Qed.
Lemma D_78eec : decode_any W_78eec = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ef0 : bv 32 := 0x00f8f7b3.
Lemma F_78ef0 : fetch_word AsanUbsan.M.loaded_segments (0x79308 : word) = Some W_78ef0.
Proof. vm_refl. Qed.
Lemma D_78ef0 : decode_any W_78ef0 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ef4 : bv 32 := 0x00e6fa63.
Lemma F_78ef4 : fetch_word AsanUbsan.M.loaded_segments (0x7930c : word) = Some W_78ef4.
Proof. vm_refl. Qed.
Lemma D_78ef4 : decode_any W_78ef4 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ef8 : bv 32 := 0x0006c803.
Lemma F_78ef8 : fetch_word AsanUbsan.M.loaded_segments (0x79310 : word) = Some W_78ef8.
Proof. vm_refl. Qed.
Lemma D_78ef8 : decode_any W_78ef8 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78efc : bv 32 := 0x00168693.
Lemma F_78efc : fetch_word AsanUbsan.M.loaded_segments (0x79314 : word) = Some W_78efc.
Proof. vm_refl. Qed.
Lemma D_78efc : decode_any W_78efc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f00 : bv 32 := 0x00f867b3.
Lemma F_78f00 : fetch_word AsanUbsan.M.loaded_segments (0x79318 : word) = Some W_78f00.
Proof. vm_refl. Qed.
Lemma D_78f00 : decode_any W_78f00 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f04 : bv 32 := 0xfee69ae3.
Lemma F_78f04 : fetch_word AsanUbsan.M.loaded_segments (0x7931c : word) = Some W_78f04.
Proof. vm_refl. Qed.
Lemma D_78f04 : decode_any W_78f04 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f08 : bv 32 := 0x0ff7f693.
Lemma F_78f08 : fetch_word AsanUbsan.M.loaded_segments (0x79320 : word) = Some W_78f08.
Proof. vm_refl. Qed.
Lemma D_78f08 : decode_any W_78f08 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f0c : bv 32 := 0xc60680e3.
Lemma F_78f0c : fetch_word AsanUbsan.M.loaded_segments (0x79324 : word) = Some W_78f0c.
Proof. vm_refl. Qed.
Lemma D_78f0c : decode_any W_78f0c = Some (Branch BC_EQ 13 0 7264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f10 : bv 32 := 0x00050493.
Lemma F_78f10 : fetch_word AsanUbsan.M.loaded_segments (0x79328 : word) = Some W_78f10.
Proof. vm_refl. Qed.
Lemma D_78f10 : decode_any W_78f10 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f14 : bv 32 := 0x00058b13.
Lemma F_78f14 : fetch_word AsanUbsan.M.loaded_segments (0x7932c : word) = Some W_78f14.
Proof. vm_refl. Qed.
Lemma D_78f14 : decode_any W_78f14 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f18 : bv 32 := 0x00060593.
Lemma F_78f18 : fetch_word AsanUbsan.M.loaded_segments (0x79330 : word) = Some W_78f18.
Proof. vm_refl. Qed.
Lemma D_78f18 : decode_any W_78f18 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f1c : bv 32 := 0x00060913.
Lemma F_78f1c : fetch_word AsanUbsan.M.loaded_segments (0x79334 : word) = Some W_78f1c.
Proof. vm_refl. Qed.
Lemma D_78f1c : decode_any W_78f1c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f20 : bv 32 := 0x188020ef.
Lemma F_78f20 : fetch_word AsanUbsan.M.loaded_segments (0x79338 : word) = Some W_78f20.
Proof. vm_refl. Qed.
Lemma D_78f20 : decode_any W_78f20 = Some (Jal 1 8584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f24 : bv 32 := 0x000b0593.
Lemma F_78f24 : fetch_word AsanUbsan.M.loaded_segments (0x7933c : word) = Some W_78f24.
Proof. vm_refl. Qed.
Lemma D_78f24 : decode_any W_78f24 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f28 : bv 32 := 0x00090613.
Lemma F_78f28 : fetch_word AsanUbsan.M.loaded_segments (0x79340 : word) = Some W_78f28.
Proof. vm_refl. Qed.
Lemma D_78f28 : decode_any W_78f28 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f2c : bv 32 := 0x00050993.
Lemma F_78f2c : fetch_word AsanUbsan.M.loaded_segments (0x79344 : word) = Some W_78f2c.
Proof. vm_refl. Qed.
Lemma D_78f2c : decode_any W_78f2c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f30 : bv 32 := 0x00048513.
Lemma F_78f30 : fetch_word AsanUbsan.M.loaded_segments (0x79348 : word) = Some W_78f30.
Proof. vm_refl. Qed.
Lemma D_78f30 : decode_any W_78f30 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f34 : bv 32 := 0xc2098ce3.
Lemma F_78f34 : fetch_word AsanUbsan.M.loaded_segments (0x7934c : word) = Some W_78f34.
Proof. vm_refl. Qed.
Lemma D_78f34 : decode_any W_78f34 = Some (Branch BC_EQ 19 0 7224, 4%Z).
Proof. vm_refl. Qed.
