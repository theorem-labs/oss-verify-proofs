(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_dd000 : bv 32 := 0x0040006f.
Lemma F_dd000 : fetch_word Ubsan.M.loaded_segments (0xe1938 : word) = Some W_dd000.
Proof. vm_refl. Qed.
Lemma D_dd000 : decode_any W_dd000 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd004 : bv 32 := 0x0023d517.
Lemma F_dd004 : fetch_word Ubsan.M.loaded_segments (0xe193c : word) = Some W_dd004.
Proof. vm_refl. Qed.
Lemma D_dd004 : decode_any W_dd004 = Some (Auipc 10 573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd008 : bv 32 := 0xc8c50513.
Lemma F_dd008 : fetch_word Ubsan.M.loaded_segments (0xe1940 : word) = Some W_dd008.
Proof. vm_refl. Qed.
Lemma D_dd008 : decode_any W_dd008 = Some (OpImm ALU_ADD 10 10 3212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd00c : bv 32 := 0x00053503.
Lemma F_dd00c : fetch_word Ubsan.M.loaded_segments (0xe1944 : word) = Some W_dd00c.
Proof. vm_refl. Qed.
Lemma D_dd00c : decode_any W_dd00c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd010 : bv 32 := 0x001d0097.
Lemma F_dd010 : fetch_word Ubsan.M.loaded_segments (0xe1948 : word) = Some W_dd010.
Proof. vm_refl. Qed.
Lemma D_dd010 : decode_any W_dd010 = Some (Auipc 1 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd014 : bv 32 := 0xd88080e7.
Lemma F_dd014 : fetch_word Ubsan.M.loaded_segments (0xe194c : word) = Some W_dd014.
Proof. vm_refl. Qed.
Lemma D_dd014 : decode_any W_dd014 = Some (Jalr 1 1 3464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd018 : bv 32 := 0x0040006f.
Lemma F_dd018 : fetch_word Ubsan.M.loaded_segments (0xe1950 : word) = Some W_dd018.
Proof. vm_refl. Qed.
Lemma D_dd018 : decode_any W_dd018 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd01c : bv 32 := 0x0023b517.
Lemma F_dd01c : fetch_word Ubsan.M.loaded_segments (0xe1954 : word) = Some W_dd01c.
Proof. vm_refl. Qed.
Lemma D_dd01c : decode_any W_dd01c = Some (Auipc 10 571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd020 : bv 32 := 0x69453503.
Lemma F_dd020 : fetch_word Ubsan.M.loaded_segments (0xe1958 : word) = Some W_dd020.
Proof. vm_refl. Qed.
Lemma D_dd020 : decode_any W_dd020 = Some (Load SZ8 true 10 10 1684, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd024 : bv 32 := 0x00050c63.
Lemma F_dd024 : fetch_word Ubsan.M.loaded_segments (0xe195c : word) = Some W_dd024.
Proof. vm_refl. Qed.
Lemma D_dd024 : decode_any W_dd024 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd028 : bv 32 := 0x0040006f.
Lemma F_dd028 : fetch_word Ubsan.M.loaded_segments (0xe1960 : word) = Some W_dd028.
Proof. vm_refl. Qed.
Lemma D_dd028 : decode_any W_dd028 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd02c : bv 32 := 0xfffa0517.
Lemma F_dd02c : fetch_word Ubsan.M.loaded_segments (0xe1964 : word) = Some W_dd02c.
Proof. vm_refl. Qed.
Lemma D_dd02c : decode_any W_dd02c = Some (Auipc 10 1048480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd030 : bv 32 := 0x22450513.
Lemma F_dd030 : fetch_word Ubsan.M.loaded_segments (0xe1968 : word) = Some W_dd030.
Proof. vm_refl. Qed.
Lemma D_dd030 : decode_any W_dd030 = Some (OpImm ALU_ADD 10 10 548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd034 : bv 32 := 0x000000ef.
Lemma F_dd034 : fetch_word Ubsan.M.loaded_segments (0xe196c : word) = Some W_dd034.
Proof. vm_refl. Qed.
Lemma D_dd034 : decode_any W_dd034 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd038 : bv 32 := 0x0040006f.
Lemma F_dd038 : fetch_word Ubsan.M.loaded_segments (0xe1970 : word) = Some W_dd038.
Proof. vm_refl. Qed.
Lemma D_dd038 : decode_any W_dd038 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd03c : bv 32 := 0x00813083.
Lemma F_dd03c : fetch_word Ubsan.M.loaded_segments (0xe1974 : word) = Some W_dd03c.
Proof. vm_refl. Qed.
Lemma D_dd03c : decode_any W_dd03c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd040 : bv 32 := 0x00013403.
Lemma F_dd040 : fetch_word Ubsan.M.loaded_segments (0xe1978 : word) = Some W_dd040.
Proof. vm_refl. Qed.
Lemma D_dd040 : decode_any W_dd040 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd044 : bv 32 := 0x01010113.
Lemma F_dd044 : fetch_word Ubsan.M.loaded_segments (0xe197c : word) = Some W_dd044.
Proof. vm_refl. Qed.
Lemma D_dd044 : decode_any W_dd044 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd048 : bv 32 := 0x00008067.
Lemma F_dd048 : fetch_word Ubsan.M.loaded_segments (0xe1980 : word) = Some W_dd048.
Proof. vm_refl. Qed.
Lemma D_dd048 : decode_any W_dd048 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd04c : bv 32 := 0xfb010113.
Lemma F_dd04c : fetch_word Ubsan.M.loaded_segments (0xe1984 : word) = Some W_dd04c.
Proof. vm_refl. Qed.
Lemma D_dd04c : decode_any W_dd04c = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd050 : bv 32 := 0x04113423.
Lemma F_dd050 : fetch_word Ubsan.M.loaded_segments (0xe1988 : word) = Some W_dd050.
Proof. vm_refl. Qed.
Lemma D_dd050 : decode_any W_dd050 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd054 : bv 32 := 0x04813023.
Lemma F_dd054 : fetch_word Ubsan.M.loaded_segments (0xe198c : word) = Some W_dd054.
Proof. vm_refl. Qed.
Lemma D_dd054 : decode_any W_dd054 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd058 : bv 32 := 0x02913c23.
Lemma F_dd058 : fetch_word Ubsan.M.loaded_segments (0xe1990 : word) = Some W_dd058.
Proof. vm_refl. Qed.
Lemma D_dd058 : decode_any W_dd058 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd05c : bv 32 := 0x03213823.
Lemma F_dd05c : fetch_word Ubsan.M.loaded_segments (0xe1994 : word) = Some W_dd05c.
Proof. vm_refl. Qed.
Lemma D_dd05c : decode_any W_dd05c = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd060 : bv 32 := 0x03313423.
Lemma F_dd060 : fetch_word Ubsan.M.loaded_segments (0xe1998 : word) = Some W_dd060.
Proof. vm_refl. Qed.
Lemma D_dd060 : decode_any W_dd060 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd064 : bv 32 := 0x03413023.
Lemma F_dd064 : fetch_word Ubsan.M.loaded_segments (0xe199c : word) = Some W_dd064.
Proof. vm_refl. Qed.
Lemma D_dd064 : decode_any W_dd064 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd068 : bv 32 := 0x01513c23.
Lemma F_dd068 : fetch_word Ubsan.M.loaded_segments (0xe19a0 : word) = Some W_dd068.
Proof. vm_refl. Qed.
Lemma D_dd068 : decode_any W_dd068 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd06c : bv 32 := 0x01613823.
Lemma F_dd06c : fetch_word Ubsan.M.loaded_segments (0xe19a4 : word) = Some W_dd06c.
Proof. vm_refl. Qed.
Lemma D_dd06c : decode_any W_dd06c = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd070 : bv 32 := 0x01713423.
Lemma F_dd070 : fetch_word Ubsan.M.loaded_segments (0xe19a8 : word) = Some W_dd070.
Proof. vm_refl. Qed.
Lemma D_dd070 : decode_any W_dd070 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd074 : bv 32 := 0x00200413.
Lemma F_dd074 : fetch_word Ubsan.M.loaded_segments (0xe19ac : word) = Some W_dd074.
Proof. vm_refl. Qed.
Lemma D_dd074 : decode_any W_dd074 = Some (OpImm ALU_ADD 8 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd078 : bv 32 := 0x18851663.
Lemma F_dd078 : fetch_word Ubsan.M.loaded_segments (0xe19b0 : word) = Some W_dd078.
Proof. vm_refl. Qed.
Lemma D_dd078 : decode_any W_dd078 = Some (Branch BC_NE 10 8 396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd07c : bv 32 := 0x0085b903.
Lemma F_dd07c : fetch_word Ubsan.M.loaded_segments (0xe19b4 : word) = Some W_dd07c.
Proof. vm_refl. Qed.
Lemma D_dd07c : decode_any W_dd07c = Some (Load SZ8 true 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd080 : bv 32 := 0x00090513.
Lemma F_dd080 : fetch_word Ubsan.M.loaded_segments (0xe19b8 : word) = Some W_dd080.
Proof. vm_refl. Qed.
Lemma D_dd080 : decode_any W_dd080 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd084 : bv 32 := 0x00000593.
Lemma F_dd084 : fetch_word Ubsan.M.loaded_segments (0xe19bc : word) = Some W_dd084.
Proof. vm_refl. Qed.
Lemma D_dd084 : decode_any W_dd084 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd088 : bv 32 := 0x001d0097.
Lemma F_dd088 : fetch_word Ubsan.M.loaded_segments (0xe19c0 : word) = Some W_dd088.
Proof. vm_refl. Qed.
Lemma D_dd088 : decode_any W_dd088 = Some (Auipc 1 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd08c : bv 32 := 0xea0080e7.
Lemma F_dd08c : fetch_word Ubsan.M.loaded_segments (0xe19c4 : word) = Some W_dd08c.
Proof. vm_refl. Qed.
Lemma D_dd08c : decode_any W_dd08c = Some (Jalr 1 1 3744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd090 : bv 32 := 0x28054263.
Lemma F_dd090 : fetch_word Ubsan.M.loaded_segments (0xe19c8 : word) = Some W_dd090.
Proof. vm_refl. Qed.
Lemma D_dd090 : decode_any W_dd090 = Some (Branch BC_LT 10 0 644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd094 : bv 32 := 0x00050a13.
Lemma F_dd094 : fetch_word Ubsan.M.loaded_segments (0xe19cc : word) = Some W_dd094.
Proof. vm_refl. Qed.
Lemma D_dd094 : decode_any W_dd094 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd098 : bv 32 := 0x00010537.
Lemma F_dd098 : fetch_word Ubsan.M.loaded_segments (0xe19d0 : word) = Some W_dd098.
Proof. vm_refl. Qed.
Lemma D_dd098 : decode_any W_dd098 = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd09c : bv 32 := 0x00010ab7.
Lemma F_dd09c : fetch_word Ubsan.M.loaded_segments (0xe19d4 : word) = Some W_dd09c.
Proof. vm_refl. Qed.
Lemma D_dd09c : decode_any W_dd09c = Some (Lui 21 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0a0 : bv 32 := 0x001d0097.
Lemma F_dd0a0 : fetch_word Ubsan.M.loaded_segments (0xe19d8 : word) = Some W_dd0a0.
Proof. vm_refl. Qed.
Lemma D_dd0a0 : decode_any W_dd0a0 = Some (Auipc 1 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0a4 : bv 32 := 0x278080e7.
Lemma F_dd0a4 : fetch_word Ubsan.M.loaded_segments (0xe19dc : word) = Some W_dd0a4.
Proof. vm_refl. Qed.
Lemma D_dd0a4 : decode_any W_dd0a4 = Some (Jalr 1 1 632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0a8 : bv 32 := 0x28050263.
Lemma F_dd0a8 : fetch_word Ubsan.M.loaded_segments (0xe19e0 : word) = Some W_dd0a8.
Proof. vm_refl. Qed.
Lemma D_dd0a8 : decode_any W_dd0a8 = Some (Branch BC_EQ 10 0 644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0ac : bv 32 := 0x00050b93.
Lemma F_dd0ac : fetch_word Ubsan.M.loaded_segments (0xe19e4 : word) = Some W_dd0ac.
Proof. vm_refl. Qed.
Lemma D_dd0ac : decode_any W_dd0ac = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0b0 : bv 32 := 0x00000993.
Lemma F_dd0b0 : fetch_word Ubsan.M.loaded_segments (0xe19e8 : word) = Some W_dd0b0.
Proof. vm_refl. Qed.
Lemma D_dd0b0 : decode_any W_dd0b0 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0b4 : bv 32 := 0x0023d517.
Lemma F_dd0b4 : fetch_word Ubsan.M.loaded_segments (0xe19ec : word) = Some W_dd0b4.
Proof. vm_refl. Qed.
Lemma D_dd0b4 : decode_any W_dd0b4 = Some (Auipc 10 573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0b8 : bv 32 := 0x51d50b13.
Lemma F_dd0b8 : fetch_word Ubsan.M.loaded_segments (0xe19f0 : word) = Some W_dd0b8.
Proof. vm_refl. Qed.
Lemma D_dd0b8 : decode_any W_dd0b8 = Some (OpImm ALU_ADD 22 10 1309, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0bc : bv 32 := 0x03501463.
Lemma F_dd0bc : fetch_word Ubsan.M.loaded_segments (0xe19f4 : word) = Some W_dd0bc.
Proof. vm_refl. Qed.
Lemma D_dd0bc : decode_any W_dd0bc = Some (Branch BC_NE 0 21 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0c0 : bv 32 := 0x02c0006f.
Lemma F_dd0c0 : fetch_word Ubsan.M.loaded_segments (0xe19f8 : word) = Some W_dd0c0.
Proof. vm_refl. Qed.
Lemma D_dd0c0 : decode_any W_dd0c0 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0c4 : bv 32 := 0x01348533.
Lemma F_dd0c4 : fetch_word Ubsan.M.loaded_segments (0xe19fc : word) = Some W_dd0c4.
Proof. vm_refl. Qed.
Lemma D_dd0c4 : decode_any W_dd0c4 = Some (Op ALU_ADD 10 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0c8 : bv 32 := 0x000b0593.
Lemma F_dd0c8 : fetch_word Ubsan.M.loaded_segments (0xe1a00 : word) = Some W_dd0c8.
Proof. vm_refl. Qed.
Lemma D_dd0c8 : decode_any W_dd0c8 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0cc : bv 32 := 0x000b8613.
Lemma F_dd0cc : fetch_word Ubsan.M.loaded_segments (0xe1a04 : word) = Some W_dd0cc.
Proof. vm_refl. Qed.
Lemma D_dd0cc : decode_any W_dd0cc = Some (OpImm ALU_ADD 12 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0d0 : bv 32 := 0x001da097.
Lemma F_dd0d0 : fetch_word Ubsan.M.loaded_segments (0xe1a08 : word) = Some W_dd0d0.
Proof. vm_refl. Qed.
Lemma D_dd0d0 : decode_any W_dd0d0 = Some (Auipc 1 474, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0d4 : bv 32 := 0x61c080e7.
Lemma F_dd0d4 : fetch_word Ubsan.M.loaded_segments (0xe1a0c : word) = Some W_dd0d4.
Proof. vm_refl. Qed.
Lemma D_dd0d4 : decode_any W_dd0d4 = Some (Jalr 1 1 1564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0d8 : bv 32 := 0x013b89b3.
Lemma F_dd0d8 : fetch_word Ubsan.M.loaded_segments (0xe1a10 : word) = Some W_dd0d8.
Proof. vm_refl. Qed.
Lemma D_dd0d8 : decode_any W_dd0d8 = Some (Op ALU_ADD 19 23 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0dc : bv 32 := 0x00048b93.
Lemma F_dd0dc : fetch_word Ubsan.M.loaded_segments (0xe1a14 : word) = Some W_dd0dc.
Proof. vm_refl. Qed.
Lemma D_dd0dc : decode_any W_dd0dc = Some (OpImm ALU_ADD 23 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0e0 : bv 32 := 0x01598663.
Lemma F_dd0e0 : fetch_word Ubsan.M.loaded_segments (0xe1a18 : word) = Some W_dd0e0.
Proof. vm_refl. Qed.
Lemma D_dd0e0 : decode_any W_dd0e0 = Some (Branch BC_EQ 19 21 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0e4 : bv 32 := 0x000b8493.
Lemma F_dd0e4 : fetch_word Ubsan.M.loaded_segments (0xe1a1c : word) = Some W_dd0e4.
Proof. vm_refl. Qed.
Lemma D_dd0e4 : decode_any W_dd0e4 = Some (OpImm ALU_ADD 9 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0e8 : bv 32 := 0x0480006f.
Lemma F_dd0e8 : fetch_word Ubsan.M.loaded_segments (0xe1a20 : word) = Some W_dd0e8.
Proof. vm_refl. Qed.
Lemma D_dd0e8 : decode_any W_dd0e8 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0ec : bv 32 := 0x01a9d513.
Lemma F_dd0ec : fetch_word Ubsan.M.loaded_segments (0xe1a24 : word) = Some W_dd0ec.
Proof. vm_refl. Qed.
Lemma D_dd0ec : decode_any W_dd0ec = Some (ShiftImm ALU_SRL 10 19 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0f0 : bv 32 := 0x1c051863.
Lemma F_dd0f0 : fetch_word Ubsan.M.loaded_segments (0xe1a28 : word) = Some W_dd0f0.
Proof. vm_refl. Qed.
Lemma D_dd0f0 : decode_any W_dd0f0 = Some (Branch BC_NE 10 0 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0f4 : bv 32 := 0x00199a93.
Lemma F_dd0f4 : fetch_word Ubsan.M.loaded_segments (0xe1a2c : word) = Some W_dd0f4.
Proof. vm_refl. Qed.
Lemma D_dd0f4 : decode_any W_dd0f4 = Some (ShiftImm ALU_SLL 21 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0f8 : bv 32 := 0x000a8513.
Lemma F_dd0f8 : fetch_word Ubsan.M.loaded_segments (0xe1a30 : word) = Some W_dd0f8.
Proof. vm_refl. Qed.
Lemma D_dd0f8 : decode_any W_dd0f8 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd0fc : bv 32 := 0x001d0097.
Lemma F_dd0fc : fetch_word Ubsan.M.loaded_segments (0xe1a34 : word) = Some W_dd0fc.
Proof. vm_refl. Qed.
Lemma D_dd0fc : decode_any W_dd0fc = Some (Auipc 1 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd100 : bv 32 := 0x21c080e7.
Lemma F_dd100 : fetch_word Ubsan.M.loaded_segments (0xe1a38 : word) = Some W_dd100.
Proof. vm_refl. Qed.
Lemma D_dd100 : decode_any W_dd100 = Some (Jalr 1 1 540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd104 : bv 32 := 0x1e050063.
Lemma F_dd104 : fetch_word Ubsan.M.loaded_segments (0xe1a3c : word) = Some W_dd104.
Proof. vm_refl. Qed.
Lemma D_dd104 : decode_any W_dd104 = Some (Branch BC_EQ 10 0 480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd108 : bv 32 := 0x00050493.
Lemma F_dd108 : fetch_word Ubsan.M.loaded_segments (0xe1a40 : word) = Some W_dd108.
Proof. vm_refl. Qed.
Lemma D_dd108 : decode_any W_dd108 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd10c : bv 32 := 0x00098c63.
Lemma F_dd10c : fetch_word Ubsan.M.loaded_segments (0xe1a44 : word) = Some W_dd10c.
Proof. vm_refl. Qed.
Lemma D_dd10c : decode_any W_dd10c = Some (Branch BC_EQ 19 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd110 : bv 32 := 0x00048513.
Lemma F_dd110 : fetch_word Ubsan.M.loaded_segments (0xe1a48 : word) = Some W_dd110.
Proof. vm_refl. Qed.
Lemma D_dd110 : decode_any W_dd110 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd114 : bv 32 := 0x000b8593.
Lemma F_dd114 : fetch_word Ubsan.M.loaded_segments (0xe1a4c : word) = Some W_dd114.
Proof. vm_refl. Qed.
Lemma D_dd114 : decode_any W_dd114 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd118 : bv 32 := 0x00098613.
Lemma F_dd118 : fetch_word Ubsan.M.loaded_segments (0xe1a50 : word) = Some W_dd118.
Proof. vm_refl. Qed.
Lemma D_dd118 : decode_any W_dd118 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd11c : bv 32 := 0x001da097.
Lemma F_dd11c : fetch_word Ubsan.M.loaded_segments (0xe1a54 : word) = Some W_dd11c.
Proof. vm_refl. Qed.
Lemma D_dd11c : decode_any W_dd11c = Some (Auipc 1 474, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd120 : bv 32 := 0x5d0080e7.
Lemma F_dd120 : fetch_word Ubsan.M.loaded_segments (0xe1a58 : word) = Some W_dd120.
Proof. vm_refl. Qed.
Lemma D_dd120 : decode_any W_dd120 = Some (Jalr 1 1 1488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd124 : bv 32 := 0x000b8513.
Lemma F_dd124 : fetch_word Ubsan.M.loaded_segments (0xe1a5c : word) = Some W_dd124.
Proof. vm_refl. Qed.
Lemma D_dd124 : decode_any W_dd124 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd128 : bv 32 := 0x001d0097.
Lemma F_dd128 : fetch_word Ubsan.M.loaded_segments (0xe1a60 : word) = Some W_dd128.
Proof. vm_refl. Qed.
Lemma D_dd128 : decode_any W_dd128 = Some (Auipc 1 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd12c : bv 32 := 0x0b0080e7.
Lemma F_dd12c : fetch_word Ubsan.M.loaded_segments (0xe1a64 : word) = Some W_dd12c.
Proof. vm_refl. Qed.
Lemma D_dd12c : decode_any W_dd12c = Some (Jalr 1 1 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd130 : bv 32 := 0x413a8633.
Lemma F_dd130 : fetch_word Ubsan.M.loaded_segments (0xe1a68 : word) = Some W_dd130.
Proof. vm_refl. Qed.
Lemma D_dd130 : decode_any W_dd130 = Some (Op ALU_SUB 12 21 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd134 : bv 32 := 0x00010537.
Lemma F_dd134 : fetch_word Ubsan.M.loaded_segments (0xe1a6c : word) = Some W_dd134.
Proof. vm_refl. Qed.
Lemma D_dd134 : decode_any W_dd134 = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd138 : bv 32 := 0x00a66463.
Lemma F_dd138 : fetch_word Ubsan.M.loaded_segments (0xe1a70 : word) = Some W_dd138.
Proof. vm_refl. Qed.
Lemma D_dd138 : decode_any W_dd138 = Some (Branch BC_LTU 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd13c : bv 32 := 0x00010637.
Lemma F_dd13c : fetch_word Ubsan.M.loaded_segments (0xe1a74 : word) = Some W_dd13c.
Proof. vm_refl. Qed.
Lemma D_dd13c : decode_any W_dd13c = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd140 : bv 32 := 0x000a0513.
Lemma F_dd140 : fetch_word Ubsan.M.loaded_segments (0xe1a78 : word) = Some W_dd140.
Proof. vm_refl. Qed.
Lemma D_dd140 : decode_any W_dd140 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd144 : bv 32 := 0x000b0593.
Lemma F_dd144 : fetch_word Ubsan.M.loaded_segments (0xe1a7c : word) = Some W_dd144.
Proof. vm_refl. Qed.
Lemma D_dd144 : decode_any W_dd144 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd148 : bv 32 := 0x001df097.
Lemma F_dd148 : fetch_word Ubsan.M.loaded_segments (0xe1a80 : word) = Some W_dd148.
Proof. vm_refl. Qed.
Lemma D_dd148 : decode_any W_dd148 = Some (Auipc 1 479, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd14c : bv 32 := 0xc74080e7.
Lemma F_dd14c : fetch_word Ubsan.M.loaded_segments (0xe1a84 : word) = Some W_dd14c.
Proof. vm_refl. Qed.
Lemma D_dd14c : decode_any W_dd14c = Some (Jalr 1 1 3188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd150 : bv 32 := 0x14054a63.
Lemma F_dd150 : fetch_word Ubsan.M.loaded_segments (0xe1a88 : word) = Some W_dd150.
Proof. vm_refl. Qed.
Lemma D_dd150 : decode_any W_dd150 = Some (Branch BC_LT 10 0 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd154 : bv 32 := 0x00050b93.
Lemma F_dd154 : fetch_word Ubsan.M.loaded_segments (0xe1a8c : word) = Some W_dd154.
Proof. vm_refl. Qed.
Lemma D_dd154 : decode_any W_dd154 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd158 : bv 32 := 0xf60516e3.
Lemma F_dd158 : fetch_word Ubsan.M.loaded_segments (0xe1a90 : word) = Some W_dd158.
Proof. vm_refl. Qed.
Lemma D_dd158 : decode_any W_dd158 = Some (Branch BC_NE 10 0 8044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd15c : bv 32 := 0x000a0513.
Lemma F_dd15c : fetch_word Ubsan.M.loaded_segments (0xe1a94 : word) = Some W_dd15c.
Proof. vm_refl. Qed.
Lemma D_dd15c : decode_any W_dd15c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd160 : bv 32 := 0x001df097.
Lemma F_dd160 : fetch_word Ubsan.M.loaded_segments (0xe1a98 : word) = Some W_dd160.
Proof. vm_refl. Qed.
Lemma D_dd160 : decode_any W_dd160 = Some (Auipc 1 479, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd164 : bv 32 := 0xbbc080e7.
Lemma F_dd164 : fetch_word Ubsan.M.loaded_segments (0xe1a9c : word) = Some W_dd164.
Proof. vm_refl. Qed.
Lemma D_dd164 : decode_any W_dd164 = Some (Jalr 1 1 3004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd168 : bv 32 := 0x00500513.
Lemma F_dd168 : fetch_word Ubsan.M.loaded_segments (0xe1aa0 : word) = Some W_dd168.
Proof. vm_refl. Qed.
Lemma D_dd168 : decode_any W_dd168 = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd16c : bv 32 := 0x0b357e63.
Lemma F_dd16c : fetch_word Ubsan.M.loaded_segments (0xe1aa4 : word) = Some W_dd16c.
Proof. vm_refl. Qed.
Lemma D_dd16c : decode_any W_dd16c = Some (Branch BC_GEU 10 19 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd170 : bv 32 := 0x00148a83.
Lemma F_dd170 : fetch_word Ubsan.M.loaded_segments (0xe1aa8 : word) = Some W_dd170.
Proof. vm_refl. Qed.
Lemma D_dd170 : decode_any W_dd170 = Some (Load SZ1 true 21 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd174 : bv 32 := 0x0004c503.
Lemma F_dd174 : fetch_word Ubsan.M.loaded_segments (0xe1aac : word) = Some W_dd174.
Proof. vm_refl. Qed.
Lemma D_dd174 : decode_any W_dd174 = Some (Load SZ1 false 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd178 : bv 32 := 0x039a9593.
Lemma F_dd178 : fetch_word Ubsan.M.loaded_segments (0xe1ab0 : word) = Some W_dd178.
Proof. vm_refl. Qed.
Lemma D_dd178 : decode_any W_dd178 = Some (ShiftImm ALU_SLL 11 21 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd17c : bv 32 := 0x0315d593.
Lemma F_dd17c : fetch_word Ubsan.M.loaded_segments (0xe1ab4 : word) = Some W_dd17c.
Proof. vm_refl. Qed.
Lemma D_dd17c : decode_any W_dd17c = Some (ShiftImm ALU_SRL 11 11 49, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd180 : bv 32 := 0x00a5e933.
Lemma F_dd180 : fetch_word Ubsan.M.loaded_segments (0xe1ab8 : word) = Some W_dd180.
Proof. vm_refl. Qed.
Lemma D_dd180 : decode_any W_dd180 = Some (Op ALU_OR 18 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd184 : bv 32 := 0x00690513.
Lemma F_dd184 : fetch_word Ubsan.M.loaded_segments (0xe1abc : word) = Some W_dd184.
Proof. vm_refl. Qed.
Lemma D_dd184 : decode_any W_dd184 = Some (OpImm ALU_ADD 10 18 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd188 : bv 32 := 0x0aa9ee63.
Lemma F_dd188 : fetch_word Ubsan.M.loaded_segments (0xe1ac0 : word) = Some W_dd188.
Proof. vm_refl. Qed.
Lemma D_dd188 : decode_any W_dd188 = Some (Branch BC_LTU 19 10 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd18c : bv 32 := 0x00248413.
Lemma F_dd18c : fetch_word Ubsan.M.loaded_segments (0xe1ac4 : word) = Some W_dd18c.
Proof. vm_refl. Qed.
Lemma D_dd18c : decode_any W_dd18c = Some (OpImm ALU_ADD 8 9 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd190 : bv 32 := 0x01240533.
Lemma F_dd190 : fetch_word Ubsan.M.loaded_segments (0xe1ac8 : word) = Some W_dd190.
Proof. vm_refl. Qed.
Lemma D_dd190 : decode_any W_dd190 = Some (Op ALU_ADD 10 8 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd194 : bv 32 := 0x00154583.
Lemma F_dd194 : fetch_word Ubsan.M.loaded_segments (0xe1acc : word) = Some W_dd194.
Proof. vm_refl. Qed.
Lemma D_dd194 : decode_any W_dd194 = Some (Load SZ1 false 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd198 : bv 32 := 0x00054603.
Lemma F_dd198 : fetch_word Ubsan.M.loaded_segments (0xe1ad0 : word) = Some W_dd198.
Proof. vm_refl. Qed.
Lemma D_dd198 : decode_any W_dd198 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd19c : bv 32 := 0x00254683.
Lemma F_dd19c : fetch_word Ubsan.M.loaded_segments (0xe1ad4 : word) = Some W_dd19c.
Proof. vm_refl. Qed.
Lemma D_dd19c : decode_any W_dd19c = Some (Load SZ1 false 13 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1a0 : bv 32 := 0x00354703.
Lemma F_dd1a0 : fetch_word Ubsan.M.loaded_segments (0xe1ad8 : word) = Some W_dd1a0.
Proof. vm_refl. Qed.
Lemma D_dd1a0 : decode_any W_dd1a0 = Some (Load SZ1 false 14 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1a4 : bv 32 := 0x00859593.
Lemma F_dd1a4 : fetch_word Ubsan.M.loaded_segments (0xe1adc : word) = Some W_dd1a4.
Proof. vm_refl. Qed.
Lemma D_dd1a4 : decode_any W_dd1a4 = Some (ShiftImm ALU_SLL 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1a8 : bv 32 := 0x00c5e5b3.
Lemma F_dd1a8 : fetch_word Ubsan.M.loaded_segments (0xe1ae0 : word) = Some W_dd1a8.
Proof. vm_refl. Qed.
Lemma D_dd1a8 : decode_any W_dd1a8 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1ac : bv 32 := 0x41298a33.
Lemma F_dd1ac : fetch_word Ubsan.M.loaded_segments (0xe1ae4 : word) = Some W_dd1ac.
Proof. vm_refl. Qed.
Lemma D_dd1ac : decode_any W_dd1ac = Some (Op ALU_SUB 20 19 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1b0 : bv 32 := 0x00450993.
Lemma F_dd1b0 : fetch_word Ubsan.M.loaded_segments (0xe1ae8 : word) = Some W_dd1b0.
Proof. vm_refl. Qed.
Lemma D_dd1b0 : decode_any W_dd1b0 = Some (OpImm ALU_ADD 19 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1b4 : bv 32 := 0x01069693.
Lemma F_dd1b4 : fetch_word Ubsan.M.loaded_segments (0xe1aec : word) = Some W_dd1b4.
Proof. vm_refl. Qed.
Lemma D_dd1b4 : decode_any W_dd1b4 = Some (ShiftImm ALU_SLL 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1b8 : bv 32 := 0x0187151b.
Lemma F_dd1b8 : fetch_word Ubsan.M.loaded_segments (0xe1af0 : word) = Some W_dd1b8.
Proof. vm_refl. Qed.
Lemma D_dd1b8 : decode_any W_dd1b8 = Some (ShiftImm32 ALU_SLL 10 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1bc : bv 32 := 0x00a6e533.
Lemma F_dd1bc : fetch_word Ubsan.M.loaded_segments (0xe1af4 : word) = Some W_dd1bc.
Proof. vm_refl. Qed.
Lemma D_dd1bc : decode_any W_dd1bc = Some (Op ALU_OR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1c0 : bv 32 := 0x00a5e533.
Lemma F_dd1c0 : fetch_word Ubsan.M.loaded_segments (0xe1af8 : word) = Some W_dd1c0.
Proof. vm_refl. Qed.
Lemma D_dd1c0 : decode_any W_dd1c0 = Some (Op ALU_OR 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1c4 : bv 32 := 0xffaa0a13.
Lemma F_dd1c4 : fetch_word Ubsan.M.loaded_segments (0xe1afc : word) = Some W_dd1c4.
Proof. vm_refl. Qed.
Lemma D_dd1c4 : decode_any W_dd1c4 = Some (OpImm ALU_ADD 20 20 4090, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1c8 : bv 32 := 0x180000ef.
Lemma F_dd1c8 : fetch_word Ubsan.M.loaded_segments (0xe1b00 : word) = Some W_dd1c8.
Proof. vm_refl. Qed.
Lemma D_dd1c8 : decode_any W_dd1c8 = Some (Jal 1 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1cc : bv 32 := 0x00040513.
Lemma F_dd1cc : fetch_word Ubsan.M.loaded_segments (0xe1b04 : word) = Some W_dd1cc.
Proof. vm_refl. Qed.
Lemma D_dd1cc : decode_any W_dd1cc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1d0 : bv 32 := 0x00090593.
Lemma F_dd1d0 : fetch_word Ubsan.M.loaded_segments (0xe1b08 : word) = Some W_dd1d0.
Proof. vm_refl. Qed.
Lemma D_dd1d0 : decode_any W_dd1d0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1d4 : bv 32 := 0x00098613.
Lemma F_dd1d4 : fetch_word Ubsan.M.loaded_segments (0xe1b0c : word) = Some W_dd1d4.
Proof. vm_refl. Qed.
Lemma D_dd1d4 : decode_any W_dd1d4 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1d8 : bv 32 := 0x000a0693.
Lemma F_dd1d8 : fetch_word Ubsan.M.loaded_segments (0xe1b10 : word) = Some W_dd1d8.
Proof. vm_refl. Qed.
Lemma D_dd1d8 : decode_any W_dd1d8 = Some (OpImm ALU_ADD 13 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1dc : bv 32 := 0x178000ef.
Lemma F_dd1dc : fetch_word Ubsan.M.loaded_segments (0xe1b14 : word) = Some W_dd1dc.
Proof. vm_refl. Qed.
Lemma D_dd1dc : decode_any W_dd1dc = Some (Jal 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1e0 : bv 32 := 0x000ac663.
Lemma F_dd1e0 : fetch_word Ubsan.M.loaded_segments (0xe1b18 : word) = Some W_dd1e0.
Proof. vm_refl. Qed.
Lemma D_dd1e0 : decode_any W_dd1e0 = Some (Branch BC_LT 21 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1e4 : bv 32 := 0x00050413.
Lemma F_dd1e4 : fetch_word Ubsan.M.loaded_segments (0xe1b1c : word) = Some W_dd1e4.
Proof. vm_refl. Qed.
Lemma D_dd1e4 : decode_any W_dd1e4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1e8 : bv 32 := 0x0800006f.
Lemma F_dd1e8 : fetch_word Ubsan.M.loaded_segments (0xe1b20 : word) = Some W_dd1e8.
Proof. vm_refl. Qed.
Lemma D_dd1e8 : decode_any W_dd1e8 = Some (Jal 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1ec : bv 32 := 0x160000ef.
Lemma F_dd1ec : fetch_word Ubsan.M.loaded_segments (0xe1b24 : word) = Some W_dd1ec.
Proof. vm_refl. Qed.
Lemma D_dd1ec : decode_any W_dd1ec = Some (Jal 1 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1f0 : bv 32 := 0x0fb00593.
Lemma F_dd1f0 : fetch_word Ubsan.M.loaded_segments (0xe1b28 : word) = Some W_dd1f0.
Proof. vm_refl. Qed.
Lemma D_dd1f0 : decode_any W_dd1f0 = Some (OpImm ALU_ADD 11 0 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1f4 : bv 32 := 0x00050413.
Lemma F_dd1f4 : fetch_word Ubsan.M.loaded_segments (0xe1b2c : word) = Some W_dd1f4.
Proof. vm_refl. Qed.
Lemma D_dd1f4 : decode_any W_dd1f4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1f8 : bv 32 := 0x06b56863.
Lemma F_dd1f8 : fetch_word Ubsan.M.loaded_segments (0xe1b30 : word) = Some W_dd1f8.
Proof. vm_refl. Qed.
Lemma D_dd1f8 : decode_any W_dd1f8 = Some (Branch BC_LTU 10 11 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd1fc : bv 32 := 0x0fb00413.
Lemma F_dd1fc : fetch_word Ubsan.M.loaded_segments (0xe1b34 : word) = Some W_dd1fc.
Proof. vm_refl. Qed.
Lemma D_dd1fc : decode_any W_dd1fc = Some (OpImm ALU_ADD 8 0 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd200 : bv 32 := 0x0680006f.
Lemma F_dd200 : fetch_word Ubsan.M.loaded_segments (0xe1b38 : word) = Some W_dd200.
Proof. vm_refl. Qed.
Lemma D_dd200 : decode_any W_dd200 = Some (Jal 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd204 : bv 32 := 0x0023b517.
Lemma F_dd204 : fetch_word Ubsan.M.loaded_segments (0xe1b3c : word) = Some W_dd204.
Proof. vm_refl. Qed.
Lemma D_dd204 : decode_any W_dd204 = Some (Auipc 10 571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd208 : bv 32 := 0x4b453503.
Lemma F_dd208 : fetch_word Ubsan.M.loaded_segments (0xe1b40 : word) = Some W_dd208.
Proof. vm_refl. Qed.
Lemma D_dd208 : decode_any W_dd208 = Some (Load SZ8 true 10 10 1204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd20c : bv 32 := 0x00053503.
Lemma F_dd20c : fetch_word Ubsan.M.loaded_segments (0xe1b44 : word) = Some W_dd20c.
Proof. vm_refl. Qed.
Lemma D_dd20c : decode_any W_dd20c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd210 : bv 32 := 0x0005b603.
Lemma F_dd210 : fetch_word Ubsan.M.loaded_segments (0xe1b48 : word) = Some W_dd210.
Proof. vm_refl. Qed.
Lemma D_dd210 : decode_any W_dd210 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd214 : bv 32 := 0xfff3a597.
Lemma F_dd214 : fetch_word Ubsan.M.loaded_segments (0xe1b4c : word) = Some W_dd214.
Proof. vm_refl. Qed.
Lemma D_dd214 : decode_any W_dd214 = Some (Auipc 11 1048378, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd218 : bv 32 := 0x14558593.
Lemma F_dd218 : fetch_word Ubsan.M.loaded_segments (0xe1b50 : word) = Some W_dd218.
Proof. vm_refl. Qed.
Lemma D_dd218 : decode_any W_dd218 = Some (OpImm ALU_ADD 11 11 325, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd21c : bv 32 := 0x001d4097.
Lemma F_dd21c : fetch_word Ubsan.M.loaded_segments (0xe1b54 : word) = Some W_dd21c.
Proof. vm_refl. Qed.
Lemma D_dd21c : decode_any W_dd21c = Some (Auipc 1 468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd220 : bv 32 := 0xbe8080e7.
Lemma F_dd220 : fetch_word Ubsan.M.loaded_segments (0xe1b58 : word) = Some W_dd220.
Proof. vm_refl. Qed.
Lemma D_dd220 : decode_any W_dd220 = Some (Jalr 1 1 3048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd224 : bv 32 := 0x0500006f.
Lemma F_dd224 : fetch_word Ubsan.M.loaded_segments (0xe1b5c : word) = Some W_dd224.
Proof. vm_refl. Qed.
Lemma D_dd224 : decode_any W_dd224 = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd228 : bv 32 := 0x0023b517.
Lemma F_dd228 : fetch_word Ubsan.M.loaded_segments (0xe1b60 : word) = Some W_dd228.
Proof. vm_refl. Qed.
Lemma D_dd228 : decode_any W_dd228 = Some (Auipc 10 571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd22c : bv 32 := 0x49053503.
Lemma F_dd22c : fetch_word Ubsan.M.loaded_segments (0xe1b64 : word) = Some W_dd22c.
Proof. vm_refl. Qed.
Lemma D_dd22c : decode_any W_dd22c = Some (Load SZ8 true 10 10 1168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd230 : bv 32 := 0x00053683.
Lemma F_dd230 : fetch_word Ubsan.M.loaded_segments (0xe1b68 : word) = Some W_dd230.
Proof. vm_refl. Qed.
Lemma D_dd230 : decode_any W_dd230 = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd234 : bv 32 := 0xfff55517.
Lemma F_dd234 : fetch_word Ubsan.M.loaded_segments (0xe1b6c : word) = Some W_dd234.
Proof. vm_refl. Qed.
Lemma D_dd234 : decode_any W_dd234 = Some (Auipc 10 1048405, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd238 : bv 32 := 0x01f00593.
Lemma F_dd238 : fetch_word Ubsan.M.loaded_segments (0xe1b70 : word) = Some W_dd238.
Proof. vm_refl. Qed.
Lemma D_dd238 : decode_any W_dd238 = Some (OpImm ALU_ADD 11 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd23c : bv 32 := 0x8f350513.
Lemma F_dd23c : fetch_word Ubsan.M.loaded_segments (0xe1b74 : word) = Some W_dd23c.
Proof. vm_refl. Qed.
Lemma D_dd23c : decode_any W_dd23c = Some (OpImm ALU_ADD 10 10 2291, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd240 : bv 32 := 0x01c0006f.
Lemma F_dd240 : fetch_word Ubsan.M.loaded_segments (0xe1b78 : word) = Some W_dd240.
Proof. vm_refl. Qed.
Lemma D_dd240 : decode_any W_dd240 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd244 : bv 32 := 0x0023b517.
Lemma F_dd244 : fetch_word Ubsan.M.loaded_segments (0xe1b7c : word) = Some W_dd244.
Proof. vm_refl. Qed.
Lemma D_dd244 : decode_any W_dd244 = Some (Auipc 10 571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd248 : bv 32 := 0x47453503.
Lemma F_dd248 : fetch_word Ubsan.M.loaded_segments (0xe1b80 : word) = Some W_dd248.
Proof. vm_refl. Qed.
Lemma D_dd248 : decode_any W_dd248 = Some (Load SZ8 true 10 10 1140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd24c : bv 32 := 0x00053683.
Lemma F_dd24c : fetch_word Ubsan.M.loaded_segments (0xe1b84 : word) = Some W_dd24c.
Proof. vm_refl. Qed.
Lemma D_dd24c : decode_any W_dd24c = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd250 : bv 32 := 0xfff3a517.
Lemma F_dd250 : fetch_word Ubsan.M.loaded_segments (0xe1b88 : word) = Some W_dd250.
Proof. vm_refl. Qed.
Lemma D_dd250 : decode_any W_dd250 = Some (Auipc 10 1048378, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd254 : bv 32 := 0x01f00593.
Lemma F_dd254 : fetch_word Ubsan.M.loaded_segments (0xe1b8c : word) = Some W_dd254.
Proof. vm_refl. Qed.
Lemma D_dd254 : decode_any W_dd254 = Some (OpImm ALU_ADD 11 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd258 : bv 32 := 0x11a50513.
Lemma F_dd258 : fetch_word Ubsan.M.loaded_segments (0xe1b90 : word) = Some W_dd258.
Proof. vm_refl. Qed.
Lemma D_dd258 : decode_any W_dd258 = Some (OpImm ALU_ADD 10 10 282, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd25c : bv 32 := 0x00100613.
Lemma F_dd25c : fetch_word Ubsan.M.loaded_segments (0xe1b94 : word) = Some W_dd25c.
Proof. vm_refl. Qed.
Lemma D_dd25c : decode_any W_dd25c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd260 : bv 32 := 0x001d4097.
Lemma F_dd260 : fetch_word Ubsan.M.loaded_segments (0xe1b98 : word) = Some W_dd260.
Proof. vm_refl. Qed.
Lemma D_dd260 : decode_any W_dd260 = Some (Auipc 1 468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd264 : bv 32 := 0x330080e7.
Lemma F_dd264 : fetch_word Ubsan.M.loaded_segments (0xe1b9c : word) = Some W_dd264.
Proof. vm_refl. Qed.
Lemma D_dd264 : decode_any W_dd264 = Some (Jalr 1 1 816, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd268 : bv 32 := 0x00048513.
Lemma F_dd268 : fetch_word Ubsan.M.loaded_segments (0xe1ba0 : word) = Some W_dd268.
Proof. vm_refl. Qed.
Lemma D_dd268 : decode_any W_dd268 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd26c : bv 32 := 0x001d0097.
Lemma F_dd26c : fetch_word Ubsan.M.loaded_segments (0xe1ba4 : word) = Some W_dd26c.
Proof. vm_refl. Qed.
Lemma D_dd26c : decode_any W_dd26c = Some (Auipc 1 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd270 : bv 32 := 0xf6c080e7.
Lemma F_dd270 : fetch_word Ubsan.M.loaded_segments (0xe1ba8 : word) = Some W_dd270.
Proof. vm_refl. Qed.
Lemma D_dd270 : decode_any W_dd270 = Some (Jalr 1 1 3948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd274 : bv 32 := 0x00040513.
Lemma F_dd274 : fetch_word Ubsan.M.loaded_segments (0xe1bac : word) = Some W_dd274.
Proof. vm_refl. Qed.
Lemma D_dd274 : decode_any W_dd274 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd278 : bv 32 := 0x04813083.
Lemma F_dd278 : fetch_word Ubsan.M.loaded_segments (0xe1bb0 : word) = Some W_dd278.
Proof. vm_refl. Qed.
Lemma D_dd278 : decode_any W_dd278 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd27c : bv 32 := 0x04013403.
Lemma F_dd27c : fetch_word Ubsan.M.loaded_segments (0xe1bb4 : word) = Some W_dd27c.
Proof. vm_refl. Qed.
Lemma D_dd27c : decode_any W_dd27c = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd280 : bv 32 := 0x03813483.
Lemma F_dd280 : fetch_word Ubsan.M.loaded_segments (0xe1bb8 : word) = Some W_dd280.
Proof. vm_refl. Qed.
Lemma D_dd280 : decode_any W_dd280 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd284 : bv 32 := 0x03013903.
Lemma F_dd284 : fetch_word Ubsan.M.loaded_segments (0xe1bbc : word) = Some W_dd284.
Proof. vm_refl. Qed.
Lemma D_dd284 : decode_any W_dd284 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd288 : bv 32 := 0x02813983.
Lemma F_dd288 : fetch_word Ubsan.M.loaded_segments (0xe1bc0 : word) = Some W_dd288.
Proof. vm_refl. Qed.
Lemma D_dd288 : decode_any W_dd288 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd28c : bv 32 := 0x02013a03.
Lemma F_dd28c : fetch_word Ubsan.M.loaded_segments (0xe1bc4 : word) = Some W_dd28c.
Proof. vm_refl. Qed.
Lemma D_dd28c : decode_any W_dd28c = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd290 : bv 32 := 0x01813a83.
Lemma F_dd290 : fetch_word Ubsan.M.loaded_segments (0xe1bc8 : word) = Some W_dd290.
Proof. vm_refl. Qed.
Lemma D_dd290 : decode_any W_dd290 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd294 : bv 32 := 0x01013b03.
Lemma F_dd294 : fetch_word Ubsan.M.loaded_segments (0xe1bcc : word) = Some W_dd294.
Proof. vm_refl. Qed.
Lemma D_dd294 : decode_any W_dd294 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd298 : bv 32 := 0x00813b83.
Lemma F_dd298 : fetch_word Ubsan.M.loaded_segments (0xe1bd0 : word) = Some W_dd298.
Proof. vm_refl. Qed.
Lemma D_dd298 : decode_any W_dd298 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd29c : bv 32 := 0x05010113.
Lemma F_dd29c : fetch_word Ubsan.M.loaded_segments (0xe1bd4 : word) = Some W_dd29c.
Proof. vm_refl. Qed.
Lemma D_dd29c : decode_any W_dd29c = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2a0 : bv 32 := 0x00008067.
Lemma F_dd2a0 : fetch_word Ubsan.M.loaded_segments (0xe1bd8 : word) = Some W_dd2a0.
Proof. vm_refl. Qed.
Lemma D_dd2a0 : decode_any W_dd2a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2a4 : bv 32 := 0x0023b517.
Lemma F_dd2a4 : fetch_word Ubsan.M.loaded_segments (0xe1bdc : word) = Some W_dd2a4.
Proof. vm_refl. Qed.
Lemma D_dd2a4 : decode_any W_dd2a4 = Some (Auipc 10 571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2a8 : bv 32 := 0x41453503.
Lemma F_dd2a8 : fetch_word Ubsan.M.loaded_segments (0xe1be0 : word) = Some W_dd2a8.
Proof. vm_refl. Qed.
Lemma D_dd2a8 : decode_any W_dd2a8 = Some (Load SZ8 true 10 10 1044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2ac : bv 32 := 0x00053503.
Lemma F_dd2ac : fetch_word Ubsan.M.loaded_segments (0xe1be4 : word) = Some W_dd2ac.
Proof. vm_refl. Qed.
Lemma D_dd2ac : decode_any W_dd2ac = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2b0 : bv 32 := 0xfff4f597.
Lemma F_dd2b0 : fetch_word Ubsan.M.loaded_segments (0xe1be8 : word) = Some W_dd2b0.
Proof. vm_refl. Qed.
Lemma D_dd2b0 : decode_any W_dd2b0 = Some (Auipc 11 1048399, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2b4 : bv 32 := 0x26b58593.
Lemma F_dd2b4 : fetch_word Ubsan.M.loaded_segments (0xe1bec : word) = Some W_dd2b4.
Proof. vm_refl. Qed.
Lemma D_dd2b4 : decode_any W_dd2b4 = Some (OpImm ALU_ADD 11 11 619, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2b8 : bv 32 := 0x00090613.
Lemma F_dd2b8 : fetch_word Ubsan.M.loaded_segments (0xe1bf0 : word) = Some W_dd2b8.
Proof. vm_refl. Qed.
Lemma D_dd2b8 : decode_any W_dd2b8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2bc : bv 32 := 0x01c0006f.
Lemma F_dd2bc : fetch_word Ubsan.M.loaded_segments (0xe1bf4 : word) = Some W_dd2bc.
Proof. vm_refl. Qed.
Lemma D_dd2bc : decode_any W_dd2bc = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2c0 : bv 32 := 0x0023b517.
Lemma F_dd2c0 : fetch_word Ubsan.M.loaded_segments (0xe1bf8 : word) = Some W_dd2c0.
Proof. vm_refl. Qed.
Lemma D_dd2c0 : decode_any W_dd2c0 = Some (Auipc 10 571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2c4 : bv 32 := 0x3f853503.
Lemma F_dd2c4 : fetch_word Ubsan.M.loaded_segments (0xe1bfc : word) = Some W_dd2c4.
Proof. vm_refl. Qed.
Lemma D_dd2c4 : decode_any W_dd2c4 = Some (Load SZ8 true 10 10 1016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2c8 : bv 32 := 0x00053503.
Lemma F_dd2c8 : fetch_word Ubsan.M.loaded_segments (0xe1c00 : word) = Some W_dd2c8.
Proof. vm_refl. Qed.
Lemma D_dd2c8 : decode_any W_dd2c8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2cc : bv 32 := 0xfff45597.
Lemma F_dd2cc : fetch_word Ubsan.M.loaded_segments (0xe1c04 : word) = Some W_dd2cc.
Proof. vm_refl. Qed.
Lemma D_dd2cc : decode_any W_dd2cc = Some (Auipc 11 1048389, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2d0 : bv 32 := 0x89658593.
Lemma F_dd2d0 : fetch_word Ubsan.M.loaded_segments (0xe1c08 : word) = Some W_dd2d0.
Proof. vm_refl. Qed.
Lemma D_dd2d0 : decode_any W_dd2d0 = Some (OpImm ALU_ADD 11 11 2198, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2d4 : bv 32 := 0x04000637.
Lemma F_dd2d4 : fetch_word Ubsan.M.loaded_segments (0xe1c0c : word) = Some W_dd2d4.
Proof. vm_refl. Qed.
Lemma D_dd2d4 : decode_any W_dd2d4 = Some (Lui 12 16384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2d8 : bv 32 := 0x001d4097.
Lemma F_dd2d8 : fetch_word Ubsan.M.loaded_segments (0xe1c10 : word) = Some W_dd2d8.
Proof. vm_refl. Qed.
Lemma D_dd2d8 : decode_any W_dd2d8 = Some (Auipc 1 468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2dc : bv 32 := 0xb2c080e7.
Lemma F_dd2dc : fetch_word Ubsan.M.loaded_segments (0xe1c14 : word) = Some W_dd2dc.
Proof. vm_refl. Qed.
Lemma D_dd2dc : decode_any W_dd2dc = Some (Jalr 1 1 2860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2e0 : bv 32 := 0x0280006f.
Lemma F_dd2e0 : fetch_word Ubsan.M.loaded_segments (0xe1c18 : word) = Some W_dd2e0.
Proof. vm_refl. Qed.
Lemma D_dd2e0 : decode_any W_dd2e0 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2e4 : bv 32 := 0x0023b517.
Lemma F_dd2e4 : fetch_word Ubsan.M.loaded_segments (0xe1c1c : word) = Some W_dd2e4.
Proof. vm_refl. Qed.
Lemma D_dd2e4 : decode_any W_dd2e4 = Some (Auipc 10 571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2e8 : bv 32 := 0x3d453503.
Lemma F_dd2e8 : fetch_word Ubsan.M.loaded_segments (0xe1c20 : word) = Some W_dd2e8.
Proof. vm_refl. Qed.
Lemma D_dd2e8 : decode_any W_dd2e8 = Some (Load SZ8 true 10 10 980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2ec : bv 32 := 0x00053683.
Lemma F_dd2ec : fetch_word Ubsan.M.loaded_segments (0xe1c24 : word) = Some W_dd2ec.
Proof. vm_refl. Qed.
Lemma D_dd2ec : decode_any W_dd2ec = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2f0 : bv 32 := 0xfff38517.
Lemma F_dd2f0 : fetch_word Ubsan.M.loaded_segments (0xe1c28 : word) = Some W_dd2f0.
Proof. vm_refl. Qed.
Lemma D_dd2f0 : decode_any W_dd2f0 = Some (Auipc 10 1048376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2f4 : bv 32 := 0x01300593.
Lemma F_dd2f4 : fetch_word Ubsan.M.loaded_segments (0xe1c2c : word) = Some W_dd2f4.
Proof. vm_refl. Qed.
Lemma D_dd2f4 : decode_any W_dd2f4 = Some (OpImm ALU_ADD 11 0 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2f8 : bv 32 := 0x8e550513.
Lemma F_dd2f8 : fetch_word Ubsan.M.loaded_segments (0xe1c30 : word) = Some W_dd2f8.
Proof. vm_refl. Qed.
Lemma D_dd2f8 : decode_any W_dd2f8 = Some (OpImm ALU_ADD 10 10 2277, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd2fc : bv 32 := 0x00100613.
Lemma F_dd2fc : fetch_word Ubsan.M.loaded_segments (0xe1c34 : word) = Some W_dd2fc.
Proof. vm_refl. Qed.
Lemma D_dd2fc : decode_any W_dd2fc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd300 : bv 32 := 0x001d4097.
Lemma F_dd300 : fetch_word Ubsan.M.loaded_segments (0xe1c38 : word) = Some W_dd300.
Proof. vm_refl. Qed.
Lemma D_dd300 : decode_any W_dd300 = Some (Auipc 1 468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd304 : bv 32 := 0x290080e7.
Lemma F_dd304 : fetch_word Ubsan.M.loaded_segments (0xe1c3c : word) = Some W_dd304.
Proof. vm_refl. Qed.
Lemma D_dd304 : decode_any W_dd304 = Some (Jalr 1 1 656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd308 : bv 32 := 0x00200513.
Lemma F_dd308 : fetch_word Ubsan.M.loaded_segments (0xe1c40 : word) = Some W_dd308.
Proof. vm_refl. Qed.
Lemma D_dd308 : decode_any W_dd308 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd30c : bv 32 := 0x001d0097.
Lemma F_dd30c : fetch_word Ubsan.M.loaded_segments (0xe1c44 : word) = Some W_dd30c.
Proof. vm_refl. Qed.
Lemma D_dd30c : decode_any W_dd30c = Some (Auipc 1 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd310 : bv 32 := 0xba8080e7.
Lemma F_dd310 : fetch_word Ubsan.M.loaded_segments (0xe1c48 : word) = Some W_dd310.
Proof. vm_refl. Qed.
Lemma D_dd310 : decode_any W_dd310 = Some (Jalr 1 1 2984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd314 : bv 32 := 0x0023b517.
Lemma F_dd314 : fetch_word Ubsan.M.loaded_segments (0xe1c4c : word) = Some W_dd314.
Proof. vm_refl. Qed.
Lemma D_dd314 : decode_any W_dd314 = Some (Auipc 10 571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd318 : bv 32 := 0x3a453503.
Lemma F_dd318 : fetch_word Ubsan.M.loaded_segments (0xe1c50 : word) = Some W_dd318.
Proof. vm_refl. Qed.
Lemma D_dd318 : decode_any W_dd318 = Some (Load SZ8 true 10 10 932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd31c : bv 32 := 0x00053503.
Lemma F_dd31c : fetch_word Ubsan.M.loaded_segments (0xe1c54 : word) = Some W_dd31c.
Proof. vm_refl. Qed.
Lemma D_dd31c : decode_any W_dd31c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd320 : bv 32 := 0xfff4f597.
Lemma F_dd320 : fetch_word Ubsan.M.loaded_segments (0xe1c58 : word) = Some W_dd320.
Proof. vm_refl. Qed.
Lemma D_dd320 : decode_any W_dd320 = Some (Auipc 11 1048399, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd324 : bv 32 := 0x1e658593.
Lemma F_dd324 : fetch_word Ubsan.M.loaded_segments (0xe1c5c : word) = Some W_dd324.
Proof. vm_refl. Qed.
Lemma D_dd324 : decode_any W_dd324 = Some (OpImm ALU_ADD 11 11 486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd328 : bv 32 := 0xf91ff06f.
Lemma F_dd328 : fetch_word Ubsan.M.loaded_segments (0xe1c60 : word) = Some W_dd328.
Proof. vm_refl. Qed.
Lemma D_dd328 : decode_any W_dd328 = Some (Jal 0 2097040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd32c : bv 32 := 0x0023b517.
Lemma F_dd32c : fetch_word Ubsan.M.loaded_segments (0xe1c64 : word) = Some W_dd32c.
Proof. vm_refl. Qed.
Lemma D_dd32c : decode_any W_dd32c = Some (Auipc 10 571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd330 : bv 32 := 0x38c53503.
Lemma F_dd330 : fetch_word Ubsan.M.loaded_segments (0xe1c68 : word) = Some W_dd330.
Proof. vm_refl. Qed.
Lemma D_dd330 : decode_any W_dd330 = Some (Load SZ8 true 10 10 908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd334 : bv 32 := 0x00053683.
Lemma F_dd334 : fetch_word Ubsan.M.loaded_segments (0xe1c6c : word) = Some W_dd334.
Proof. vm_refl. Qed.
Lemma D_dd334 : decode_any W_dd334 = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd338 : bv 32 := 0xfff38517.
Lemma F_dd338 : fetch_word Ubsan.M.loaded_segments (0xe1c70 : word) = Some W_dd338.
Proof. vm_refl. Qed.
Lemma D_dd338 : decode_any W_dd338 = Some (Auipc 10 1048376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd33c : bv 32 := 0x01300593.
Lemma F_dd33c : fetch_word Ubsan.M.loaded_segments (0xe1c74 : word) = Some W_dd33c.
Proof. vm_refl. Qed.
Lemma D_dd33c : decode_any W_dd33c = Some (OpImm ALU_ADD 11 0 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd340 : bv 32 := 0x89d50513.
Lemma F_dd340 : fetch_word Ubsan.M.loaded_segments (0xe1c78 : word) = Some W_dd340.
Proof. vm_refl. Qed.
Lemma D_dd340 : decode_any W_dd340 = Some (OpImm ALU_ADD 10 10 2205, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd344 : bv 32 := 0xfb9ff06f.
Lemma F_dd344 : fetch_word Ubsan.M.loaded_segments (0xe1c7c : word) = Some W_dd344.
Proof. vm_refl. Qed.
Lemma D_dd344 : decode_any W_dd344 = Some (Jal 0 2097080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd348 : bv 32 := 0x00008067.
Lemma F_dd348 : fetch_word Ubsan.M.loaded_segments (0xe1c80 : word) = Some W_dd348.
Proof. vm_refl. Qed.
Lemma D_dd348 : decode_any W_dd348 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd34c : bv 32 := 0x00000513.
Lemma F_dd34c : fetch_word Ubsan.M.loaded_segments (0xe1c84 : word) = Some W_dd34c.
Proof. vm_refl. Qed.
Lemma D_dd34c : decode_any W_dd34c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd350 : bv 32 := 0x00008067.
Lemma F_dd350 : fetch_word Ubsan.M.loaded_segments (0xe1c88 : word) = Some W_dd350.
Proof. vm_refl. Qed.
Lemma D_dd350 : decode_any W_dd350 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd4f4 : bv 32 := 0xfb010113.
Lemma F_dd4f4 : fetch_word Ubsan.M.loaded_segments (0xe1e2c : word) = Some W_dd4f4.
Proof. vm_refl. Qed.
Lemma D_dd4f4 : decode_any W_dd4f4 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd4f8 : bv 32 := 0x00113423.
Lemma F_dd4f8 : fetch_word Ubsan.M.loaded_segments (0xe1e30 : word) = Some W_dd4f8.
Proof. vm_refl. Qed.
Lemma D_dd4f8 : decode_any W_dd4f8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd4fc : bv 32 := 0x02f13c23.
Lemma F_dd4fc : fetch_word Ubsan.M.loaded_segments (0xe1e34 : word) = Some W_dd4fc.
Proof. vm_refl. Qed.
Lemma D_dd4fc : decode_any W_dd4fc = Some (Store SZ8 2 15 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd500 : bv 32 := 0x05013023.
Lemma F_dd500 : fetch_word Ubsan.M.loaded_segments (0xe1e38 : word) = Some W_dd500.
Proof. vm_refl. Qed.
Lemma D_dd500 : decode_any W_dd500 = Some (Store SZ8 2 16 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd504 : bv 32 := 0x05113423.
Lemma F_dd504 : fetch_word Ubsan.M.loaded_segments (0xe1e3c : word) = Some W_dd504.
Proof. vm_refl. Qed.
Lemma D_dd504 : decode_any W_dd504 = Some (Store SZ8 2 17 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd508 : bv 32 := 0x00b13c23.
Lemma F_dd508 : fetch_word Ubsan.M.loaded_segments (0xe1e40 : word) = Some W_dd508.
Proof. vm_refl. Qed.
Lemma D_dd508 : decode_any W_dd508 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd50c : bv 32 := 0x02c13023.
Lemma F_dd50c : fetch_word Ubsan.M.loaded_segments (0xe1e44 : word) = Some W_dd50c.
Proof. vm_refl. Qed.
Lemma D_dd50c : decode_any W_dd50c = Some (Store SZ8 2 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd510 : bv 32 := 0x02d13423.
Lemma F_dd510 : fetch_word Ubsan.M.loaded_segments (0xe1e48 : word) = Some W_dd510.
Proof. vm_refl. Qed.
Lemma D_dd510 : decode_any W_dd510 = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd514 : bv 32 := 0x02e13823.
Lemma F_dd514 : fetch_word Ubsan.M.loaded_segments (0xe1e4c : word) = Some W_dd514.
Proof. vm_refl. Qed.
Lemma D_dd514 : decode_any W_dd514 = Some (Store SZ8 2 14 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd518 : bv 32 := 0x01810513.
Lemma F_dd518 : fetch_word Ubsan.M.loaded_segments (0xe1e50 : word) = Some W_dd518.
Proof. vm_refl. Qed.
Lemma D_dd518 : decode_any W_dd518 = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd51c : bv 32 := 0x00a13023.
Lemma F_dd51c : fetch_word Ubsan.M.loaded_segments (0xe1e54 : word) = Some W_dd51c.
Proof. vm_refl. Qed.
Lemma D_dd51c : decode_any W_dd51c = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd520 : bv 32 := 0xfff37517.
Lemma F_dd520 : fetch_word Ubsan.M.loaded_segments (0xe1e58 : word) = Some W_dd520.
Proof. vm_refl. Qed.
Lemma D_dd520 : decode_any W_dd520 = Some (Auipc 10 1048375, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd524 : bv 32 := 0x6c950513.
Lemma F_dd524 : fetch_word Ubsan.M.loaded_segments (0xe1e5c : word) = Some W_dd524.
Proof. vm_refl. Qed.
Lemma D_dd524 : decode_any W_dd524 = Some (OpImm ALU_ADD 10 10 1737, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd528 : bv 32 := 0x01810593.
Lemma F_dd528 : fetch_word Ubsan.M.loaded_segments (0xe1e60 : word) = Some W_dd528.
Proof. vm_refl. Qed.
Lemma D_dd528 : decode_any W_dd528 = Some (OpImm ALU_ADD 11 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd52c : bv 32 := 0x001d9097.
Lemma F_dd52c : fetch_word Ubsan.M.loaded_segments (0xe1e64 : word) = Some W_dd52c.
Proof. vm_refl. Qed.
Lemma D_dd52c : decode_any W_dd52c = Some (Auipc 1 473, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd530 : bv 32 := 0xc34080e7.
Lemma F_dd530 : fetch_word Ubsan.M.loaded_segments (0xe1e68 : word) = Some W_dd530.
Proof. vm_refl. Qed.
Lemma D_dd530 : decode_any W_dd530 = Some (Jalr 1 1 3124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd534 : bv 32 := 0x00813083.
Lemma F_dd534 : fetch_word Ubsan.M.loaded_segments (0xe1e6c : word) = Some W_dd534.
Proof. vm_refl. Qed.
Lemma D_dd534 : decode_any W_dd534 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd538 : bv 32 := 0x05010113.
Lemma F_dd538 : fetch_word Ubsan.M.loaded_segments (0xe1e70 : word) = Some W_dd538.
Proof. vm_refl. Qed.
Lemma D_dd538 : decode_any W_dd538 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd53c : bv 32 := 0x00008067.
Lemma F_dd53c : fetch_word Ubsan.M.loaded_segments (0xe1e74 : word) = Some W_dd53c.
Proof. vm_refl. Qed.
Lemma D_dd53c : decode_any W_dd53c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbd8 : bv 32 := 0xfe010113.
Lemma F_ddbd8 : fetch_word Ubsan.M.loaded_segments (0xe2670 : word) = Some W_ddbd8.
Proof. vm_refl. Qed.
Lemma D_ddbd8 : decode_any W_ddbd8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbdc : bv 32 := 0x00113c23.
Lemma F_ddbdc : fetch_word Ubsan.M.loaded_segments (0xe2674 : word) = Some W_ddbdc.
Proof. vm_refl. Qed.
Lemma D_ddbdc : decode_any W_ddbdc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbe0 : bv 32 := 0x00813823.
Lemma F_ddbe0 : fetch_word Ubsan.M.loaded_segments (0xe2678 : word) = Some W_ddbe0.
Proof. vm_refl. Qed.
Lemma D_ddbe0 : decode_any W_ddbe0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbe4 : bv 32 := 0x00913423.
Lemma F_ddbe4 : fetch_word Ubsan.M.loaded_segments (0xe267c : word) = Some W_ddbe4.
Proof. vm_refl. Qed.
Lemma D_ddbe4 : decode_any W_ddbe4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbe8 : bv 32 := 0x02010413.
Lemma F_ddbe8 : fetch_word Ubsan.M.loaded_segments (0xe2680 : word) = Some W_ddbe8.
Proof. vm_refl. Qed.
Lemma D_ddbe8 : decode_any W_ddbe8 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbec : bv 32 := 0x0024d517.
Lemma F_ddbec : fetch_word Ubsan.M.loaded_segments (0xe2684 : word) = Some W_ddbec.
Proof. vm_refl. Qed.
Lemma D_ddbec : decode_any W_ddbec = Some (Auipc 10 589, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbf0 : bv 32 := 0x91c50493.
Lemma F_ddbf0 : fetch_word Ubsan.M.loaded_segments (0xe2688 : word) = Some W_ddbf0.
Proof. vm_refl. Qed.
Lemma D_ddbf0 : decode_any W_ddbf0 = Some (OpImm ALU_ADD 9 10 2332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbf4 : bv 32 := 0x0004c503.
Lemma F_ddbf4 : fetch_word Ubsan.M.loaded_segments (0xe268c : word) = Some W_ddbf4.
Proof. vm_refl. Qed.
Lemma D_ddbf4 : decode_any W_ddbf4 = Some (Load SZ1 false 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbf8 : bv 32 := 0x0a050863.
Lemma F_ddbf8 : fetch_word Ubsan.M.loaded_segments (0xe2690 : word) = Some W_ddbf8.
Proof. vm_refl. Qed.
Lemma D_ddbf8 : decode_any W_ddbf8 = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddca8 : bv 32 := 0x01813083.
Lemma F_ddca8 : fetch_word Ubsan.M.loaded_segments (0xe2740 : word) = Some W_ddca8.
Proof. vm_refl. Qed.
Lemma D_ddca8 : decode_any W_ddca8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcac : bv 32 := 0x01013403.
Lemma F_ddcac : fetch_word Ubsan.M.loaded_segments (0xe2744 : word) = Some W_ddcac.
Proof. vm_refl. Qed.
Lemma D_ddcac : decode_any W_ddcac = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcb0 : bv 32 := 0x00813483.
Lemma F_ddcb0 : fetch_word Ubsan.M.loaded_segments (0xe2748 : word) = Some W_ddcb0.
Proof. vm_refl. Qed.
Lemma D_ddcb0 : decode_any W_ddcb0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcb4 : bv 32 := 0x02010113.
Lemma F_ddcb4 : fetch_word Ubsan.M.loaded_segments (0xe274c : word) = Some W_ddcb4.
Proof. vm_refl. Qed.
Lemma D_ddcb4 : decode_any W_ddcb4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcb8 : bv 32 := 0x00008067.
Lemma F_ddcb8 : fetch_word Ubsan.M.loaded_segments (0xe2750 : word) = Some W_ddcb8.
Proof. vm_refl. Qed.
Lemma D_ddcb8 : decode_any W_ddcb8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
