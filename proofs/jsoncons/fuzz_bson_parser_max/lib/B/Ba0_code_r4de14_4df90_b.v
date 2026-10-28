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
Definition W_6331c : bv 32 := 0x06048a63.
Lemma F_6331c : fetch_word AsanUbsan.M.loaded_segments (0x63734 : word) = Some W_6331c.
Proof. vm_refl. Qed.
Lemma D_6331c : decode_any W_6331c = Some (Branch BC_EQ 9 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63320 : bv 32 := 0x000d4597.
Lemma F_63320 : fetch_word AsanUbsan.M.loaded_segments (0x63738 : word) = Some W_63320.
Proof. vm_refl. Qed.
Lemma D_63320 : decode_any W_63320 = Some (Auipc 11 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63324 : bv 32 := 0xd785ba83.
Lemma F_63324 : fetch_word AsanUbsan.M.loaded_segments (0x6373c : word) = Some W_63324.
Proof. vm_refl. Qed.
Lemma D_63324 : decode_any W_63324 = Some (Load SZ8 true 21 11 3448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63328 : bv 32 := 0x0fbac583.
Lemma F_63328 : fetch_word AsanUbsan.M.loaded_segments (0x63740 : word) = Some W_63328.
Proof. vm_refl. Qed.
Lemma D_63328 : decode_any W_63328 = Some (Load SZ1 false 11 21 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6332c : bv 32 := 0x06058263.
Lemma F_6332c : fetch_word AsanUbsan.M.loaded_segments (0x63744 : word) = Some W_6332c.
Proof. vm_refl. Qed.
Lemma D_6332c : decode_any W_6332c = Some (Branch BC_EQ 11 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63330 : bv 32 := 0x00150493.
Lemma F_63330 : fetch_word AsanUbsan.M.loaded_segments (0x63748 : word) = Some W_63330.
Proof. vm_refl. Qed.
Lemma D_63330 : decode_any W_63330 = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63334 : bv 32 := 0x0934f463.
Lemma F_63334 : fetch_word AsanUbsan.M.loaded_segments (0x6374c : word) = Some W_63334.
Proof. vm_refl. Qed.
Lemma D_63334 : decode_any W_63334 = Some (Branch BC_GEU 9 19 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63338 : bv 32 := 0xfff94593.
Lemma F_63338 : fetch_word AsanUbsan.M.loaded_segments (0x63750 : word) = Some W_63338.
Proof. vm_refl. Qed.
Lemma D_63338 : decode_any W_63338 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6333c : bv 32 := 0x80040a13.
Lemma F_6333c : fetch_word AsanUbsan.M.loaded_segments (0x63754 : word) = Some W_6333c.
Proof. vm_refl. Qed.
Lemma D_6333c : decode_any W_6333c = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63340 : bv 32 := 0xfa8a0a13.
Lemma F_63340 : fetch_word AsanUbsan.M.loaded_segments (0x63758 : word) = Some W_63340.
Proof. vm_refl. Qed.
Lemma D_63340 : decode_any W_63340 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63344 : bv 32 := 0x0895e663.
Lemma F_63344 : fetch_word AsanUbsan.M.loaded_segments (0x6375c : word) = Some W_63344.
Proof. vm_refl. Qed.
Lemma D_63344 : decode_any W_63344 = Some (Branch BC_LTU 11 9 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63348 : bv 32 := 0xfbf48593.
Lemma F_63348 : fetch_word AsanUbsan.M.loaded_segments (0x63760 : word) = Some W_63348.
Proof. vm_refl. Qed.
Lemma D_63348 : decode_any W_63348 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6334c : bv 32 := 0xfbf00613.
Lemma F_6334c : fetch_word AsanUbsan.M.loaded_segments (0x63764 : word) = Some W_6334c.
Proof. vm_refl. Qed.
Lemma D_6334c : decode_any W_6334c = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63350 : bv 32 := 0x0eb67863.
Lemma F_63350 : fetch_word AsanUbsan.M.loaded_segments (0x63768 : word) = Some W_63350.
Proof. vm_refl. Qed.
Lemma D_63350 : decode_any W_63350 = Some (Branch BC_GEU 12 11 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63354 : bv 32 := 0x000d4597.
Lemma F_63354 : fetch_word AsanUbsan.M.loaded_segments (0x6376c : word) = Some W_63354.
Proof. vm_refl. Qed.
Lemma D_63354 : decode_any W_63354 = Some (Auipc 11 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63358 : bv 32 := 0xd545b583.
Lemma F_63358 : fetch_word AsanUbsan.M.loaded_segments (0x63770 : word) = Some W_63358.
Proof. vm_refl. Qed.
Lemma D_63358 : decode_any W_63358 = Some (Load SZ8 true 11 11 3412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6335c : bv 32 := 0x009906b3.
Lemma F_6335c : fetch_word AsanUbsan.M.loaded_segments (0x63774 : word) = Some W_6335c.
Proof. vm_refl. Qed.
Lemma D_6335c : decode_any W_6335c = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63360 : bv 32 := 0x0005b603.
Lemma F_63360 : fetch_word AsanUbsan.M.loaded_segments (0x63778 : word) = Some W_63360.
Proof. vm_refl. Qed.
Lemma D_63360 : decode_any W_63360 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63364 : bv 32 := 0x00395593.
Lemma F_63364 : fetch_word AsanUbsan.M.loaded_segments (0x6377c : word) = Some W_63364.
Proof. vm_refl. Qed.
Lemma D_63364 : decode_any W_63364 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63368 : bv 32 := 0xfff68693.
Lemma F_63368 : fetch_word AsanUbsan.M.loaded_segments (0x63780 : word) = Some W_63368.
Proof. vm_refl. Qed.
Lemma D_63368 : decode_any W_63368 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6336c : bv 32 := 0x0036d713.
Lemma F_6336c : fetch_word AsanUbsan.M.loaded_segments (0x63784 : word) = Some W_6336c.
Proof. vm_refl. Qed.
Lemma D_6336c : decode_any W_6336c = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63370 : bv 32 := 0x00b605b3.
Lemma F_63370 : fetch_word AsanUbsan.M.loaded_segments (0x63788 : word) = Some W_63370.
Proof. vm_refl. Qed.
Lemma D_63370 : decode_any W_63370 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63374 : bv 32 := 0x00e60633.
Lemma F_63374 : fetch_word AsanUbsan.M.loaded_segments (0x6378c : word) = Some W_63374.
Proof. vm_refl. Qed.
Lemma D_63374 : decode_any W_63374 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63378 : bv 32 := 0xff85f713.
Lemma F_63378 : fetch_word AsanUbsan.M.loaded_segments (0x63790 : word) = Some W_63378.
Proof. vm_refl. Qed.
Lemma D_63378 : decode_any W_63378 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6337c : bv 32 := 0xff867793.
Lemma F_6337c : fetch_word AsanUbsan.M.loaded_segments (0x63794 : word) = Some W_6337c.
Proof. vm_refl. Qed.
Lemma D_6337c : decode_any W_6337c = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63380 : bv 32 := 0x00073703.
Lemma F_63380 : fetch_word AsanUbsan.M.loaded_segments (0x63798 : word) = Some W_63380.
Proof. vm_refl. Qed.
Lemma D_63380 : decode_any W_63380 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63384 : bv 32 := 0x0007b783.
Lemma F_63384 : fetch_word AsanUbsan.M.loaded_segments (0x6379c : word) = Some W_63384.
Proof. vm_refl. Qed.
Lemma D_63384 : decode_any W_63384 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63388 : bv 32 := 0x00e7e733.
Lemma F_63388 : fetch_word AsanUbsan.M.loaded_segments (0x637a0 : word) = Some W_63388.
Proof. vm_refl. Qed.
Lemma D_63388 : decode_any W_63388 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6338c : bv 32 := 0x0a071e63.
Lemma F_6338c : fetch_word AsanUbsan.M.loaded_segments (0x637a4 : word) = Some W_6338c.
Proof. vm_refl. Qed.
Lemma D_6338c : decode_any W_6338c = Some (Branch BC_NE 14 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63440 : bv 32 := 0x02049e63.
Lemma F_63440 : fetch_word AsanUbsan.M.loaded_segments (0x63858 : word) = Some W_63440.
Proof. vm_refl. Qed.
Lemma D_63440 : decode_any W_63440 = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6347c : bv 32 := 0x00050b13.
Lemma F_6347c : fetch_word AsanUbsan.M.loaded_segments (0x63894 : word) = Some W_6347c.
Proof. vm_refl. Qed.
Lemma D_6347c : decode_any W_6347c = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63480 : bv 32 := 0x00090513.
Lemma F_63480 : fetch_word AsanUbsan.M.loaded_segments (0x63898 : word) = Some W_63480.
Proof. vm_refl. Qed.
Lemma D_63480 : decode_any W_63480 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63484 : bv 32 := 0x00048593.
Lemma F_63484 : fetch_word AsanUbsan.M.loaded_segments (0x6389c : word) = Some W_63484.
Proof. vm_refl. Qed.
Lemma D_63484 : decode_any W_63484 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63488 : bv 32 := 0x421170ef.
Lemma F_63488 : fetch_word AsanUbsan.M.loaded_segments (0x638a0 : word) = Some W_63488.
Proof. vm_refl. Qed.
Lemma D_63488 : decode_any W_63488 = Some (Jal 1 97312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6348c : bv 32 := 0x00050913.
Lemma F_6348c : fetch_word AsanUbsan.M.loaded_segments (0x638a4 : word) = Some W_6348c.
Proof. vm_refl. Qed.
Lemma D_6348c : decode_any W_6348c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63490 : bv 32 := 0x000b0513.
Lemma F_63490 : fetch_word AsanUbsan.M.loaded_segments (0x638a8 : word) = Some W_63490.
Proof. vm_refl. Qed.
Lemma D_63490 : decode_any W_63490 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63494 : bv 32 := 0xee090ee3.
Lemma F_63494 : fetch_word AsanUbsan.M.loaded_segments (0x638ac : word) = Some W_63494.
Proof. vm_refl. Qed.
Lemma D_63494 : decode_any W_63494 = Some (Branch BC_EQ 18 0 7932, 4%Z).
Proof. vm_refl. Qed.
