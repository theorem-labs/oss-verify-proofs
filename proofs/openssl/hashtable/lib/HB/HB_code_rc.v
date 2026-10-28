(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1afb34 : bv 32 := 0xfff4c593.
Lemma F_1afb34 : fetch_word AsanUbsan.M.loaded_segments (0x1aab04 : word) = Some W_1afb34.
Proof. vm_refl. Qed.
Lemma D_1afb34 : decode_any W_1afb34 = Some (OpImm ALU_XOR 11 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb38 : bv 32 := 0x80040a13.
Lemma F_1afb38 : fetch_word AsanUbsan.M.loaded_segments (0x1aab08 : word) = Some W_1afb38.
Proof. vm_refl. Qed.
Lemma D_1afb38 : decode_any W_1afb38 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb3c : bv 32 := 0xfb8a0a13.
Lemma F_1afb3c : fetch_word AsanUbsan.M.loaded_segments (0x1aab0c : word) = Some W_1afb3c.
Proof. vm_refl. Qed.
Lemma D_1afb3c : decode_any W_1afb3c = Some (OpImm ALU_ADD 20 20 4024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb40 : bv 32 := 0x06a5e863.
Lemma F_1afb40 : fetch_word AsanUbsan.M.loaded_segments (0x1aab10 : word) = Some W_1afb40.
Proof. vm_refl. Qed.
Lemma D_1afb40 : decode_any W_1afb40 = Some (Branch BC_LTU 11 10 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb44 : bv 32 := 0xfbf50593.
Lemma F_1afb44 : fetch_word AsanUbsan.M.loaded_segments (0x1aab14 : word) = Some W_1afb44.
Proof. vm_refl. Qed.
Lemma D_1afb44 : decode_any W_1afb44 = Some (OpImm ALU_ADD 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb48 : bv 32 := 0xfc000613.
Lemma F_1afb48 : fetch_word AsanUbsan.M.loaded_segments (0x1aab18 : word) = Some W_1afb48.
Proof. vm_refl. Qed.
Lemma D_1afb48 : decode_any W_1afb48 = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb4c : bv 32 := 0x0cc5ee63.
Lemma F_1afb4c : fetch_word AsanUbsan.M.loaded_segments (0x1aab1c : word) = Some W_1afb4c.
Proof. vm_refl. Qed.
Lemma D_1afb4c : decode_any W_1afb4c = Some (Branch BC_LTU 11 12 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb50 : bv 32 := 0x00434597.
Lemma F_1afb50 : fetch_word AsanUbsan.M.loaded_segments (0x1aab20 : word) = Some W_1afb50.
Proof. vm_refl. Qed.
Lemma D_1afb50 : decode_any W_1afb50 = Some (Auipc 11 1076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb54 : bv 32 := 0xfb85b583.
Lemma F_1afb54 : fetch_word AsanUbsan.M.loaded_segments (0x1aab24 : word) = Some W_1afb54.
Proof. vm_refl. Qed.
Lemma D_1afb54 : decode_any W_1afb54 = Some (Load SZ8 true 11 11 4024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb58 : bv 32 := 0x00a486b3.
Lemma F_1afb58 : fetch_word AsanUbsan.M.loaded_segments (0x1aab28 : word) = Some W_1afb58.
Proof. vm_refl. Qed.
Lemma D_1afb58 : decode_any W_1afb58 = Some (Op ALU_ADD 13 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb5c : bv 32 := 0x0005b603.
Lemma F_1afb5c : fetch_word AsanUbsan.M.loaded_segments (0x1aab2c : word) = Some W_1afb5c.
Proof. vm_refl. Qed.
Lemma D_1afb5c : decode_any W_1afb5c = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb60 : bv 32 := 0x0034d593.
Lemma F_1afb60 : fetch_word AsanUbsan.M.loaded_segments (0x1aab30 : word) = Some W_1afb60.
Proof. vm_refl. Qed.
Lemma D_1afb60 : decode_any W_1afb60 = Some (ShiftImm ALU_SRL 11 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb64 : bv 32 := 0xfff68693.
Lemma F_1afb64 : fetch_word AsanUbsan.M.loaded_segments (0x1aab34 : word) = Some W_1afb64.
Proof. vm_refl. Qed.
Lemma D_1afb64 : decode_any W_1afb64 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb68 : bv 32 := 0x0036d713.
Lemma F_1afb68 : fetch_word AsanUbsan.M.loaded_segments (0x1aab38 : word) = Some W_1afb68.
Proof. vm_refl. Qed.
Lemma D_1afb68 : decode_any W_1afb68 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb6c : bv 32 := 0x00b605b3.
Lemma F_1afb6c : fetch_word AsanUbsan.M.loaded_segments (0x1aab3c : word) = Some W_1afb6c.
Proof. vm_refl. Qed.
Lemma D_1afb6c : decode_any W_1afb6c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb70 : bv 32 := 0x00e60633.
Lemma F_1afb70 : fetch_word AsanUbsan.M.loaded_segments (0x1aab40 : word) = Some W_1afb70.
Proof. vm_refl. Qed.
Lemma D_1afb70 : decode_any W_1afb70 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb74 : bv 32 := 0xff85f713.
Lemma F_1afb74 : fetch_word AsanUbsan.M.loaded_segments (0x1aab44 : word) = Some W_1afb74.
Proof. vm_refl. Qed.
Lemma D_1afb74 : decode_any W_1afb74 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb78 : bv 32 := 0xff867793.
Lemma F_1afb78 : fetch_word AsanUbsan.M.loaded_segments (0x1aab48 : word) = Some W_1afb78.
Proof. vm_refl. Qed.
Lemma D_1afb78 : decode_any W_1afb78 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb7c : bv 32 := 0x00073703.
Lemma F_1afb7c : fetch_word AsanUbsan.M.loaded_segments (0x1aab4c : word) = Some W_1afb7c.
Proof. vm_refl. Qed.
Lemma D_1afb7c : decode_any W_1afb7c = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb80 : bv 32 := 0x0007b783.
Lemma F_1afb80 : fetch_word AsanUbsan.M.loaded_segments (0x1aab50 : word) = Some W_1afb80.
Proof. vm_refl. Qed.
Lemma D_1afb80 : decode_any W_1afb80 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb84 : bv 32 := 0x00e7e733.
Lemma F_1afb84 : fetch_word AsanUbsan.M.loaded_segments (0x1aab54 : word) = Some W_1afb84.
Proof. vm_refl. Qed.
Lemma D_1afb84 : decode_any W_1afb84 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb88 : bv 32 := 0x14071663.
Lemma F_1afb88 : fetch_word AsanUbsan.M.loaded_segments (0x1aab58 : word) = Some W_1afb88.
Proof. vm_refl. Qed.
Lemma D_1afb88 : decode_any W_1afb88 = Some (Branch BC_NE 14 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1afb8c : bv 32 := 0x06010113.
Lemma F_1afb8c : fetch_word AsanUbsan.M.loaded_segments (0x1aab5c : word) = Some W_1afb8c.
Proof. vm_refl. Qed.
Lemma D_1afb8c : decode_any W_1afb8c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.
