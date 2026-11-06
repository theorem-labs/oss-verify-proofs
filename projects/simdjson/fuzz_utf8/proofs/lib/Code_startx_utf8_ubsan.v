(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_bcb60 : bv 32 := 0x0004b503.
Lemma F_bcb60 : fetch_word Ubsan.M.loaded_segments (0xbcc5c : word) = Some W_bcb60.
Proof. vm_refl. Qed.
Lemma D_bcb60 : decode_any W_bcb60 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb64 : bv 32 := 0x00848493.
Lemma F_bcb64 : fetch_word Ubsan.M.loaded_segments (0xbcc60 : word) = Some W_bcb64.
Proof. vm_refl. Qed.
Lemma D_bcb64 : decode_any W_bcb64 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb68 : bv 32 := 0xfe051ce3.
Lemma F_bcb68 : fetch_word Ubsan.M.loaded_segments (0xbcc64 : word) = Some W_bcb68.
Proof. vm_refl. Qed.
Lemma D_bcb68 : decode_any W_bcb68 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb6c : bv 32 := 0x00051517.
Lemma F_bcb6c : fetch_word Ubsan.M.loaded_segments (0xbcc68 : word) = Some W_bcb6c.
Proof. vm_refl. Qed.
Lemma D_bcb6c : decode_any W_bcb6c = Some (Auipc 10 81, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb70 : bv 32 := 0x0a050913.
Lemma F_bcb70 : fetch_word Ubsan.M.loaded_segments (0xbcc6c : word) = Some W_bcb70.
Proof. vm_refl. Qed.
Lemma D_bcb70 : decode_any W_bcb70 = Some (OpImm ALU_ADD 18 10 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb74 : bv 32 := 0x00993423.
Lemma F_bcb74 : fetch_word Ubsan.M.loaded_segments (0xbcc70 : word) = Some W_bcb74.
Proof. vm_refl. Qed.
Lemma D_bcb74 : decode_any W_bcb74 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb78 : bv 32 := 0x0004b583.
Lemma F_bcb78 : fetch_word Ubsan.M.loaded_segments (0xbcc74 : word) = Some W_bcb78.
Proof. vm_refl. Qed.
Lemma D_bcb78 : decode_any W_bcb78 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb7c : bv 32 := 0x04058c63.
Lemma F_bcb7c : fetch_word Ubsan.M.loaded_segments (0xbcc78 : word) = Some W_bcb7c.
Proof. vm_refl. Qed.
Lemma D_bcb7c : decode_any W_bcb7c = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb80 : bv 32 := 0x01048493.
Lemma F_bcb80 : fetch_word Ubsan.M.loaded_segments (0xbcc7c : word) = Some W_bcb80.
Proof. vm_refl. Qed.
Lemma D_bcb80 : decode_any W_bcb80 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb84 : bv 32 := 0x02500513.
Lemma F_bcb84 : fetch_word Ubsan.M.loaded_segments (0xbcc80 : word) = Some W_bcb84.
Proof. vm_refl. Qed.
Lemma D_bcb84 : decode_any W_bcb84 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb88 : bv 32 := 0x03010613.
Lemma F_bcb88 : fetch_word Ubsan.M.loaded_segments (0xbcc84 : word) = Some W_bcb88.
Proof. vm_refl. Qed.
Lemma D_bcb88 : decode_any W_bcb88 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb8c : bv 32 := 0x0100006f.
Lemma F_bcb8c : fetch_word Ubsan.M.loaded_segments (0xbcc88 : word) = Some W_bcb8c.
Proof. vm_refl. Qed.
Lemma D_bcb8c : decode_any W_bcb8c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb90 : bv 32 := 0x0004b583.
Lemma F_bcb90 : fetch_word Ubsan.M.loaded_segments (0xbcc8c : word) = Some W_bcb90.
Proof. vm_refl. Qed.
Lemma D_bcb90 : decode_any W_bcb90 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb94 : bv 32 := 0x01048493.
Lemma F_bcb94 : fetch_word Ubsan.M.loaded_segments (0xbcc90 : word) = Some W_bcb94.
Proof. vm_refl. Qed.
Lemma D_bcb94 : decode_any W_bcb94 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb98 : bv 32 := 0x00058e63.
Lemma F_bcb98 : fetch_word Ubsan.M.loaded_segments (0xbcc94 : word) = Some W_bcb98.
Proof. vm_refl. Qed.
Lemma D_bcb98 : decode_any W_bcb98 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb9c : bv 32 := 0xfeb56ae3.
Lemma F_bcb9c : fetch_word Ubsan.M.loaded_segments (0xbcc98 : word) = Some W_bcb9c.
Proof. vm_refl. Qed.
Lemma D_bcb9c : decode_any W_bcb9c = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcba0 : bv 32 := 0xff84b683.
Lemma F_bcba0 : fetch_word Ubsan.M.loaded_segments (0xbcc9c : word) = Some W_bcba0.
Proof. vm_refl. Qed.
Lemma D_bcba0 : decode_any W_bcba0 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcba4 : bv 32 := 0x00359593.
Lemma F_bcba4 : fetch_word Ubsan.M.loaded_segments (0xbcca0 : word) = Some W_bcba4.
Proof. vm_refl. Qed.
Lemma D_bcba4 : decode_any W_bcba4 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcba8 : bv 32 := 0x00b605b3.
Lemma F_bcba8 : fetch_word Ubsan.M.loaded_segments (0xbcca4 : word) = Some W_bcba8.
Proof. vm_refl. Qed.
Lemma D_bcba8 : decode_any W_bcba8 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbac : bv 32 := 0x00d5b023.
Lemma F_bcbac : fetch_word Ubsan.M.loaded_segments (0xbcca8 : word) = Some W_bcbac.
Proof. vm_refl. Qed.
Lemma D_bcbac : decode_any W_bcbac = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbb0 : bv 32 := 0xfe1ff06f.
Lemma F_bcbb0 : fetch_word Ubsan.M.loaded_segments (0xbccac : word) = Some W_bcbb0.
Proof. vm_refl. Qed.
Lemma D_bcbb0 : decode_any W_bcbb0 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbb4 : bv 32 := 0x0b013583.
Lemma F_bcbb4 : fetch_word Ubsan.M.loaded_segments (0xbccb0 : word) = Some W_bcbb4.
Proof. vm_refl. Qed.
Lemma D_bcbb4 : decode_any W_bcbb4 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbb8 : bv 32 := 0x13013503.
Lemma F_bcbb8 : fetch_word Ubsan.M.loaded_segments (0xbccb4 : word) = Some W_bcbb8.
Proof. vm_refl. Qed.
Lemma D_bcbb8 : decode_any W_bcbb8 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbbc : bv 32 := 0x00051617.
Lemma F_bcbbc : fetch_word Ubsan.M.loaded_segments (0xbccb8 : word) = Some W_bcbbc.
Proof. vm_refl. Qed.
Lemma D_bcbbc : decode_any W_bcbbc = Some (Auipc 12 81, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbc0 : bv 32 := 0x0ab63c23.
Lemma F_bcbc0 : fetch_word Ubsan.M.loaded_segments (0xbccbc : word) = Some W_bcbc0.
Proof. vm_refl. Qed.
Lemma D_bcbc0 : decode_any W_bcbc0 = Some (Store SZ8 12 11 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbc4 : bv 32 := 0x00050c63.
Lemma F_bcbc4 : fetch_word Ubsan.M.loaded_segments (0xbccc0 : word) = Some W_bcbc4.
Proof. vm_refl. Qed.
Lemma D_bcbc4 : decode_any W_bcbc4 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbc8 : bv 32 := 0x00051597.
Lemma F_bcbc8 : fetch_word Ubsan.M.loaded_segments (0xbccc4 : word) = Some W_bcbc8.
Proof. vm_refl. Qed.
Lemma D_bcbc8 : decode_any W_bcbc8 = Some (Auipc 11 81, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbcc : bv 32 := 0x02a5b623.
Lemma F_bcbcc : fetch_word Ubsan.M.loaded_segments (0xbccc8 : word) = Some W_bcbcc.
Proof. vm_refl. Qed.
Lemma D_bcbcc : decode_any W_bcbcc = Some (Store SZ8 11 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbd0 : bv 32 := 0x00c0006f.
Lemma F_bcbd0 : fetch_word Ubsan.M.loaded_segments (0xbcccc : word) = Some W_bcbd0.
Proof. vm_refl. Qed.
Lemma D_bcbd0 : decode_any W_bcbd0 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbd4 : bv 32 := 0x00051517.
Lemma F_bcbd4 : fetch_word Ubsan.M.loaded_segments (0xbccd0 : word) = Some W_bcbd4.
Proof. vm_refl. Qed.
Lemma D_bcbd4 : decode_any W_bcbd4 = Some (Auipc 10 81, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbd8 : bv 32 := 0x0a053023.
Lemma F_bcbd8 : fetch_word Ubsan.M.loaded_segments (0xbccd4 : word) = Some W_bcbd8.
Proof. vm_refl. Qed.
Lemma D_bcbd8 : decode_any W_bcbd8 = Some (Store SZ8 10 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbdc : bv 32 := 0x06013503.
Lemma F_bcbdc : fetch_word Ubsan.M.loaded_segments (0xbccd8 : word) = Some W_bcbdc.
Proof. vm_refl. Qed.
Lemma D_bcbdc : decode_any W_bcbdc = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbe0 : bv 32 := 0x02a93823.
Lemma F_bcbe0 : fetch_word Ubsan.M.loaded_segments (0xbccdc : word) = Some W_bcbe0.
Proof. vm_refl. Qed.
Lemma D_bcbe0 : decode_any W_bcbe0 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbe4 : bv 32 := 0x00041463.
Lemma F_bcbe4 : fetch_word Ubsan.M.loaded_segments (0xbcce0 : word) = Some W_bcbe4.
Proof. vm_refl. Qed.
Lemma D_bcbe4 : decode_any W_bcbe4 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbe8 : bv 32 := 0x12813403.
Lemma F_bcbe8 : fetch_word Ubsan.M.loaded_segments (0xbcce4 : word) = Some W_bcbe8.
Proof. vm_refl. Qed.
Lemma D_bcbe8 : decode_any W_bcbe8 = Some (Load SZ8 true 8 2 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbec : bv 32 := 0x00041663.
Lemma F_bcbec : fetch_word Ubsan.M.loaded_segments (0xbcce8 : word) = Some W_bcbec.
Proof. vm_refl. Qed.
Lemma D_bcbec : decode_any W_bcbec = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbf0 : bv 32 := 0xfff54517.
Lemma F_bcbf0 : fetch_word Ubsan.M.loaded_segments (0xbccec : word) = Some W_bcbf0.
Proof. vm_refl. Qed.
Lemma D_bcbf0 : decode_any W_bcbf0 = Some (Auipc 10 1048404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbf4 : bv 32 := 0xfef50413.
Lemma F_bcbf4 : fetch_word Ubsan.M.loaded_segments (0xbccf0 : word) = Some W_bcbf4.
Proof. vm_refl. Qed.
Lemma D_bcbf4 : decode_any W_bcbf4 = Some (OpImm ALU_ADD 8 10 4079, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbf8 : bv 32 := 0x0001d517.
Lemma F_bcbf8 : fetch_word Ubsan.M.loaded_segments (0xbccf4 : word) = Some W_bcbf8.
Proof. vm_refl. Qed.
Lemma D_bcbf8 : decode_any W_bcbf8 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcbfc : bv 32 := 0x35453583.
Lemma F_bcbfc : fetch_word Ubsan.M.loaded_segments (0xbccf8 : word) = Some W_bcbfc.
Proof. vm_refl. Qed.
Lemma D_bcbfc : decode_any W_bcbfc = Some (Load SZ8 true 11 10 852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcc00 : bv 32 := 0x0001d517.
Lemma F_bcc00 : fetch_word Ubsan.M.loaded_segments (0xbccfc : word) = Some W_bcc00.
Proof. vm_refl. Qed.
Lemma D_bcc00 : decode_any W_bcc00 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcc04 : bv 32 := 0x35453503.
Lemma F_bcc04 : fetch_word Ubsan.M.loaded_segments (0xbcd00 : word) = Some W_bcc04.
Proof. vm_refl. Qed.
Lemma D_bcc04 : decode_any W_bcc04 = Some (Load SZ8 true 10 10 852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcc08 : bv 32 := 0x0085b023.
Lemma F_bcc08 : fetch_word Ubsan.M.loaded_segments (0xbcd04 : word) = Some W_bcc08.
Proof. vm_refl. Qed.
Lemma D_bcc08 : decode_any W_bcc08 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcc0c : bv 32 := 0x00140593.
Lemma F_bcc0c : fetch_word Ubsan.M.loaded_segments (0xbcd08 : word) = Some W_bcc0c.
Proof. vm_refl. Qed.
Lemma D_bcc0c : decode_any W_bcc0c = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcc10 : bv 32 := 0x00853023.
Lemma F_bcc10 : fetch_word Ubsan.M.loaded_segments (0xbcd0c : word) = Some W_bcc10.
Proof. vm_refl. Qed.
Lemma D_bcc10 : decode_any W_bcc10 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcc14 : bv 32 := 0x02f00613.
Lemma F_bcc14 : fetch_word Ubsan.M.loaded_segments (0xbcd10 : word) = Some W_bcc14.
Proof. vm_refl. Qed.
Lemma D_bcc14 : decode_any W_bcc14 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcc18 : bv 32 := 0x00c0006f.
Lemma F_bcc18 : fetch_word Ubsan.M.loaded_segments (0xbcd14 : word) = Some W_bcc18.
Proof. vm_refl. Qed.
Lemma D_bcc18 : decode_any W_bcc18 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcc1c : bv 32 := 0x00b53023.
Lemma F_bcc1c : fetch_word Ubsan.M.loaded_segments (0xbcd18 : word) = Some W_bcc1c.
Proof. vm_refl. Qed.
Lemma D_bcc1c : decode_any W_bcc1c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcc20 : bv 32 := 0x00158593.
Lemma F_bcc20 : fetch_word Ubsan.M.loaded_segments (0xbcd1c : word) = Some W_bcc20.
Proof. vm_refl. Qed.
Lemma D_bcc20 : decode_any W_bcc20 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcc24 : bv 32 := 0xfff5c683.
Lemma F_bcc24 : fetch_word Ubsan.M.loaded_segments (0xbcd20 : word) = Some W_bcc24.
Proof. vm_refl. Qed.
Lemma D_bcc24 : decode_any W_bcc24 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcc28 : bv 32 := 0xfec68ae3.
Lemma F_bcc28 : fetch_word Ubsan.M.loaded_segments (0xbcd24 : word) = Some W_bcc28.
Proof. vm_refl. Qed.
Lemma D_bcc28 : decode_any W_bcc28 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcc2c : bv 32 := 0xfe069ae3.
Lemma F_bcc2c : fetch_word Ubsan.M.loaded_segments (0xbcd28 : word) = Some W_bcc2c.
Proof. vm_refl. Qed.
Lemma D_bcc2c : decode_any W_bcc2c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
