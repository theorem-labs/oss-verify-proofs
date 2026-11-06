(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Plain.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_1ed68 : bv 32 := 0x00008067.
Lemma F_1ed68 : fetch_word Plain.M.loaded_segments (0x1ee64 : word) = Some W_1ed68.
Proof. vm_refl. Qed.
Lemma D_1ed68 : decode_any W_1ed68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ed6c : bv 32 := 0xe8010113.
Lemma F_1ed6c : fetch_word Plain.M.loaded_segments (0x1ee68 : word) = Some W_1ed6c.
Proof. vm_refl. Qed.
Lemma D_1ed6c : decode_any W_1ed6c = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ed70 : bv 32 := 0x16113c23.
Lemma F_1ed70 : fetch_word Plain.M.loaded_segments (0x1ee6c : word) = Some W_1ed70.
Proof. vm_refl. Qed.
Lemma D_1ed70 : decode_any W_1ed70 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ed74 : bv 32 := 0x16813823.
Lemma F_1ed74 : fetch_word Plain.M.loaded_segments (0x1ee70 : word) = Some W_1ed74.
Proof. vm_refl. Qed.
Lemma D_1ed74 : decode_any W_1ed74 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ed78 : bv 32 := 0x16913423.
Lemma F_1ed78 : fetch_word Plain.M.loaded_segments (0x1ee74 : word) = Some W_1ed78.
Proof. vm_refl. Qed.
Lemma D_1ed78 : decode_any W_1ed78 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ed7c : bv 32 := 0x17213023.
Lemma F_1ed7c : fetch_word Plain.M.loaded_segments (0x1ee78 : word) = Some W_1ed7c.
Proof. vm_refl. Qed.
Lemma D_1ed7c : decode_any W_1ed7c = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ed80 : bv 32 := 0x00058413.
Lemma F_1ed80 : fetch_word Plain.M.loaded_segments (0x1ee7c : word) = Some W_1ed80.
Proof. vm_refl. Qed.
Lemma D_1ed80 : decode_any W_1ed80 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ed84 : bv 32 := 0x00050493.
Lemma F_1ed84 : fetch_word Plain.M.loaded_segments (0x1ee80 : word) = Some W_1ed84.
Proof. vm_refl. Qed.
Lemma D_1ed84 : decode_any W_1ed84 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ed88 : bv 32 := 0x03010513.
Lemma F_1ed88 : fetch_word Plain.M.loaded_segments (0x1ee84 : word) = Some W_1ed88.
Proof. vm_refl. Qed.
Lemma D_1ed88 : decode_any W_1ed88 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ed8c : bv 32 := 0x13000613.
Lemma F_1ed8c : fetch_word Plain.M.loaded_segments (0x1ee88 : word) = Some W_1ed8c.
Proof. vm_refl. Qed.
Lemma D_1ed8c : decode_any W_1ed8c = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ed90 : bv 32 := 0x00000593.
Lemma F_1ed90 : fetch_word Plain.M.loaded_segments (0x1ee8c : word) = Some W_1ed90.
Proof. vm_refl. Qed.
Lemma D_1ed90 : decode_any W_1ed90 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ed94 : bv 32 := 0x15c080ef.
Lemma F_1ed94 : fetch_word Plain.M.loaded_segments (0x1ee90 : word) = Some W_1ed94.
Proof. vm_refl. Qed.
Lemma D_1ed94 : decode_any W_1ed94 = Some (Jal 1 33116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ed98 : bv 32 := 0x00009517.
Lemma F_1ed98 : fetch_word Plain.M.loaded_segments (0x1ee94 : word) = Some W_1ed98.
Proof. vm_refl. Qed.
Lemma D_1ed98 : decode_any W_1ed98 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ed9c : bv 32 := 0x7bc53503.
Lemma F_1ed9c : fetch_word Plain.M.loaded_segments (0x1ee98 : word) = Some W_1ed9c.
Proof. vm_refl. Qed.
Lemma D_1ed9c : decode_any W_1ed9c = Some (Load SZ8 true 10 10 1980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1eda0 : bv 32 := 0x00953023.
Lemma F_1eda0 : fetch_word Plain.M.loaded_segments (0x1ee9c : word) = Some W_1eda0.
Proof. vm_refl. Qed.
Lemma D_1eda0 : decode_any W_1eda0 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1eda4 : bv 32 := 0x0004b503.
Lemma F_1eda4 : fetch_word Plain.M.loaded_segments (0x1eea0 : word) = Some W_1eda4.
Proof. vm_refl. Qed.
Lemma D_1eda4 : decode_any W_1eda4 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1eda8 : bv 32 := 0x00848493.
Lemma F_1eda8 : fetch_word Plain.M.loaded_segments (0x1eea4 : word) = Some W_1eda8.
Proof. vm_refl. Qed.
Lemma D_1eda8 : decode_any W_1eda8 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1edac : bv 32 := 0xfe051ce3.
Lemma F_1edac : fetch_word Plain.M.loaded_segments (0x1eea8 : word) = Some W_1edac.
Proof. vm_refl. Qed.
Lemma D_1edac : decode_any W_1edac = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1edb0 : bv 32 := 0x0003c517.
Lemma F_1edb0 : fetch_word Plain.M.loaded_segments (0x1eeac : word) = Some W_1edb0.
Proof. vm_refl. Qed.
Lemma D_1edb0 : decode_any W_1edb0 = Some (Auipc 10 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1edb4 : bv 32 := 0xac450913.
Lemma F_1edb4 : fetch_word Plain.M.loaded_segments (0x1eeb0 : word) = Some W_1edb4.
Proof. vm_refl. Qed.
Lemma D_1edb4 : decode_any W_1edb4 = Some (OpImm ALU_ADD 18 10 2756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1edb8 : bv 32 := 0x00993423.
Lemma F_1edb8 : fetch_word Plain.M.loaded_segments (0x1eeb4 : word) = Some W_1edb8.
Proof. vm_refl. Qed.
Lemma D_1edb8 : decode_any W_1edb8 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1edbc : bv 32 := 0x0004b583.
Lemma F_1edbc : fetch_word Plain.M.loaded_segments (0x1eeb8 : word) = Some W_1edbc.
Proof. vm_refl. Qed.
Lemma D_1edbc : decode_any W_1edbc = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1edc0 : bv 32 := 0x04058c63.
Lemma F_1edc0 : fetch_word Plain.M.loaded_segments (0x1eebc : word) = Some W_1edc0.
Proof. vm_refl. Qed.
Lemma D_1edc0 : decode_any W_1edc0 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1edc4 : bv 32 := 0x01048493.
Lemma F_1edc4 : fetch_word Plain.M.loaded_segments (0x1eec0 : word) = Some W_1edc4.
Proof. vm_refl. Qed.
Lemma D_1edc4 : decode_any W_1edc4 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1edc8 : bv 32 := 0x02500513.
Lemma F_1edc8 : fetch_word Plain.M.loaded_segments (0x1eec4 : word) = Some W_1edc8.
Proof. vm_refl. Qed.
Lemma D_1edc8 : decode_any W_1edc8 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1edcc : bv 32 := 0x03010613.
Lemma F_1edcc : fetch_word Plain.M.loaded_segments (0x1eec8 : word) = Some W_1edcc.
Proof. vm_refl. Qed.
Lemma D_1edcc : decode_any W_1edcc = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1edd0 : bv 32 := 0x0100006f.
Lemma F_1edd0 : fetch_word Plain.M.loaded_segments (0x1eecc : word) = Some W_1edd0.
Proof. vm_refl. Qed.
Lemma D_1edd0 : decode_any W_1edd0 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1edd4 : bv 32 := 0x0004b583.
Lemma F_1edd4 : fetch_word Plain.M.loaded_segments (0x1eed0 : word) = Some W_1edd4.
Proof. vm_refl. Qed.
Lemma D_1edd4 : decode_any W_1edd4 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1edd8 : bv 32 := 0x01048493.
Lemma F_1edd8 : fetch_word Plain.M.loaded_segments (0x1eed4 : word) = Some W_1edd8.
Proof. vm_refl. Qed.
Lemma D_1edd8 : decode_any W_1edd8 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1eddc : bv 32 := 0x00058e63.
Lemma F_1eddc : fetch_word Plain.M.loaded_segments (0x1eed8 : word) = Some W_1eddc.
Proof. vm_refl. Qed.
Lemma D_1eddc : decode_any W_1eddc = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ede0 : bv 32 := 0xfeb56ae3.
Lemma F_1ede0 : fetch_word Plain.M.loaded_segments (0x1eedc : word) = Some W_1ede0.
Proof. vm_refl. Qed.
Lemma D_1ede0 : decode_any W_1ede0 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ede4 : bv 32 := 0xff84b683.
Lemma F_1ede4 : fetch_word Plain.M.loaded_segments (0x1eee0 : word) = Some W_1ede4.
Proof. vm_refl. Qed.
Lemma D_1ede4 : decode_any W_1ede4 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ede8 : bv 32 := 0x00359593.
Lemma F_1ede8 : fetch_word Plain.M.loaded_segments (0x1eee4 : word) = Some W_1ede8.
Proof. vm_refl. Qed.
Lemma D_1ede8 : decode_any W_1ede8 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1edec : bv 32 := 0x00b605b3.
Lemma F_1edec : fetch_word Plain.M.loaded_segments (0x1eee8 : word) = Some W_1edec.
Proof. vm_refl. Qed.
Lemma D_1edec : decode_any W_1edec = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1edf0 : bv 32 := 0x00d5b023.
Lemma F_1edf0 : fetch_word Plain.M.loaded_segments (0x1eeec : word) = Some W_1edf0.
Proof. vm_refl. Qed.
Lemma D_1edf0 : decode_any W_1edf0 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1edf4 : bv 32 := 0xfe1ff06f.
Lemma F_1edf4 : fetch_word Plain.M.loaded_segments (0x1eef0 : word) = Some W_1edf4.
Proof. vm_refl. Qed.
Lemma D_1edf4 : decode_any W_1edf4 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1edf8 : bv 32 := 0x0b013583.
Lemma F_1edf8 : fetch_word Plain.M.loaded_segments (0x1eef4 : word) = Some W_1edf8.
Proof. vm_refl. Qed.
Lemma D_1edf8 : decode_any W_1edf8 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1edfc : bv 32 := 0x13013503.
Lemma F_1edfc : fetch_word Plain.M.loaded_segments (0x1eef8 : word) = Some W_1edfc.
Proof. vm_refl. Qed.
Lemma D_1edfc : decode_any W_1edfc = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee00 : bv 32 := 0x0003c617.
Lemma F_1ee00 : fetch_word Plain.M.loaded_segments (0x1eefc : word) = Some W_1ee00.
Proof. vm_refl. Qed.
Lemma D_1ee00 : decode_any W_1ee00 = Some (Auipc 12 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee04 : bv 32 := 0xacb63e23.
Lemma F_1ee04 : fetch_word Plain.M.loaded_segments (0x1ef00 : word) = Some W_1ee04.
Proof. vm_refl. Qed.
Lemma D_1ee04 : decode_any W_1ee04 = Some (Store SZ8 12 11 2780, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee08 : bv 32 := 0x00050c63.
Lemma F_1ee08 : fetch_word Plain.M.loaded_segments (0x1ef04 : word) = Some W_1ee08.
Proof. vm_refl. Qed.
Lemma D_1ee08 : decode_any W_1ee08 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee20 : bv 32 := 0x06013503.
Lemma F_1ee20 : fetch_word Plain.M.loaded_segments (0x1ef1c : word) = Some W_1ee20.
Proof. vm_refl. Qed.
Lemma D_1ee20 : decode_any W_1ee20 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee24 : bv 32 := 0x02a93823.
Lemma F_1ee24 : fetch_word Plain.M.loaded_segments (0x1ef20 : word) = Some W_1ee24.
Proof. vm_refl. Qed.
Lemma D_1ee24 : decode_any W_1ee24 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee28 : bv 32 := 0x00041463.
Lemma F_1ee28 : fetch_word Plain.M.loaded_segments (0x1ef24 : word) = Some W_1ee28.
Proof. vm_refl. Qed.
Lemma D_1ee28 : decode_any W_1ee28 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee30 : bv 32 := 0x00041663.
Lemma F_1ee30 : fetch_word Plain.M.loaded_segments (0x1ef2c : word) = Some W_1ee30.
Proof. vm_refl. Qed.
Lemma D_1ee30 : decode_any W_1ee30 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee3c : bv 32 := 0x00009517.
Lemma F_1ee3c : fetch_word Plain.M.loaded_segments (0x1ef38 : word) = Some W_1ee3c.
Proof. vm_refl. Qed.
Lemma D_1ee3c : decode_any W_1ee3c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee40 : bv 32 := 0x72053583.
Lemma F_1ee40 : fetch_word Plain.M.loaded_segments (0x1ef3c : word) = Some W_1ee40.
Proof. vm_refl. Qed.
Lemma D_1ee40 : decode_any W_1ee40 = Some (Load SZ8 true 11 10 1824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee44 : bv 32 := 0x00009517.
Lemma F_1ee44 : fetch_word Plain.M.loaded_segments (0x1ef40 : word) = Some W_1ee44.
Proof. vm_refl. Qed.
Lemma D_1ee44 : decode_any W_1ee44 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee48 : bv 32 := 0x72053503.
Lemma F_1ee48 : fetch_word Plain.M.loaded_segments (0x1ef44 : word) = Some W_1ee48.
Proof. vm_refl. Qed.
Lemma D_1ee48 : decode_any W_1ee48 = Some (Load SZ8 true 10 10 1824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee4c : bv 32 := 0x0085b023.
Lemma F_1ee4c : fetch_word Plain.M.loaded_segments (0x1ef48 : word) = Some W_1ee4c.
Proof. vm_refl. Qed.
Lemma D_1ee4c : decode_any W_1ee4c = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee50 : bv 32 := 0x00140593.
Lemma F_1ee50 : fetch_word Plain.M.loaded_segments (0x1ef4c : word) = Some W_1ee50.
Proof. vm_refl. Qed.
Lemma D_1ee50 : decode_any W_1ee50 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee54 : bv 32 := 0x00853023.
Lemma F_1ee54 : fetch_word Plain.M.loaded_segments (0x1ef50 : word) = Some W_1ee54.
Proof. vm_refl. Qed.
Lemma D_1ee54 : decode_any W_1ee54 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee58 : bv 32 := 0x02f00613.
Lemma F_1ee58 : fetch_word Plain.M.loaded_segments (0x1ef54 : word) = Some W_1ee58.
Proof. vm_refl. Qed.
Lemma D_1ee58 : decode_any W_1ee58 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee5c : bv 32 := 0x00c0006f.
Lemma F_1ee5c : fetch_word Plain.M.loaded_segments (0x1ef58 : word) = Some W_1ee5c.
Proof. vm_refl. Qed.
Lemma D_1ee5c : decode_any W_1ee5c = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee60 : bv 32 := 0x00b53023.
Lemma F_1ee60 : fetch_word Plain.M.loaded_segments (0x1ef5c : word) = Some W_1ee60.
Proof. vm_refl. Qed.
Lemma D_1ee60 : decode_any W_1ee60 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee64 : bv 32 := 0x00158593.
Lemma F_1ee64 : fetch_word Plain.M.loaded_segments (0x1ef60 : word) = Some W_1ee64.
Proof. vm_refl. Qed.
Lemma D_1ee64 : decode_any W_1ee64 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee68 : bv 32 := 0xfff5c683.
Lemma F_1ee68 : fetch_word Plain.M.loaded_segments (0x1ef64 : word) = Some W_1ee68.
Proof. vm_refl. Qed.
Lemma D_1ee68 : decode_any W_1ee68 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee6c : bv 32 := 0xfec68ae3.
Lemma F_1ee6c : fetch_word Plain.M.loaded_segments (0x1ef68 : word) = Some W_1ee6c.
Proof. vm_refl. Qed.
Lemma D_1ee6c : decode_any W_1ee6c = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee70 : bv 32 := 0xfe069ae3.
Lemma F_1ee70 : fetch_word Plain.M.loaded_segments (0x1ef6c : word) = Some W_1ee70.
Proof. vm_refl. Qed.
Lemma D_1ee70 : decode_any W_1ee70 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee74 : bv 32 := 0x03010513.
Lemma F_1ee74 : fetch_word Plain.M.loaded_segments (0x1ef70 : word) = Some W_1ee74.
Proof. vm_refl. Qed.
Lemma D_1ee74 : decode_any W_1ee74 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee78 : bv 32 := 0x214000ef.
Lemma F_1ee78 : fetch_word Plain.M.loaded_segments (0x1ef74 : word) = Some W_1ee78.
Proof. vm_refl. Qed.
Lemma D_1ee78 : decode_any W_1ee78 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee7c : bv 32 := 0x0f813503.
Lemma F_1ee7c : fetch_word Plain.M.loaded_segments (0x1ef78 : word) = Some W_1ee7c.
Proof. vm_refl. Qed.
Lemma D_1ee7c : decode_any W_1ee7c = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee80 : bv 32 := 0x0d9000ef.
Lemma F_1ee80 : fetch_word Plain.M.loaded_segments (0x1ef7c : word) = Some W_1ee80.
Proof. vm_refl. Qed.
Lemma D_1ee80 : decode_any W_1ee80 = Some (Jal 1 2264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee84 : bv 32 := 0x08813503.
Lemma F_1ee84 : fetch_word Plain.M.loaded_segments (0x1ef80 : word) = Some W_1ee84.
Proof. vm_refl. Qed.
Lemma D_1ee84 : decode_any W_1ee84 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee88 : bv 32 := 0x09013583.
Lemma F_1ee88 : fetch_word Plain.M.loaded_segments (0x1ef84 : word) = Some W_1ee88.
Proof. vm_refl. Qed.
Lemma D_1ee88 : decode_any W_1ee88 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee8c : bv 32 := 0x00b51c63.
Lemma F_1ee8c : fetch_word Plain.M.loaded_segments (0x1ef88 : word) = Some W_1ee8c.
Proof. vm_refl. Qed.
Lemma D_1ee8c : decode_any W_1ee8c = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee90 : bv 32 := 0x09813503.
Lemma F_1ee90 : fetch_word Plain.M.loaded_segments (0x1ef8c : word) = Some W_1ee90.
Proof. vm_refl. Qed.
Lemma D_1ee90 : decode_any W_1ee90 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee94 : bv 32 := 0x0a013583.
Lemma F_1ee94 : fetch_word Plain.M.loaded_segments (0x1ef90 : word) = Some W_1ee94.
Proof. vm_refl. Qed.
Lemma D_1ee94 : decode_any W_1ee94 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee98 : bv 32 := 0x00b51663.
Lemma F_1ee98 : fetch_word Plain.M.loaded_segments (0x1ef94 : word) = Some W_1ee98.
Proof. vm_refl. Qed.
Lemma D_1ee98 : decode_any W_1ee98 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ee9c : bv 32 := 0x0e813503.
Lemma F_1ee9c : fetch_word Plain.M.loaded_segments (0x1ef98 : word) = Some W_1ee9c.
Proof. vm_refl. Qed.
Lemma D_1ee9c : decode_any W_1ee9c = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1eea0 : bv 32 := 0x0e050063.
Lemma F_1eea0 : fetch_word Plain.M.loaded_segments (0x1ef9c : word) = Some W_1eea0.
Proof. vm_refl. Qed.
Lemma D_1eea0 : decode_any W_1eea0 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ef80 : bv 32 := 0x17813083.
Lemma F_1ef80 : fetch_word Plain.M.loaded_segments (0x1f07c : word) = Some W_1ef80.
Proof. vm_refl. Qed.
Lemma D_1ef80 : decode_any W_1ef80 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ef84 : bv 32 := 0x17013403.
Lemma F_1ef84 : fetch_word Plain.M.loaded_segments (0x1f080 : word) = Some W_1ef84.
Proof. vm_refl. Qed.
Lemma D_1ef84 : decode_any W_1ef84 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ef88 : bv 32 := 0x16813483.
Lemma F_1ef88 : fetch_word Plain.M.loaded_segments (0x1f084 : word) = Some W_1ef88.
Proof. vm_refl. Qed.
Lemma D_1ef88 : decode_any W_1ef88 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ef8c : bv 32 := 0x16013903.
Lemma F_1ef8c : fetch_word Plain.M.loaded_segments (0x1f088 : word) = Some W_1ef8c.
Proof. vm_refl. Qed.
Lemma D_1ef8c : decode_any W_1ef8c = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ef90 : bv 32 := 0x18010113.
Lemma F_1ef90 : fetch_word Plain.M.loaded_segments (0x1f08c : word) = Some W_1ef90.
Proof. vm_refl. Qed.
Lemma D_1ef90 : decode_any W_1ef90 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ef94 : bv 32 := 0x00008067.
Lemma F_1ef94 : fetch_word Plain.M.loaded_segments (0x1f090 : word) = Some W_1ef94.
Proof. vm_refl. Qed.
Lemma D_1ef94 : decode_any W_1ef94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ef98 : bv 32 := 0xfe010113.
Lemma F_1ef98 : fetch_word Plain.M.loaded_segments (0x1f094 : word) = Some W_1ef98.
Proof. vm_refl. Qed.
Lemma D_1ef98 : decode_any W_1ef98 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ef9c : bv 32 := 0x00113c23.
Lemma F_1ef9c : fetch_word Plain.M.loaded_segments (0x1f098 : word) = Some W_1ef9c.
Proof. vm_refl. Qed.
Lemma D_1ef9c : decode_any W_1ef9c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efa0 : bv 32 := 0x00813823.
Lemma F_1efa0 : fetch_word Plain.M.loaded_segments (0x1f09c : word) = Some W_1efa0.
Proof. vm_refl. Qed.
Lemma D_1efa0 : decode_any W_1efa0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efa4 : bv 32 := 0x00913423.
Lemma F_1efa4 : fetch_word Plain.M.loaded_segments (0x1f0a0 : word) = Some W_1efa4.
Proof. vm_refl. Qed.
Lemma D_1efa4 : decode_any W_1efa4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efa8 : bv 32 := 0xdc1ff0ef.
Lemma F_1efa8 : fetch_word Plain.M.loaded_segments (0x1f0a4 : word) = Some W_1efa8.
Proof. vm_refl. Qed.
Lemma D_1efa8 : decode_any W_1efa8 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efac : bv 32 := 0x00009517.
Lemma F_1efac : fetch_word Plain.M.loaded_segments (0x1f0a8 : word) = Some W_1efac.
Proof. vm_refl. Qed.
Lemma D_1efac : decode_any W_1efac = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efb0 : bv 32 := 0x00009597.
Lemma F_1efb0 : fetch_word Plain.M.loaded_segments (0x1f0ac : word) = Some W_1efb0.
Proof. vm_refl. Qed.
Lemma D_1efb0 : decode_any W_1efb0 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efb4 : bv 32 := 0x5c053403.
Lemma F_1efb4 : fetch_word Plain.M.loaded_segments (0x1f0b0 : word) = Some W_1efb4.
Proof. vm_refl. Qed.
Lemma D_1efb4 : decode_any W_1efb4 = Some (Load SZ8 true 8 10 1472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efb8 : bv 32 := 0x5c45b483.
Lemma F_1efb8 : fetch_word Plain.M.loaded_segments (0x1f0b4 : word) = Some W_1efb8.
Proof. vm_refl. Qed.
Lemma D_1efb8 : decode_any W_1efb8 = Some (Load SZ8 true 9 11 1476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efbc : bv 32 := 0x0084fa63.
Lemma F_1efbc : fetch_word Plain.M.loaded_segments (0x1f0b8 : word) = Some W_1efbc.
Proof. vm_refl. Qed.
Lemma D_1efbc : decode_any W_1efbc = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efc0 : bv 32 := 0x0004b503.
Lemma F_1efc0 : fetch_word Plain.M.loaded_segments (0x1f0bc : word) = Some W_1efc0.
Proof. vm_refl. Qed.
Lemma D_1efc0 : decode_any W_1efc0 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efc4 : bv 32 := 0x000500e7.
Lemma F_1efc4 : fetch_word Plain.M.loaded_segments (0x1f0c0 : word) = Some W_1efc4.
Proof. vm_refl. Qed.
Lemma D_1efc4 : decode_any W_1efc4 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efc8 : bv 32 := 0x00848493.
Lemma F_1efc8 : fetch_word Plain.M.loaded_segments (0x1f0c4 : word) = Some W_1efc8.
Proof. vm_refl. Qed.
Lemma D_1efc8 : decode_any W_1efc8 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efcc : bv 32 := 0xfe84eae3.
Lemma F_1efcc : fetch_word Plain.M.loaded_segments (0x1f0c8 : word) = Some W_1efcc.
Proof. vm_refl. Qed.
Lemma D_1efcc : decode_any W_1efcc = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efd0 : bv 32 := 0x01813083.
Lemma F_1efd0 : fetch_word Plain.M.loaded_segments (0x1f0cc : word) = Some W_1efd0.
Proof. vm_refl. Qed.
Lemma D_1efd0 : decode_any W_1efd0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efd4 : bv 32 := 0x01013403.
Lemma F_1efd4 : fetch_word Plain.M.loaded_segments (0x1f0d0 : word) = Some W_1efd4.
Proof. vm_refl. Qed.
Lemma D_1efd4 : decode_any W_1efd4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efd8 : bv 32 := 0x00813483.
Lemma F_1efd8 : fetch_word Plain.M.loaded_segments (0x1f0d4 : word) = Some W_1efd8.
Proof. vm_refl. Qed.
Lemma D_1efd8 : decode_any W_1efd8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efdc : bv 32 := 0x02010113.
Lemma F_1efdc : fetch_word Plain.M.loaded_segments (0x1f0d8 : word) = Some W_1efdc.
Proof. vm_refl. Qed.
Lemma D_1efdc : decode_any W_1efdc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efe0 : bv 32 := 0x00008067.
Lemma F_1efe0 : fetch_word Plain.M.loaded_segments (0x1f0dc : word) = Some W_1efe0.
Proof. vm_refl. Qed.
Lemma D_1efe0 : decode_any W_1efe0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efe4 : bv 32 := 0xfe010113.
Lemma F_1efe4 : fetch_word Plain.M.loaded_segments (0x1f0e0 : word) = Some W_1efe4.
Proof. vm_refl. Qed.
Lemma D_1efe4 : decode_any W_1efe4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efe8 : bv 32 := 0x00113c23.
Lemma F_1efe8 : fetch_word Plain.M.loaded_segments (0x1f0e4 : word) = Some W_1efe8.
Proof. vm_refl. Qed.
Lemma D_1efe8 : decode_any W_1efe8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1efec : bv 32 := 0x00813823.
Lemma F_1efec : fetch_word Plain.M.loaded_segments (0x1f0e8 : word) = Some W_1efec.
Proof. vm_refl. Qed.
Lemma D_1efec : decode_any W_1efec = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1eff0 : bv 32 := 0x00913423.
Lemma F_1eff0 : fetch_word Plain.M.loaded_segments (0x1f0ec : word) = Some W_1eff0.
Proof. vm_refl. Qed.
Lemma D_1eff0 : decode_any W_1eff0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1eff4 : bv 32 := 0x01213023.
Lemma F_1eff4 : fetch_word Plain.M.loaded_segments (0x1f0f0 : word) = Some W_1eff4.
Proof. vm_refl. Qed.
Lemma D_1eff4 : decode_any W_1eff4 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1eff8 : bv 32 := 0x00060413.
Lemma F_1eff8 : fetch_word Plain.M.loaded_segments (0x1f0f4 : word) = Some W_1eff8.
Proof. vm_refl. Qed.
Lemma D_1eff8 : decode_any W_1eff8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1effc : bv 32 := 0x00058493.
Lemma F_1effc : fetch_word Plain.M.loaded_segments (0x1f0f8 : word) = Some W_1effc.
Proof. vm_refl. Qed.
Lemma D_1effc : decode_any W_1effc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f000 : bv 32 := 0x00050913.
Lemma F_1f000 : fetch_word Plain.M.loaded_segments (0x1f0fc : word) = Some W_1f000.
Proof. vm_refl. Qed.
Lemma D_1f000 : decode_any W_1f000 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f004 : bv 32 := 0x00063583.
Lemma F_1f004 : fetch_word Plain.M.loaded_segments (0x1f100 : word) = Some W_1f004.
Proof. vm_refl. Qed.
Lemma D_1f004 : decode_any W_1f004 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f008 : bv 32 := 0x00349513.
Lemma F_1f008 : fetch_word Plain.M.loaded_segments (0x1f104 : word) = Some W_1f008.
Proof. vm_refl. Qed.
Lemma D_1f008 : decode_any W_1f008 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f00c : bv 32 := 0x00a60533.
Lemma F_1f00c : fetch_word Plain.M.loaded_segments (0x1f108 : word) = Some W_1f00c.
Proof. vm_refl. Qed.
Lemma D_1f00c : decode_any W_1f00c = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f010 : bv 32 := 0x00850513.
Lemma F_1f010 : fetch_word Plain.M.loaded_segments (0x1f10c : word) = Some W_1f010.
Proof. vm_refl. Qed.
Lemma D_1f010 : decode_any W_1f010 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f014 : bv 32 := 0xd59ff0ef.
Lemma F_1f014 : fetch_word Plain.M.loaded_segments (0x1f110 : word) = Some W_1f014.
Proof. vm_refl. Qed.
Lemma D_1f014 : decode_any W_1f014 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f018 : bv 32 := 0x00000517.
Lemma F_1f018 : fetch_word Plain.M.loaded_segments (0x1f114 : word) = Some W_1f018.
Proof. vm_refl. Qed.
Lemma D_1f018 : decode_any W_1f018 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f01c : bv 32 := 0x02c50313.
Lemma F_1f01c : fetch_word Plain.M.loaded_segments (0x1f118 : word) = Some W_1f01c.
Proof. vm_refl. Qed.
Lemma D_1f01c : decode_any W_1f01c = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f020 : bv 32 := 0x00090513.
Lemma F_1f020 : fetch_word Plain.M.loaded_segments (0x1f11c : word) = Some W_1f020.
Proof. vm_refl. Qed.
Lemma D_1f020 : decode_any W_1f020 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f024 : bv 32 := 0x00048593.
Lemma F_1f024 : fetch_word Plain.M.loaded_segments (0x1f120 : word) = Some W_1f024.
Proof. vm_refl. Qed.
Lemma D_1f024 : decode_any W_1f024 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f028 : bv 32 := 0x00040613.
Lemma F_1f028 : fetch_word Plain.M.loaded_segments (0x1f124 : word) = Some W_1f028.
Proof. vm_refl. Qed.
Lemma D_1f028 : decode_any W_1f028 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f02c : bv 32 := 0x01813083.
Lemma F_1f02c : fetch_word Plain.M.loaded_segments (0x1f128 : word) = Some W_1f02c.
Proof. vm_refl. Qed.
Lemma D_1f02c : decode_any W_1f02c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f030 : bv 32 := 0x01013403.
Lemma F_1f030 : fetch_word Plain.M.loaded_segments (0x1f12c : word) = Some W_1f030.
Proof. vm_refl. Qed.
Lemma D_1f030 : decode_any W_1f030 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f034 : bv 32 := 0x00813483.
Lemma F_1f034 : fetch_word Plain.M.loaded_segments (0x1f130 : word) = Some W_1f034.
Proof. vm_refl. Qed.
Lemma D_1f034 : decode_any W_1f034 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f038 : bv 32 := 0x00013903.
Lemma F_1f038 : fetch_word Plain.M.loaded_segments (0x1f134 : word) = Some W_1f038.
Proof. vm_refl. Qed.
Lemma D_1f038 : decode_any W_1f038 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f03c : bv 32 := 0x02010113.
Lemma F_1f03c : fetch_word Plain.M.loaded_segments (0x1f138 : word) = Some W_1f03c.
Proof. vm_refl. Qed.
Lemma D_1f03c : decode_any W_1f03c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f040 : bv 32 := 0x00030067.
Lemma F_1f040 : fetch_word Plain.M.loaded_segments (0x1f13c : word) = Some W_1f040.
Proof. vm_refl. Qed.
Lemma D_1f040 : decode_any W_1f040 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f044 : bv 32 := 0xfd010113.
Lemma F_1f044 : fetch_word Plain.M.loaded_segments (0x1f140 : word) = Some W_1f044.
Proof. vm_refl. Qed.
Lemma D_1f044 : decode_any W_1f044 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f048 : bv 32 := 0x02113423.
Lemma F_1f048 : fetch_word Plain.M.loaded_segments (0x1f144 : word) = Some W_1f048.
Proof. vm_refl. Qed.
Lemma D_1f048 : decode_any W_1f048 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f04c : bv 32 := 0x02813023.
Lemma F_1f04c : fetch_word Plain.M.loaded_segments (0x1f148 : word) = Some W_1f04c.
Proof. vm_refl. Qed.
Lemma D_1f04c : decode_any W_1f04c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f050 : bv 32 := 0x00913c23.
Lemma F_1f050 : fetch_word Plain.M.loaded_segments (0x1f14c : word) = Some W_1f050.
Proof. vm_refl. Qed.
Lemma D_1f050 : decode_any W_1f050 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f054 : bv 32 := 0x01213823.
Lemma F_1f054 : fetch_word Plain.M.loaded_segments (0x1f150 : word) = Some W_1f054.
Proof. vm_refl. Qed.
Lemma D_1f054 : decode_any W_1f054 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f058 : bv 32 := 0x01313423.
Lemma F_1f058 : fetch_word Plain.M.loaded_segments (0x1f154 : word) = Some W_1f058.
Proof. vm_refl. Qed.
Lemma D_1f058 : decode_any W_1f058 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f05c : bv 32 := 0x00060413.
Lemma F_1f05c : fetch_word Plain.M.loaded_segments (0x1f158 : word) = Some W_1f05c.
Proof. vm_refl. Qed.
Lemma D_1f05c : decode_any W_1f05c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f060 : bv 32 := 0x00058493.
Lemma F_1f060 : fetch_word Plain.M.loaded_segments (0x1f15c : word) = Some W_1f060.
Proof. vm_refl. Qed.
Lemma D_1f060 : decode_any W_1f060 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f064 : bv 32 := 0x00050913.
Lemma F_1f064 : fetch_word Plain.M.loaded_segments (0x1f160 : word) = Some W_1f064.
Proof. vm_refl. Qed.
Lemma D_1f064 : decode_any W_1f064 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f068 : bv 32 := 0x00359513.
Lemma F_1f068 : fetch_word Plain.M.loaded_segments (0x1f164 : word) = Some W_1f068.
Proof. vm_refl. Qed.
Lemma D_1f068 : decode_any W_1f068 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f06c : bv 32 := 0x00a60533.
Lemma F_1f06c : fetch_word Plain.M.loaded_segments (0x1f168 : word) = Some W_1f06c.
Proof. vm_refl. Qed.
Lemma D_1f06c : decode_any W_1f06c = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f070 : bv 32 := 0x00850993.
Lemma F_1f070 : fetch_word Plain.M.loaded_segments (0x1f16c : word) = Some W_1f070.
Proof. vm_refl. Qed.
Lemma D_1f070 : decode_any W_1f070 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f074 : bv 32 := 0xf25ff0ef.
Lemma F_1f074 : fetch_word Plain.M.loaded_segments (0x1f170 : word) = Some W_1f074.
Proof. vm_refl. Qed.
Lemma D_1f074 : decode_any W_1f074 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f078 : bv 32 := 0x00048513.
Lemma F_1f078 : fetch_word Plain.M.loaded_segments (0x1f174 : word) = Some W_1f078.
Proof. vm_refl. Qed.
Lemma D_1f078 : decode_any W_1f078 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f07c : bv 32 := 0x00040593.
Lemma F_1f07c : fetch_word Plain.M.loaded_segments (0x1f178 : word) = Some W_1f07c.
Proof. vm_refl. Qed.
Lemma D_1f07c : decode_any W_1f07c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f080 : bv 32 := 0x00098613.
Lemma F_1f080 : fetch_word Plain.M.loaded_segments (0x1f17c : word) = Some W_1f080.
Proof. vm_refl. Qed.
Lemma D_1f080 : decode_any W_1f080 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f084 : bv 32 := 0x000900e7.
Lemma F_1f084 : fetch_word Plain.M.loaded_segments (0x1f180 : word) = Some W_1f084.
Proof. vm_refl. Qed.
Lemma D_1f084 : decode_any W_1f084 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_1f40c : bv 32 := 0x00050593.
Lemma F_1f40c : fetch_word Plain.M.loaded_segments (0x1f4fc : word) = Some W_1f40c.
Proof. vm_refl. Qed.
Lemma D_1f40c : decode_any W_1f40c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f410 : bv 32 := 0x05e00893.
Lemma F_1f410 : fetch_word Plain.M.loaded_segments (0x1f500 : word) = Some W_1f410.
Proof. vm_refl. Qed.
Lemma D_1f410 : decode_any W_1f410 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f414 : bv 32 := 0x00000073.
Lemma F_1f414 : fetch_word Plain.M.loaded_segments (0x1f504 : word) = Some W_1f414.
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma E_1f414 : is_ecall W_1f414 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_1f428 : bv 32 := 0x00008067.
Lemma F_1f428 : fetch_word Plain.M.loaded_segments (0x1f6ac : word) = Some W_1f428.
Proof. vm_refl. Qed.
Lemma D_1f428 : decode_any W_1f428 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f42c : bv 32 := 0xfe010113.
Lemma F_1f42c : fetch_word Plain.M.loaded_segments (0x1f6b0 : word) = Some W_1f42c.
Proof. vm_refl. Qed.
Lemma D_1f42c : decode_any W_1f42c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f430 : bv 32 := 0x00113c23.
Lemma F_1f430 : fetch_word Plain.M.loaded_segments (0x1f6b4 : word) = Some W_1f430.
Proof. vm_refl. Qed.
Lemma D_1f430 : decode_any W_1f430 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f434 : bv 32 := 0x00813823.
Lemma F_1f434 : fetch_word Plain.M.loaded_segments (0x1f6b8 : word) = Some W_1f434.
Proof. vm_refl. Qed.
Lemma D_1f434 : decode_any W_1f434 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f438 : bv 32 := 0x00913423.
Lemma F_1f438 : fetch_word Plain.M.loaded_segments (0x1f6bc : word) = Some W_1f438.
Proof. vm_refl. Qed.
Lemma D_1f438 : decode_any W_1f438 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f43c : bv 32 := 0x00009517.
Lemma F_1f43c : fetch_word Plain.M.loaded_segments (0x1f6c0 : word) = Some W_1f43c.
Proof. vm_refl. Qed.
Lemma D_1f43c : decode_any W_1f43c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f440 : bv 32 := 0x00009597.
Lemma F_1f440 : fetch_word Plain.M.loaded_segments (0x1f6c4 : word) = Some W_1f440.
Proof. vm_refl. Qed.
Lemma D_1f440 : decode_any W_1f440 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f444 : bv 32 := 0xfc053503.
Lemma F_1f444 : fetch_word Plain.M.loaded_segments (0x1f6c8 : word) = Some W_1f444.
Proof. vm_refl. Qed.
Lemma D_1f444 : decode_any W_1f444 = Some (Load SZ8 true 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f448 : bv 32 := 0xfc45b403.
Lemma F_1f448 : fetch_word Plain.M.loaded_segments (0x1f6cc : word) = Some W_1f448.
Proof. vm_refl. Qed.
Lemma D_1f448 : decode_any W_1f448 = Some (Load SZ8 true 8 11 4036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f44c : bv 32 := 0x00a47c63.
Lemma F_1f44c : fetch_word Plain.M.loaded_segments (0x1f6d0 : word) = Some W_1f44c.
Proof. vm_refl. Qed.
Lemma D_1f44c : decode_any W_1f44c = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f450 : bv 32 := 0xff853583.
Lemma F_1f450 : fetch_word Plain.M.loaded_segments (0x1f6d4 : word) = Some W_1f450.
Proof. vm_refl. Qed.
Lemma D_1f450 : decode_any W_1f450 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f454 : bv 32 := 0xff850493.
Lemma F_1f454 : fetch_word Plain.M.loaded_segments (0x1f6d8 : word) = Some W_1f454.
Proof. vm_refl. Qed.
Lemma D_1f454 : decode_any W_1f454 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f458 : bv 32 := 0x000580e7.
Lemma F_1f458 : fetch_word Plain.M.loaded_segments (0x1f6dc : word) = Some W_1f458.
Proof. vm_refl. Qed.
Lemma D_1f458 : decode_any W_1f458 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f45c : bv 32 := 0x00048513.
Lemma F_1f45c : fetch_word Plain.M.loaded_segments (0x1f6e0 : word) = Some W_1f45c.
Proof. vm_refl. Qed.
Lemma D_1f45c : decode_any W_1f45c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f460 : bv 32 := 0xfe9468e3.
Lemma F_1f460 : fetch_word Plain.M.loaded_segments (0x1f6e4 : word) = Some W_1f460.
Proof. vm_refl. Qed.
Lemma D_1f460 : decode_any W_1f460 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f464 : bv 32 := 0x01813083.
Lemma F_1f464 : fetch_word Plain.M.loaded_segments (0x1f6e8 : word) = Some W_1f464.
Proof. vm_refl. Qed.
Lemma D_1f464 : decode_any W_1f464 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f468 : bv 32 := 0x01013403.
Lemma F_1f468 : fetch_word Plain.M.loaded_segments (0x1f6ec : word) = Some W_1f468.
Proof. vm_refl. Qed.
Lemma D_1f468 : decode_any W_1f468 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f46c : bv 32 := 0x00813483.
Lemma F_1f46c : fetch_word Plain.M.loaded_segments (0x1f6f0 : word) = Some W_1f46c.
Proof. vm_refl. Qed.
Lemma D_1f46c : decode_any W_1f46c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f470 : bv 32 := 0x02010113.
Lemma F_1f470 : fetch_word Plain.M.loaded_segments (0x1f6f4 : word) = Some W_1f470.
Proof. vm_refl. Qed.
Lemma D_1f470 : decode_any W_1f470 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f474 : bv 32 := 0xfb5ff06f.
Lemma F_1f474 : fetch_word Plain.M.loaded_segments (0x1f6f8 : word) = Some W_1f474.
Proof. vm_refl. Qed.
Lemma D_1f474 : decode_any W_1f474 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f478 : bv 32 := 0xff010113.
Lemma F_1f478 : fetch_word Plain.M.loaded_segments (0x1f6fc : word) = Some W_1f478.
Proof. vm_refl. Qed.
Lemma D_1f478 : decode_any W_1f478 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f47c : bv 32 := 0x00113423.
Lemma F_1f47c : fetch_word Plain.M.loaded_segments (0x1f700 : word) = Some W_1f47c.
Proof. vm_refl. Qed.
Lemma D_1f47c : decode_any W_1f47c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f480 : bv 32 := 0x00813023.
Lemma F_1f480 : fetch_word Plain.M.loaded_segments (0x1f704 : word) = Some W_1f480.
Proof. vm_refl. Qed.
Lemma D_1f480 : decode_any W_1f480 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f484 : bv 32 := 0x00000593.
Lemma F_1f484 : fetch_word Plain.M.loaded_segments (0x1f708 : word) = Some W_1f484.
Proof. vm_refl. Qed.
Lemma D_1f484 : decode_any W_1f484 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f488 : bv 32 := 0x00020613.
Lemma F_1f488 : fetch_word Plain.M.loaded_segments (0x1f70c : word) = Some W_1f488.
Proof. vm_refl. Qed.
Lemma D_1f488 : decode_any W_1f488 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f48c : bv 32 := 0xf5862603.
Lemma F_1f48c : fetch_word Plain.M.loaded_segments (0x1f710 : word) = Some W_1f48c.
Proof. vm_refl. Qed.
Lemma D_1f48c : decode_any W_1f48c = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f490 : bv 32 := 0x0003b697.
Lemma F_1f490 : fetch_word Plain.M.loaded_segments (0x1f714 : word) = Some W_1f490.
Proof. vm_refl. Qed.
Lemma D_1f490 : decode_any W_1f490 = Some (Auipc 13 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f494 : bv 32 := 0x23468693.
Lemma F_1f494 : fetch_word Plain.M.loaded_segments (0x1f718 : word) = Some W_1f494.
Proof. vm_refl. Qed.
Lemma D_1f494 : decode_any W_1f494 = Some (OpImm ALU_ADD 13 13 564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f498 : bv 32 := 0x1606a72f.
Lemma F_1f498 : fetch_word Plain.M.loaded_segments (0x1f71c : word) = Some W_1f498.
Proof. vm_refl. Qed.
Lemma D_1f498 : decode_any W_1f498 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f49c : bv 32 := 0x00b71663.
Lemma F_1f49c : fetch_word Plain.M.loaded_segments (0x1f720 : word) = Some W_1f49c.
Proof. vm_refl. Qed.
Lemma D_1f49c : decode_any W_1f49c = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f4a0 : bv 32 := 0x1ec6a7af.
Lemma F_1f4a0 : fetch_word Plain.M.loaded_segments (0x1f724 : word) = Some W_1f4a0.
Proof. vm_refl. Qed.
Lemma D_1f4a0 : decode_any W_1f4a0 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f4a4 : bv 32 := 0xfe079ae3.
Lemma F_1f4a4 : fetch_word Plain.M.loaded_segments (0x1f728 : word) = Some W_1f4a4.
Proof. vm_refl. Qed.
Lemma D_1f4a4 : decode_any W_1f4a4 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f4a8 : bv 32 := 0x0007059b.
Lemma F_1f4a8 : fetch_word Plain.M.loaded_segments (0x1f72c : word) = Some W_1f4a8.
Proof. vm_refl. Qed.
Lemma D_1f4a8 : decode_any W_1f4a8 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f4ac : bv 32 := 0x02c58263.
Lemma F_1f4ac : fetch_word Plain.M.loaded_segments (0x1f730 : word) = Some W_1f4ac.
Proof. vm_refl. Qed.
Lemma D_1f4ac : decode_any W_1f4ac = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f4b0 : bv 32 := 0x02058263.
Lemma F_1f4b0 : fetch_word Plain.M.loaded_segments (0x1f734 : word) = Some W_1f4b0.
Proof. vm_refl. Qed.
Lemma D_1f4b0 : decode_any W_1f4b0 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f4d4 : bv 32 := 0x00050413.
Lemma F_1f4d4 : fetch_word Plain.M.loaded_segments (0x1f758 : word) = Some W_1f4d4.
Proof. vm_refl. Qed.
Lemma D_1f4d4 : decode_any W_1f4d4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f4d8 : bv 32 := 0xdbdff0ef.
Lemma F_1f4d8 : fetch_word Plain.M.loaded_segments (0x1f75c : word) = Some W_1f4d8.
Proof. vm_refl. Qed.
Lemma D_1f4d8 : decode_any W_1f4d8 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f4dc : bv 32 := 0xf51ff0ef.
Lemma F_1f4dc : fetch_word Plain.M.loaded_segments (0x1f760 : word) = Some W_1f4dc.
Proof. vm_refl. Qed.
Lemma D_1f4dc : decode_any W_1f4dc = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f4e0 : bv 32 := 0x348020ef.
Lemma F_1f4e0 : fetch_word Plain.M.loaded_segments (0x1f764 : word) = Some W_1f4e0.
Proof. vm_refl. Qed.
Lemma D_1f4e0 : decode_any W_1f4e0 = Some (Jal 1 9032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f4e4 : bv 32 := 0x00040513.
Lemma F_1f4e4 : fetch_word Plain.M.loaded_segments (0x1f768 : word) = Some W_1f4e4.
Proof. vm_refl. Qed.
Lemma D_1f4e4 : decode_any W_1f4e4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f4e8 : bv 32 := 0xd91ff0ef.
Lemma F_1f4e8 : fetch_word Plain.M.loaded_segments (0x1f76c : word) = Some W_1f4e8.
Proof. vm_refl. Qed.
Lemma D_1f4e8 : decode_any W_1f4e8 = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f5d0 : bv 32 := 0xff010113.
Lemma F_1f5d0 : fetch_word Plain.M.loaded_segments (0x1f854 : word) = Some W_1f5d0.
Proof. vm_refl. Qed.
Lemma D_1f5d0 : decode_any W_1f5d0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f5d4 : bv 32 := 0x00113423.
Lemma F_1f5d4 : fetch_word Plain.M.loaded_segments (0x1f858 : word) = Some W_1f5d4.
Proof. vm_refl. Qed.
Lemma D_1f5d4 : decode_any W_1f5d4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f5d8 : bv 32 := 0x00050e63.
Lemma F_1f5d8 : fetch_word Plain.M.loaded_segments (0x1f85c : word) = Some W_1f5d8.
Proof. vm_refl. Qed.
Lemma D_1f5d8 : decode_any W_1f5d8 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f5dc : bv 32 := 0x00050593.
Lemma F_1f5dc : fetch_word Plain.M.loaded_segments (0x1f860 : word) = Some W_1f5dc.
Proof. vm_refl. Qed.
Lemma D_1f5dc : decode_any W_1f5dc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f5e0 : bv 32 := 0x00009517.
Lemma F_1f5e0 : fetch_word Plain.M.loaded_segments (0x1f864 : word) = Some W_1f5e0.
Proof. vm_refl. Qed.
Lemma D_1f5e0 : decode_any W_1f5e0 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f5e4 : bv 32 := 0xe1453503.
Lemma F_1f5e4 : fetch_word Plain.M.loaded_segments (0x1f868 : word) = Some W_1f5e4.
Proof. vm_refl. Qed.
Lemma D_1f5e4 : decode_any W_1f5e4 = Some (Load SZ8 true 10 10 3604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f5e8 : bv 32 := 0x00800613.
Lemma F_1f5e8 : fetch_word Plain.M.loaded_segments (0x1f86c : word) = Some W_1f5e8.
Proof. vm_refl. Qed.
Lemma D_1f5e8 : decode_any W_1f5e8 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f5ec : bv 32 := 0x378070ef.
Lemma F_1f5ec : fetch_word Plain.M.loaded_segments (0x1f870 : word) = Some W_1f5ec.
Proof. vm_refl. Qed.
Lemma D_1f5ec : decode_any W_1f5ec = Some (Jal 1 29560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f5f0 : bv 32 := 0x01c0006f.
Lemma F_1f5f0 : fetch_word Plain.M.loaded_segments (0x1f874 : word) = Some W_1f5f0.
Proof. vm_refl. Qed.
Lemma D_1f5f0 : decode_any W_1f5f0 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f60c : bv 32 := 0x00009517.
Lemma F_1f60c : fetch_word Plain.M.loaded_segments (0x1f890 : word) = Some W_1f60c.
Proof. vm_refl. Qed.
Lemma D_1f60c : decode_any W_1f60c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f610 : bv 32 := 0xde853503.
Lemma F_1f610 : fetch_word Plain.M.loaded_segments (0x1f894 : word) = Some W_1f610.
Proof. vm_refl. Qed.
Lemma D_1f610 : decode_any W_1f610 = Some (Load SZ8 true 10 10 3560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f614 : bv 32 := 0x000500a3.
Lemma F_1f614 : fetch_word Plain.M.loaded_segments (0x1f898 : word) = Some W_1f614.
Proof. vm_refl. Qed.
Lemma D_1f614 : decode_any W_1f614 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f618 : bv 32 := 0x00053503.
Lemma F_1f618 : fetch_word Plain.M.loaded_segments (0x1f89c : word) = Some W_1f618.
Proof. vm_refl. Qed.
Lemma D_1f618 : decode_any W_1f618 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f61c : bv 32 := 0x00020593.
Lemma F_1f61c : fetch_word Plain.M.loaded_segments (0x1f8a0 : word) = Some W_1f61c.
Proof. vm_refl. Qed.
Lemma D_1f61c : decode_any W_1f61c = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.
