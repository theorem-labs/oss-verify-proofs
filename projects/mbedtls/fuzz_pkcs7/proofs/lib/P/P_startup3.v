(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (section P4 restated over the whole process input, mmap base, entry and draw, with the valid_launch and entry_launch_ok_va hypotheses, its stack and data words read through pn_w, J_aux, J_lsm and D_libc at the new arguments; the lia oracle and its recorded tables, the CDefT import and the using attributes dropped, with Default Proof Using set to All). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Plain.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StartupTac ArgvEnv Layout.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_img P_startup_defs   .
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.
Local Set Default Proof Using "All".

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Module P_startup3_rc2.
Definition W_3bbb4 : bv 32 := 0xfc010113.
Lemma F_3bbb4 : fetch_word Plain.M.loaded_segments (0x3bbb4 : word) = Some W_3bbb4.
Proof. vm_refl_bv. Qed.
Lemma D_3bbb4 : decode_any W_3bbb4 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbb8 : bv 32 := 0x02113c23.
Lemma F_3bbb8 : fetch_word Plain.M.loaded_segments (0x3bbb8 : word) = Some W_3bbb8.
Proof. vm_refl_bv. Qed.
Lemma D_3bbb8 : decode_any W_3bbb8 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbbc : bv 32 := 0x02813823.
Lemma F_3bbbc : fetch_word Plain.M.loaded_segments (0x3bbbc : word) = Some W_3bbbc.
Proof. vm_refl_bv. Qed.
Lemma D_3bbbc : decode_any W_3bbbc = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbc0 : bv 32 := 0x02913423.
Lemma F_3bbc0 : fetch_word Plain.M.loaded_segments (0x3bbc0 : word) = Some W_3bbc0.
Proof. vm_refl_bv. Qed.
Lemma D_3bbc0 : decode_any W_3bbc0 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbc4 : bv 32 := 0x03213023.
Lemma F_3bbc4 : fetch_word Plain.M.loaded_segments (0x3bbc4 : word) = Some W_3bbc4.
Proof. vm_refl_bv. Qed.
Lemma D_3bbc4 : decode_any W_3bbc4 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbc8 : bv 32 := 0x01313c23.
Lemma F_3bbc8 : fetch_word Plain.M.loaded_segments (0x3bbc8 : word) = Some W_3bbc8.
Proof. vm_refl_bv. Qed.
Lemma D_3bbc8 : decode_any W_3bbc8 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbcc : bv 32 := 0x01413823.
Lemma F_3bbcc : fetch_word Plain.M.loaded_segments (0x3bbcc : word) = Some W_3bbcc.
Proof. vm_refl_bv. Qed.
Lemma D_3bbcc : decode_any W_3bbcc = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbd0 : bv 32 := 0x01513423.
Lemma F_3bbd0 : fetch_word Plain.M.loaded_segments (0x3bbd0 : word) = Some W_3bbd0.
Proof. vm_refl_bv. Qed.
Lemma D_3bbd0 : decode_any W_3bbd0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbd4 : bv 32 := 0x02853683.
Lemma F_3bbd4 : fetch_word Plain.M.loaded_segments (0x3bbd4 : word) = Some W_3bbd4.
Proof. vm_refl_bv. Qed.
Lemma D_3bbd4 : decode_any W_3bbd4 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbd8 : bv 32 := 0x0003e597.
Lemma F_3bbd8 : fetch_word Plain.M.loaded_segments (0x3bbd8 : word) = Some W_3bbd8.
Proof. vm_refl_bv. Qed.
Lemma D_3bbd8 : decode_any W_3bbd8 = Some (Auipc 11 62, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbdc : bv 32 := 0xdf858593.
Lemma F_3bbdc : fetch_word Plain.M.loaded_segments (0x3bbdc : word) = Some W_3bbdc.
Proof. vm_refl_bv. Qed.
Lemma D_3bbdc : decode_any W_3bbdc = Some (OpImm ALU_ADD 11 11 3576, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbe0 : bv 32 := 0x0003e617.
Lemma F_3bbe0 : fetch_word Plain.M.loaded_segments (0x3bbe0 : word) = Some W_3bbe0.
Proof. vm_refl_bv. Qed.
Lemma D_3bbe0 : decode_any W_3bbe0 = Some (Auipc 12 62, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbe4 : bv 32 := 0x07060493.
Lemma F_3bbe4 : fetch_word Plain.M.loaded_segments (0x3bbe4 : word) = Some W_3bbe4.
Proof. vm_refl_bv. Qed.
Lemma D_3bbe4 : decode_any W_3bbe4 = Some (OpImm ALU_ADD 9 12 112, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbe8 : bv 32 := 0x0c068e63.
Lemma F_3bbe8 : fetch_word Plain.M.loaded_segments (0x3bbe8 : word) = Some W_3bbe8.
Proof. vm_refl_bv. Qed.
Lemma D_3bbe8 : decode_any W_3bbe8 = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbec : bv 32 := 0x00000613.
Lemma F_3bbec : fetch_word Plain.M.loaded_segments (0x3bbec : word) = Some W_3bbec.
Proof. vm_refl_bv. Qed.
Lemma D_3bbec : decode_any W_3bbec = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbf0 : bv 32 := 0x00000893.
Lemma F_3bbf0 : fetch_word Plain.M.loaded_segments (0x3bbf0 : word) = Some W_3bbf0.
Proof. vm_refl_bv. Qed.
Lemma D_3bbf0 : decode_any W_3bbf0 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbf4 : bv 32 := 0x0000e717.
Lemma F_3bbf4 : fetch_word Plain.M.loaded_segments (0x3bbf4 : word) = Some W_3bbf4.
Proof. vm_refl_bv. Qed.
Lemma D_3bbf4 : decode_any W_3bbf4 = Some (Auipc 14 14, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbf8 : bv 32 := 0x01853783.
Lemma F_3bbf8 : fetch_word Plain.M.loaded_segments (0x3bbf8 : word) = Some W_3bbf8.
Proof. vm_refl_bv. Qed.
Lemma D_3bbf8 : decode_any W_3bbf8 = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbfc : bv 32 := 0x02053503.
Lemma F_3bbfc : fetch_word Plain.M.loaded_segments (0x3bbfc : word) = Some W_3bbfc.
Proof. vm_refl_bv. Qed.
Lemma D_3bbfc : decode_any W_3bbfc = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc00 : bv 32 := 0x00600813.
Lemma F_3bc00 : fetch_word Plain.M.loaded_segments (0x3bc00 : word) = Some W_3bc00.
Proof. vm_refl_bv. Qed.
Lemma D_3bc00 : decode_any W_3bc00 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc04 : bv 32 := 0x0000d297.
Lemma F_3bc04 : fetch_word Plain.M.loaded_segments (0x3bc04 : word) = Some W_3bc04.
Proof. vm_refl_bv. Qed.
Lemma D_3bc04 : decode_any W_3bc04 = Some (Auipc 5 13, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc08 : bv 32 := 0xc2476f03.
Lemma F_3bc08 : fetch_word Plain.M.loaded_segments (0x3bc08 : word) = Some W_3bc08.
Proof. vm_refl_bv. Qed.
Lemma D_3bc08 : decode_any W_3bc08 = Some (Load SZ4 false 30 14 3108, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc0c : bv 32 := 0x95c2b283.
Lemma F_3bc0c : fetch_word Plain.M.loaded_segments (0x3bc0c : word) = Some W_3bc0c.
Proof. vm_refl_bv. Qed.
Lemma D_3bc0c : decode_any W_3bc0c = Some (Load SZ8 true 5 5 2396, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc10 : bv 32 := 0x00200313.
Lemma F_3bc10 : fetch_word Plain.M.loaded_segments (0x3bc10 : word) = Some W_3bc10.
Proof. vm_refl_bv. Qed.
Lemma D_3bc10 : decode_any W_3bc10 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc14 : bv 32 := 0x00700393.
Lemma F_3bc14 : fetch_word Plain.M.loaded_segments (0x3bc14 : word) = Some W_3bc14.
Proof. vm_refl_bv. Qed.
Lemma D_3bc14 : decode_any W_3bc14 = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc18 : bv 32 := 0x6474ee37.
Lemma F_3bc18 : fetch_word Plain.M.loaded_segments (0x3bc18 : word) = Some W_3bc18.
Proof. vm_refl_bv. Qed.
Lemma D_3bc18 : decode_any W_3bc18 = Some (Lui 28 411470, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc1c : bv 32 := 0x551e0e1b.
Lemma F_3bc1c : fetch_word Plain.M.loaded_segments (0x3bc1c : word) = Some W_3bc1c.
Proof. vm_refl_bv. Qed.
Lemma D_3bc1c : decode_any W_3bc1c = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc20 : bv 32 := 0x00078e93.
Lemma F_3bc20 : fetch_word Plain.M.loaded_segments (0x3bc20 : word) = Some W_3bc20.
Proof. vm_refl_bv. Qed.
Lemma D_3bc20 : decode_any W_3bc20 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc24 : bv 32 := 0x0180006f.
Lemma F_3bc24 : fetch_word Plain.M.loaded_segments (0x3bc24 : word) = Some W_3bc24.
Proof. vm_refl_bv. Qed.
Lemma D_3bc24 : decode_any W_3bc24 = Some (Jal 0 24, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc28 : bv 32 := 0x010eb603.
Lemma F_3bc28 : fetch_word Plain.M.loaded_segments (0x3bc28 : word) = Some W_3bc28.
Proof. vm_refl_bv. Qed.
Lemma D_3bc28 : decode_any W_3bc28 = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc2c : bv 32 := 0x40c78633.
Lemma F_3bc2c : fetch_word Plain.M.loaded_segments (0x3bc2c : word) = Some W_3bc2c.
Proof. vm_refl_bv. Qed.
Lemma D_3bc2c : decode_any W_3bc2c = Some (Op ALU_SUB 12 15 12, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc30 : bv 32 := 0xfff68693.
Lemma F_3bc30 : fetch_word Plain.M.loaded_segments (0x3bc30 : word) = Some W_3bc30.
Proof. vm_refl_bv. Qed.
Lemma D_3bc30 : decode_any W_3bc30 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc34 : bv 32 := 0x00ae8eb3.
Lemma F_3bc34 : fetch_word Plain.M.loaded_segments (0x3bc34 : word) = Some W_3bc34.
Proof. vm_refl_bv. Qed.
Lemma D_3bc34 : decode_any W_3bc34 = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc38 : bv 32 := 0x04068a63.
Lemma F_3bc38 : fetch_word Plain.M.loaded_segments (0x3bc38 : word) = Some W_3bc38.
Proof. vm_refl_bv. Qed.
Lemma D_3bc38 : decode_any W_3bc38 = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc3c : bv 32 := 0x000ea403.
Lemma F_3bc3c : fetch_word Plain.M.loaded_segments (0x3bc3c : word) = Some W_3bc3c.
Proof. vm_refl_bv. Qed.
Lemma D_3bc3c : decode_any W_3bc3c = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc40 : bv 32 := 0xff0404e3.
Lemma F_3bc40 : fetch_word Plain.M.loaded_segments (0x3bc40 : word) = Some W_3bc40.
Proof. vm_refl_bv. Qed.
Lemma D_3bc40 : decode_any W_3bc40 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc44 : bv 32 := 0x00028a63.
Lemma F_3bc44 : fetch_word Plain.M.loaded_segments (0x3bc44 : word) = Some W_3bc44.
Proof. vm_refl_bv. Qed.
Lemma D_3bc44 : decode_any W_3bc44 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc58 : bv 32 := 0x000e8f93.
Lemma F_3bc58 : fetch_word Plain.M.loaded_segments (0x3bc58 : word) = Some W_3bc58.
Proof. vm_refl_bv. Qed.
Lemma D_3bc58 : decode_any W_3bc58 = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc5c : bv 32 := 0x00740463.
Lemma F_3bc5c : fetch_word Plain.M.loaded_segments (0x3bc5c : word) = Some W_3bc5c.
Proof. vm_refl_bv. Qed.
Lemma D_3bc5c : decode_any W_3bc5c = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc60 : bv 32 := 0x00088f93.
Lemma F_3bc60 : fetch_word Plain.M.loaded_segments (0x3bc60 : word) = Some W_3bc60.
Proof. vm_refl_bv. Qed.
Lemma D_3bc60 : decode_any W_3bc60 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc64 : bv 32 := 0x03c41063.
Lemma F_3bc64 : fetch_word Plain.M.loaded_segments (0x3bc64 : word) = Some W_3bc64.
Proof. vm_refl_bv. Qed.
Lemma D_3bc64 : decode_any W_3bc64 = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc68 : bv 32 := 0x028eb883.
Lemma F_3bc68 : fetch_word Plain.M.loaded_segments (0x3bc68 : word) = Some W_3bc68.
Proof. vm_refl_bv. Qed.
Lemma D_3bc68 : decode_any W_3bc68 = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc6c : bv 32 := 0x011f7c63.
Lemma F_3bc6c : fetch_word Plain.M.loaded_segments (0x3bc6c : word) = Some W_3bc6c.
Proof. vm_refl_bv. Qed.
Lemma D_3bc6c : decode_any W_3bc6c = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc84 : bv 32 := 0x000f8893.
Lemma F_3bc84 : fetch_word Plain.M.loaded_segments (0x3bc84 : word) = Some W_3bc84.
Proof. vm_refl_bv. Qed.
Lemma D_3bc84 : decode_any W_3bc84 = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc88 : bv 32 := 0xfa9ff06f.
Lemma F_3bc88 : fetch_word Plain.M.loaded_segments (0x3bc88 : word) = Some W_3bc88.
Proof. vm_refl_bv. Qed.
Lemma D_3bc88 : decode_any W_3bc88 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc8c : bv 32 := 0x02088c63.
Lemma F_3bc8c : fetch_word Plain.M.loaded_segments (0x3bc8c : word) = Some W_3bc8c.
Proof. vm_refl_bv. Qed.
Lemma D_3bc8c : decode_any W_3bc8c = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcc4 : bv 32 := 0x0105b603.
Lemma F_3bcc4 : fetch_word Plain.M.loaded_segments (0x3bcc4 : word) = Some W_3bcc4.
Proof. vm_refl_bv. Qed.
Lemma D_3bcc4 : decode_any W_3bcc4 = Some (Load SZ8 true 12 11 16, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcc8 : bv 32 := 0x0205b683.
Lemma F_3bcc8 : fetch_word Plain.M.loaded_segments (0x3bcc8 : word) = Some W_3bcc8.
Proof. vm_refl_bv. Qed.
Lemma D_3bcc8 : decode_any W_3bcc8 = Some (Load SZ8 true 13 11 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bccc : bv 32 := 0x0285b503.
Lemma F_3bccc : fetch_word Plain.M.loaded_segments (0x3bccc : word) = Some W_3bccc.
Proof. vm_refl_bv. Qed.
Lemma D_3bccc : decode_any W_3bccc = Some (Load SZ8 true 10 11 40, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcd0 : bv 32 := 0x00c68733.
Lemma F_3bcd0 : fetch_word Plain.M.loaded_segments (0x3bcd0 : word) = Some W_3bcd0.
Proof. vm_refl_bv. Qed.
Lemma D_3bcd0 : decode_any W_3bcd0 = Some (Op ALU_ADD 14 13 12, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcd4 : bv 32 := 0xfff50793.
Lemma F_3bcd4 : fetch_word Plain.M.loaded_segments (0x3bcd4 : word) = Some W_3bcd4.
Proof. vm_refl_bv. Qed.
Lemma D_3bcd4 : decode_any W_3bcd4 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcd8 : bv 32 := 0x40e00733.
Lemma F_3bcd8 : fetch_word Plain.M.loaded_segments (0x3bcd8 : word) = Some W_3bcd8.
Proof. vm_refl_bv. Qed.
Lemma D_3bcd8 : decode_any W_3bcd8 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcdc : bv 32 := 0x00c7f633.
Lemma F_3bcdc : fetch_word Plain.M.loaded_segments (0x3bcdc : word) = Some W_3bcdc.
Proof. vm_refl_bv. Qed.
Lemma D_3bcdc : decode_any W_3bcdc = Some (Op ALU_AND 12 15 12, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bce0 : bv 32 := 0x00e7f733.
Lemma F_3bce0 : fetch_word Plain.M.loaded_segments (0x3bce0 : word) = Some W_3bce0.
Proof. vm_refl_bv. Qed.
Lemma D_3bce0 : decode_any W_3bce0 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bce4 : bv 32 := 0x00700793.
Lemma F_3bce4 : fetch_word Plain.M.loaded_segments (0x3bce4 : word) = Some W_3bce4.
Proof. vm_refl_bv. Qed.
Lemma D_3bce4 : decode_any W_3bce4 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bce8 : bv 32 := 0x00d706b3.
Lemma F_3bce8 : fetch_word Plain.M.loaded_segments (0x3bce8 : word) = Some W_3bce8.
Proof. vm_refl_bv. Qed.
Lemma D_3bce8 : decode_any W_3bce8 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcec : bv 32 := 0x02d5b023.
Lemma F_3bcec : fetch_word Plain.M.loaded_segments (0x3bcec : word) = Some W_3bcec.
Proof. vm_refl_bv. Qed.
Lemma D_3bcec : decode_any W_3bcec = Some (Store SZ8 11 13 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcf0 : bv 32 := 0x02c5b823.
Lemma F_3bcf0 : fetch_word Plain.M.loaded_segments (0x3bcf0 : word) = Some W_3bcf0.
Proof. vm_refl_bv. Qed.
Lemma D_3bcf0 : decode_any W_3bcf0 = Some (Store SZ8 11 12 48, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcf4 : bv 32 := 0x00a7e663.
Lemma F_3bcf4 : fetch_word Plain.M.loaded_segments (0x3bcf4 : word) = Some W_3bcf4.
Proof. vm_refl_bv. Qed.
Lemma D_3bcf4 : decode_any W_3bcf4 = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcf8 : bv 32 := 0x00800513.
Lemma F_3bcf8 : fetch_word Plain.M.loaded_segments (0x3bcf8 : word) = Some W_3bcf8.
Proof. vm_refl_bv. Qed.
Lemma D_3bcf8 : decode_any W_3bcf8 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcfc : bv 32 := 0x02a5b423.
Lemma F_3bcfc : fetch_word Plain.M.loaded_segments (0x3bcfc : word) = Some W_3bcfc.
Proof. vm_refl_bv. Qed.
Lemma D_3bcfc : decode_any W_3bcfc = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd00 : bv 32 := 0x00d60633.
Lemma F_3bd00 : fetch_word Plain.M.loaded_segments (0x3bd00 : word) = Some W_3bd00.
Proof. vm_refl_bv. Qed.
Lemma D_3bd00 : decode_any W_3bd00 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd04 : bv 32 := 0x000205b7.
Lemma F_3bd04 : fetch_word Plain.M.loaded_segments (0x3bd04 : word) = Some W_3bd04.
Proof. vm_refl_bv. Qed.
Lemma D_3bd04 : decode_any W_3bd04 = Some (Lui 11 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd08 : bv 32 := 0x00a60633.
Lemma F_3bd08 : fetch_word Plain.M.loaded_segments (0x3bd08 : word) = Some W_3bd08.
Proof. vm_refl_bv. Qed.
Lemma D_3bd08 : decode_any W_3bd08 = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd0c : bv 32 := 0x0d15869b.
Lemma F_3bd0c : fetch_word Plain.M.loaded_segments (0x3bd0c : word) = Some W_3bd0c.
Proof. vm_refl_bv. Qed.
Lemma D_3bd0c : decode_any W_3bd0c = Some (OpImm32 13 11 209, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd10 : bv 32 := 0x0df60593.
Lemma F_3bd10 : fetch_word Plain.M.loaded_segments (0x3bd10 : word) = Some W_3bd10.
Proof. vm_refl_bv. Qed.
Lemma D_3bd10 : decode_any W_3bd10 = Some (OpImm ALU_ADD 11 12 223, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd14 : bv 32 := 0xff85f593.
Lemma F_3bd14 : fetch_word Plain.M.loaded_segments (0x3bd14 : word) = Some W_3bd14.
Proof. vm_refl_bv. Qed.
Lemma D_3bd14 : decode_any W_3bd14 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd18 : bv 32 := 0x00b4bc23.
Lemma F_3bd18 : fetch_word Plain.M.loaded_segments (0x3bd18 : word) = Some W_3bd18.
Proof. vm_refl_bv. Qed.
Lemma D_3bd18 : decode_any W_3bd18 = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd1c : bv 32 := 0x02a4b023.
Lemma F_3bd1c : fetch_word Plain.M.loaded_segments (0x3bd1c : word) = Some W_3bd1c.
Proof. vm_refl_bv. Qed.
Lemma D_3bd1c : decode_any W_3bd1c = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd20 : bv 32 := 0x02d5ea63.
Lemma F_3bd20 : fetch_word Plain.M.loaded_segments (0x3bd20 : word) = Some W_3bd20.
Proof. vm_refl_bv. Qed.
Lemma D_3bd20 : decode_any W_3bd20 = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd54 : bv 32 := 0x0001e697.
Lemma F_3bd54 : fetch_word Plain.M.loaded_segments (0x3bd54 : word) = Some W_3bd54.
Proof. vm_refl_bv. Qed.
Lemma D_3bd54 : decode_any W_3bd54 = Some (Auipc 13 30, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd58 : bv 32 := 0x0104b983.
Lemma F_3bd58 : fetch_word Plain.M.loaded_segments (0x3bd58 : word) = Some W_3bd58.
Proof. vm_refl_bv. Qed.
Lemma D_3bd58 : decode_any W_3bd58 = Some (Load SZ8 true 19 9 16, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd5c : bv 32 := 0x0284b603.
Lemma F_3bd5c : fetch_word Plain.M.loaded_segments (0x3bd5c : word) = Some W_3bd5c.
Proof. vm_refl_bv. Qed.
Lemma D_3bd5c : decode_any W_3bd5c = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd60 : bv 32 := 0xfff50713.
Lemma F_3bd60 : fetch_word Plain.M.loaded_segments (0x3bd60 : word) = Some W_3bd60.
Proof. vm_refl_bv. Qed.
Lemma D_3bd60 : decode_any W_3bd60 = Some (OpImm ALU_ADD 14 10 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd64 : bv 32 := 0xf3800793.
Lemma F_3bd64 : fetch_word Plain.M.loaded_segments (0x3bd64 : word) = Some W_3bd64.
Proof. vm_refl_bv. Qed.
Lemma D_3bd64 : decode_any W_3bd64 = Some (OpImm ALU_ADD 15 0 3896, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd68 : bv 32 := 0xbac68513.
Lemma F_3bd68 : fetch_word Plain.M.loaded_segments (0x3bd68 : word) = Some W_3bd68.
Proof. vm_refl_bv. Qed.
Lemma D_3bd68 : decode_any W_3bd68 = Some (OpImm ALU_ADD 10 13 2988, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd6c : bv 32 := 0x40a787b3.
Lemma F_3bd6c : fetch_word Plain.M.loaded_segments (0x3bd6c : word) = Some W_3bd6c.
Proof. vm_refl_bv. Qed.
Lemma D_3bd6c : decode_any W_3bd6c = Some (Op ALU_SUB 15 15 10, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd70 : bv 32 := 0x00f77733.
Lemma F_3bd70 : fetch_word Plain.M.loaded_segments (0x3bd70 : word) = Some W_3bd70.
Proof. vm_refl_bv. Qed.
Lemma D_3bd70 : decode_any W_3bd70 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd74 : bv 32 := 0xfff64693.
Lemma F_3bd74 : fetch_word Plain.M.loaded_segments (0x3bd74 : word) = Some W_3bd74.
Proof. vm_refl_bv. Qed.
Lemma D_3bd74 : decode_any W_3bd74 = Some (OpImm ALU_XOR 13 12 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd78 : bv 32 := 0x00e50933.
Lemma F_3bd78 : fetch_word Plain.M.loaded_segments (0x3bd78 : word) = Some W_3bd78.
Proof. vm_refl_bv. Qed.
Lemma D_3bd78 : decode_any W_3bd78 = Some (Op ALU_ADD 18 10 14, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd7c : bv 32 := 0x00369693.
Lemma F_3bd7c : fetch_word Plain.M.loaded_segments (0x3bd7c : word) = Some W_3bd7c.
Proof. vm_refl_bv. Qed.
Lemma D_3bd7c : decode_any W_3bd7c = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd80 : bv 32 := 0x00d506b3.
Lemma F_3bd80 : fetch_word Plain.M.loaded_segments (0x3bd80 : word) = Some W_3bd80.
Proof. vm_refl_bv. Qed.
Lemma D_3bd80 : decode_any W_3bd80 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd84 : bv 32 := 0x00b68a33.
Lemma F_3bd84 : fetch_word Plain.M.loaded_segments (0x3bd84 : word) = Some W_3bd84.
Proof. vm_refl_bv. Qed.
Lemma D_3bd84 : decode_any W_3bd84 = Some (Op ALU_ADD 20 13 11, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd88 : bv 32 := 0x0c890413.
Lemma F_3bd88 : fetch_word Plain.M.loaded_segments (0x3bd88 : word) = Some W_3bd88.
Proof. vm_refl_bv. Qed.
Lemma D_3bd88 : decode_any W_3bd88 = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd8c : bv 32 := 0x04098463.
Lemma F_3bd8c : fetch_word Plain.M.loaded_segments (0x3bd8c : word) = Some W_3bd8c.
Proof. vm_refl_bv. Qed.
Lemma D_3bd8c : decode_any W_3bd8c = Some (Branch BC_EQ 19 0 72, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bdd4 : bv 32 := 0x00ca3023.
Lemma F_3bdd4 : fetch_word Plain.M.loaded_segments (0x3bdd4 : word) = Some W_3bdd4.
Proof. vm_refl_bv. Qed.
Lemma D_3bdd4 : decode_any W_3bdd4 = Some (Store SZ8 20 12 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bdd8 : bv 32 := 0x0d493023.
Lemma F_3bdd8 : fetch_word Plain.M.loaded_segments (0x3bdd8 : word) = Some W_3bdd8.
Proof. vm_refl_bv. Qed.
Lemma D_3bdd8 : decode_any W_3bdd8 = Some (Store SZ8 18 20 192, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bddc : bv 32 := 0x01293023.
Lemma F_3bddc : fetch_word Plain.M.loaded_segments (0x3bddc : word) = Some W_3bddc.
Proof. vm_refl_bv. Qed.
Lemma D_3bddc : decode_any W_3bddc = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bde0 : bv 32 := 0x00040513.
Lemma F_3bde0 : fetch_word Plain.M.loaded_segments (0x3bde0 : word) = Some W_3bde0.
Proof. vm_refl_bv. Qed.
Lemma D_3bde0 : decode_any W_3bde0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bde4 : bv 32 := 0x5c9070ef.
Lemma F_3bde4 : fetch_word Plain.M.loaded_segments (0x3bde4 : word) = Some W_3bde4.
Proof. vm_refl_bv. Qed.
Lemma D_3bde4 : decode_any W_3bde4 = Some (Jal 1 32200, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bde8 : bv 32 := 0x04054a63.
Lemma F_3bde8 : fetch_word Plain.M.loaded_segments (0x3bde8 : word) = Some W_3bde8.
Proof. vm_refl_bv. Qed.
Lemma D_3bde8 : decode_any W_3bde8 = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bdec : bv 32 := 0x00051663.
Lemma F_3bdec : fetch_word Plain.M.loaded_segments (0x3bdec : word) = Some W_3bdec.
Proof. vm_refl_bv. Qed.
Lemma D_3bdec : decode_any W_3bdec = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bdf0 : bv 32 := 0x00100513.
Lemma F_3bdf0 : fetch_word Plain.M.loaded_segments (0x3bdf0 : word) = Some W_3bdf0.
Proof. vm_refl_bv. Qed.
Lemma D_3bdf0 : decode_any W_3bdf0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bdf4 : bv 32 := 0x00a48023.
Lemma F_3bdf4 : fetch_word Plain.M.loaded_segments (0x3bdf4 : word) = Some W_3bdf4.
Proof. vm_refl_bv. Qed.
Lemma D_3bdf4 : decode_any W_3bdf4 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bdf8 : bv 32 := 0x00200513.
Lemma F_3bdf8 : fetch_word Plain.M.loaded_segments (0x3bdf8 : word) = Some W_3bdf8.
Proof. vm_refl_bv. Qed.
Lemma D_3bdf8 : decode_any W_3bdf8 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bdfc : bv 32 := 0x0003e597.
Lemma F_3bdfc : fetch_word Plain.M.loaded_segments (0x3bdfc : word) = Some W_3bdfc.
Proof. vm_refl_bv. Qed.
Lemma D_3bdfc : decode_any W_3bdfc = Some (Auipc 11 62, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be00 : bv 32 := 0x02a92423.
Lemma F_3be00 : fetch_word Plain.M.loaded_segments (0x3be00 : word) = Some W_3be00.
Proof. vm_refl_bv. Qed.
Lemma D_3be00 : decode_any W_3be00 = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be04 : bv 32 := 0x06000893.
Lemma F_3be04 : fetch_word Plain.M.loaded_segments (0x3be04 : word) = Some W_3be04.
Proof. vm_refl_bv. Qed.
Lemma D_3be04 : decode_any W_3be04 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be08 : bv 32 := 0xbd458513.
Lemma F_3be08 : fetch_word Plain.M.loaded_segments (0x3be08 : word) = Some W_3be08.
Proof. vm_refl_bv. Qed.
Lemma D_3be08 : decode_any W_3be08 = Some (OpImm ALU_ADD 10 11 3028, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be0c : bv 32 := 0x03848593.
Lemma F_3be0c : fetch_word Plain.M.loaded_segments (0x3be0c : word) = Some W_3be0c.
Proof. vm_refl_bv. Qed.
Lemma D_3be0c : decode_any W_3be0c = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be10 : bv 32 := 0x00000073.
Lemma F_3be10 : fetch_word Plain.M.loaded_segments (0x3be10 : word) = Some W_3be10.
Proof. vm_refl_bv. Qed.
Lemma E_3be10 : is_ecall W_3be10 = true.
Proof. reflexivity. Qed.
Definition W_3be14 : bv 32 := 0x07890613.
Lemma F_3be14 : fetch_word Plain.M.loaded_segments (0x3be14 : word) = Some W_3be14.
Proof. vm_refl_bv. Qed.
Lemma D_3be14 : decode_any W_3be14 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be18 : bv 32 := 0x02a92023.
Lemma F_3be18 : fetch_word Plain.M.loaded_segments (0x3be18 : word) = Some W_3be18.
Proof. vm_refl_bv. Qed.
Lemma D_3be18 : decode_any W_3be18 = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be1c : bv 32 := 0x08b93c23.
Lemma F_3be1c : fetch_word Plain.M.loaded_segments (0x3be1c : word) = Some W_3be1c.
Proof. vm_refl_bv. Qed.
Lemma D_3be1c : decode_any W_3be1c = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be20 : bv 32 := 0x06c93c23.
Lemma F_3be20 : fetch_word Plain.M.loaded_segments (0x3be20 : word) = Some W_3be20.
Proof. vm_refl_bv. Qed.
Lemma D_3be20 : decode_any W_3be20 = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be24 : bv 32 := 0x0003e517.
Lemma F_3be24 : fetch_word Plain.M.loaded_segments (0x3be24 : word) = Some W_3be24.
Proof. vm_refl_bv. Qed.
Lemma D_3be24 : decode_any W_3be24 = Some (Auipc 10 62, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be28 : bv 32 := 0xe1453503.
Lemma F_3be28 : fetch_word Plain.M.loaded_segments (0x3be28 : word) = Some W_3be28.
Proof. vm_refl_bv. Qed.
Lemma D_3be28 : decode_any W_3be28 = Some (Load SZ8 true 10 10 3604, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be2c : bv 32 := 0x01293423.
Lemma F_3be2c : fetch_word Plain.M.loaded_segments (0x3be2c : word) = Some W_3be2c.
Proof. vm_refl_bv. Qed.
Lemma D_3be2c : decode_any W_3be2c = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be30 : bv 32 := 0x01293823.
Lemma F_3be30 : fetch_word Plain.M.loaded_segments (0x3be30 : word) = Some W_3be30.
Proof. vm_refl_bv. Qed.
Lemma D_3be30 : decode_any W_3be30 = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be34 : bv 32 := 0x00a93c23.
Lemma F_3be34 : fetch_word Plain.M.loaded_segments (0x3be34 : word) = Some W_3be34.
Proof. vm_refl_bv. Qed.
Lemma D_3be34 : decode_any W_3be34 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be38 : bv 32 := 0x0080006f.
Lemma F_3be38 : fetch_word Plain.M.loaded_segments (0x3be38 : word) = Some W_3be38.
Proof. vm_refl_bv. Qed.
Lemma D_3be38 : decode_any W_3be38 = Some (Jal 0 8, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be40 : bv 32 := 0x03813083.
Lemma F_3be40 : fetch_word Plain.M.loaded_segments (0x3be40 : word) = Some W_3be40.
Proof. vm_refl_bv. Qed.
Lemma D_3be40 : decode_any W_3be40 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be44 : bv 32 := 0x03013403.
Lemma F_3be44 : fetch_word Plain.M.loaded_segments (0x3be44 : word) = Some W_3be44.
Proof. vm_refl_bv. Qed.
Lemma D_3be44 : decode_any W_3be44 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be48 : bv 32 := 0x02813483.
Lemma F_3be48 : fetch_word Plain.M.loaded_segments (0x3be48 : word) = Some W_3be48.
Proof. vm_refl_bv. Qed.
Lemma D_3be48 : decode_any W_3be48 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be4c : bv 32 := 0x02013903.
Lemma F_3be4c : fetch_word Plain.M.loaded_segments (0x3be4c : word) = Some W_3be4c.
Proof. vm_refl_bv. Qed.
Lemma D_3be4c : decode_any W_3be4c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be50 : bv 32 := 0x01813983.
Lemma F_3be50 : fetch_word Plain.M.loaded_segments (0x3be50 : word) = Some W_3be50.
Proof. vm_refl_bv. Qed.
Lemma D_3be50 : decode_any W_3be50 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be54 : bv 32 := 0x01013a03.
Lemma F_3be54 : fetch_word Plain.M.loaded_segments (0x3be54 : word) = Some W_3be54.
Proof. vm_refl_bv. Qed.
Lemma D_3be54 : decode_any W_3be54 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be58 : bv 32 := 0x00813a83.
Lemma F_3be58 : fetch_word Plain.M.loaded_segments (0x3be58 : word) = Some W_3be58.
Proof. vm_refl_bv. Qed.
Lemma D_3be58 : decode_any W_3be58 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be5c : bv 32 := 0x04010113.
Lemma F_3be5c : fetch_word Plain.M.loaded_segments (0x3be5c : word) = Some W_3be5c.
Proof. vm_refl_bv. Qed.
Lemma D_3be5c : decode_any W_3be5c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be60 : bv 32 := 0x00008067.
Lemma F_3be60 : fetch_word Plain.M.loaded_segments (0x3be60 : word) = Some W_3be60.
Proof. vm_refl_bv. Qed.
Lemma D_3be60 : decode_any W_3be60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_43bac : bv 32 := 0x00050213.
Lemma F_43bac : fetch_word Plain.M.loaded_segments (0x43bac : word) = Some W_43bac.
Proof. vm_refl_bv. Qed.
Lemma D_43bac : decode_any W_43bac = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_43bb0 : bv 32 := 0x00000513.
Lemma F_43bb0 : fetch_word Plain.M.loaded_segments (0x43bb0 : word) = Some W_43bb0.
Proof. vm_refl_bv. Qed.
Lemma D_43bb0 : decode_any W_43bb0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_43bb4 : bv 32 := 0x00008067.
Lemma F_43bb4 : fetch_word Plain.M.loaded_segments (0x43bb4 : word) = Some W_43bb4.
Proof. vm_refl_bv. Qed.
Lemma D_43bb4 : decode_any W_43bb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma img_10040_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65600) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 6)).
Proof. vm_refl_bv. Qed.
Lemma img_10050_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 65616) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 65600)).
Proof. vm_refl_bv. Qed.
Lemma img_10078_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65656) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma img_100b0_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65712) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma img_100e8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65768) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma img_10120_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65824) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma img_10158_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65880) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382482)).
Proof. vm_refl_bv. Qed.
Lemma img_10190_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65936) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382480)).
Proof. vm_refl_bv. Qed.
Lemma img_101c8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65992) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382481)).
Proof. vm_refl_bv. Qed.
Lemma img_101f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 66032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_10200_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66048) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4)).
Proof. vm_refl_bv. Qed.
Lemma img_10238_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66104) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1879048195)).
Proof. vm_refl_bv. Qed.
Lemma img_48560_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 296288) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_49818_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 301080) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
Lemma img_799e0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 498144) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_799f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 498160) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_799f8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 498168) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_79c38_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 498744) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_79c60_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 498784) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_79c78_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 498808) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
End P_startup3_rc2.
Import P_startup3_rc2.

Section P4.
  Variable v : VaSize.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 brk : word.
  Variable rdraw : EntryDraw.
  Variable Jb : word -> option byte.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va v (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rdraw)) (only parsing).

  Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 244132 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w inp rdraw ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 498768 ->
getr regs 19 = Z_to_bv 64 0 ->
getr regs 20 = Z_to_bv 64 0 ->
getr regs 21 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 9 = (Z_to_bv 64 498768) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 498128) ->
getr regs' 13 = (Z_to_bv 64 10) ->
getr regs' 15 = (Z_to_bv 64 65600) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 65600) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
regs_agree (fun r => In r [2; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs' ->
G (mkst regs' (0x3bc3c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 244132))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 498768))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) ->
G (mkst regs (0x3bbb4 : word) (CM (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (D_libc sp0 inp rdraw)) rom)
(* [comment removed for export] *).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_3bbb4 D_3bbb4 (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* [comment removed for export] *)
      stw F_3bbb8 D_3bbb8 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 244132) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_3bbbc D_3bbbc (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w inp rdraw) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_3bbc0 D_3bbc0 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_3bbc4 D_3bbc4 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 498768) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_3bbc8 D_3bbc8 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_3bbcc D_3bbcc (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_3bbd0 D_3bbd0 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      ld_step F_3bbd4 D_3bbd4 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_3bbd8 D_3bbd8.  (* [comment removed for export] *)
      sn F_3bbdc D_3bbdc.  (* [comment removed for export] *)
      sn F_3bbe0 D_3bbe0.  (* [comment removed for export] *)
      sn F_3bbe4 D_3bbe4.  (* [comment removed for export] *)
      stepb_ft F_3bbe8 D_3bbe8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bbec D_3bbec.  (* [comment removed for export] *)
      sn F_3bbf0 D_3bbf0.  (* [comment removed for export] *)
      sn F_3bbf4 D_3bbf4.  (* [comment removed for export] *)
      ld_step F_3bbf8 D_3bbf8 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3bbfc D_3bbfc (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_3bc00 D_3bc00.  (* [comment removed for export] *)
      sn F_3bc04 D_3bc04.  (* [comment removed for export] *)
      ld_step F_3bc08 D_3bc08 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_49818_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      ld_step F_3bc0c D_3bc0c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_48560_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_3bc10 D_3bc10.  (* [comment removed for export] *)
      sn F_3bc14 D_3bc14.  (* [comment removed for export] *)
      sn F_3bc18 D_3bc18.  (* [comment removed for export] *)
      sn F_3bc1c D_3bc1c.  (* [comment removed for export] *)
      sn F_3bc20 D_3bc20.  (* [comment removed for export] *)
      sn F_3bc24 D_3bc24.  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 498768 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 498128 ->
getr regs 13 = Z_to_bv 64 10 ->
getr regs 15 = Z_to_bv 64 65600 ->
getr regs 16 = Z_to_bv 64 6 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
getr regs 28 = Z_to_bv 64 1685382481 ->
getr regs 29 = Z_to_bv 64 65600 ->
getr regs 30 = Z_to_bv 64 131072 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 9 = (Z_to_bv 64 498768) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 498128) ->
getr regs' 13 = (Z_to_bv 64 5) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 65880) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x3bc3c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 244132))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 498768))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) ->
G (mkst regs (0x3bc3c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 244132))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 498768))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)
(* [comment removed for export] *).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_3bc3c D_3bc3c (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_3bc40 D_3bc40 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_3bc28 D_3bc28 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_3bc2c D_3bc2c.  (* [comment removed for export] *)
      sn F_3bc30 D_3bc30.  (* [comment removed for export] *)
      sn F_3bc34 D_3bc34.  (* [comment removed for export] *)
      stepb_ft F_3bc38 D_3bc38 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_3bc3c D_3bc3c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_3bc40 D_3bc40 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_3bc44 D_3bc44 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc58 D_3bc58.  (* [comment removed for export] *)
      stepb_ft F_3bc5c D_3bc5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc60 D_3bc60.  (* [comment removed for export] *)
      stepb_tk F_3bc64 D_3bc64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc84 D_3bc84.  (* [comment removed for export] *)
      sn F_3bc88 D_3bc88.  (* [comment removed for export] *)
      sn F_3bc30 D_3bc30.  (* [comment removed for export] *)
      sn F_3bc34 D_3bc34.  (* [comment removed for export] *)
      stepb_ft F_3bc38 D_3bc38 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_3bc3c D_3bc3c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_3bc40 D_3bc40 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_3bc44 D_3bc44 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc58 D_3bc58.  (* [comment removed for export] *)
      stepb_ft F_3bc5c D_3bc5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc60 D_3bc60.  (* [comment removed for export] *)
      stepb_tk F_3bc64 D_3bc64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc84 D_3bc84.  (* [comment removed for export] *)
      sn F_3bc88 D_3bc88.  (* [comment removed for export] *)
      sn F_3bc30 D_3bc30.  (* [comment removed for export] *)
      sn F_3bc34 D_3bc34.  (* [comment removed for export] *)
      stepb_ft F_3bc38 D_3bc38 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_3bc3c D_3bc3c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_3bc40 D_3bc40 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_3bc44 D_3bc44 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc58 D_3bc58.  (* [comment removed for export] *)
      stepb_ft F_3bc5c D_3bc5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc60 D_3bc60.  (* [comment removed for export] *)
      stepb_tk F_3bc64 D_3bc64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc84 D_3bc84.  (* [comment removed for export] *)
      sn F_3bc88 D_3bc88.  (* [comment removed for export] *)
      sn F_3bc30 D_3bc30.  (* [comment removed for export] *)
      sn F_3bc34 D_3bc34.  (* [comment removed for export] *)
      stepb_ft F_3bc38 D_3bc38 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_3bc3c D_3bc3c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_3bc40 D_3bc40 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_3bc44 D_3bc44 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc58 D_3bc58.  (* [comment removed for export] *)
      stepb_ft F_3bc5c D_3bc5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc60 D_3bc60.  (* [comment removed for export] *)
      stepb_tk F_3bc64 D_3bc64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc84 D_3bc84.  (* [comment removed for export] *)
      sn F_3bc88 D_3bc88.  (* [comment removed for export] *)
      sn F_3bc30 D_3bc30.  (* [comment removed for export] *)
      sn F_3bc34 D_3bc34.  (* [comment removed for export] *)
      stepb_ft F_3bc38 D_3bc38 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 498768 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 498128 ->
getr regs 13 = Z_to_bv 64 5 ->
getr regs 16 = Z_to_bv 64 6 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
getr regs 28 = Z_to_bv 64 1685382481 ->
getr regs 29 = Z_to_bv 64 65880 ->
getr regs 30 = Z_to_bv 64 131072 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 9 = (Z_to_bv 64 498768) ->
getr regs' 11 = (Z_to_bv 64 498128) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x3bc8c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 244132))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 498768))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) ->
G (mkst regs (0x3bc3c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 244132))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 498768))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)
(* [comment removed for export] *).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_3bc3c D_3bc3c (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_3bc40 D_3bc40 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_3bc44 D_3bc44 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc58 D_3bc58.  (* [comment removed for export] *)
      stepb_ft F_3bc5c D_3bc5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc60 D_3bc60.  (* [comment removed for export] *)
      stepb_tk F_3bc64 D_3bc64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc84 D_3bc84.  (* [comment removed for export] *)
      sn F_3bc88 D_3bc88.  (* [comment removed for export] *)
      sn F_3bc30 D_3bc30.  (* [comment removed for export] *)
      sn F_3bc34 D_3bc34.  (* [comment removed for export] *)
      stepb_ft F_3bc38 D_3bc38 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_3bc3c D_3bc3c (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_3bc40 D_3bc40 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_3bc44 D_3bc44 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc58 D_3bc58.  (* [comment removed for export] *)
      stepb_ft F_3bc5c D_3bc5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc60 D_3bc60.  (* [comment removed for export] *)
      stepb_tk F_3bc64 D_3bc64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc84 D_3bc84.  (* [comment removed for export] *)
      sn F_3bc88 D_3bc88.  (* [comment removed for export] *)
      sn F_3bc30 D_3bc30.  (* [comment removed for export] *)
      sn F_3bc34 D_3bc34.  (* [comment removed for export] *)
      stepb_ft F_3bc38 D_3bc38 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_3bc3c D_3bc3c (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_3bc40 D_3bc40 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_3bc44 D_3bc44 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc58 D_3bc58.  (* [comment removed for export] *)
      stepb_ft F_3bc5c D_3bc5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc60 D_3bc60.  (* [comment removed for export] *)
      stepb_ft F_3bc64 D_3bc64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_3bc68 D_3bc68 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_3bc6c D_3bc6c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc84 D_3bc84.  (* [comment removed for export] *)
      sn F_3bc88 D_3bc88.  (* [comment removed for export] *)
      sn F_3bc30 D_3bc30.  (* [comment removed for export] *)
      sn F_3bc34 D_3bc34.  (* [comment removed for export] *)
      stepb_ft F_3bc38 D_3bc38 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_3bc3c D_3bc3c (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_3bc40 D_3bc40 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_3bc44 D_3bc44 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc58 D_3bc58.  (* [comment removed for export] *)
      stepb_ft F_3bc5c D_3bc5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc60 D_3bc60.  (* [comment removed for export] *)
      stepb_tk F_3bc64 D_3bc64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc84 D_3bc84.  (* [comment removed for export] *)
      sn F_3bc88 D_3bc88.  (* [comment removed for export] *)
      sn F_3bc30 D_3bc30.  (* [comment removed for export] *)
      sn F_3bc34 D_3bc34.  (* [comment removed for export] *)
      stepb_ft F_3bc38 D_3bc38 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_3bc3c D_3bc3c (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_3bc40 D_3bc40 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_3bc44 D_3bc44 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc58 D_3bc58.  (* [comment removed for export] *)
      stepb_ft F_3bc5c D_3bc5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc60 D_3bc60.  (* [comment removed for export] *)
      stepb_tk F_3bc64 D_3bc64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bc84 D_3bc84.  (* [comment removed for export] *)
      sn F_3bc88 D_3bc88.  (* [comment removed for export] *)
      sn F_3bc30 D_3bc30.  (* [comment removed for export] *)
      sn F_3bc34 D_3bc34.  (* [comment removed for export] *)
      stepb_tk F_3bc38 D_3bc38 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 498768 ->
getr regs 11 = Z_to_bv 64 498128 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 367048) ->
getr regs' 10 = (Z_to_bv 64 498128) ->
getr regs' 11 = (Z_to_bv 64 498824) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 366840) ->
getr regs' 14 = (Z_to_bv 64 0) ->
getr regs' 15 = (Z_to_bv 64 18446744073709184568) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 366848) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x3be10 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 244132))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 498768))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 498160) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 498176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 498168) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 498792) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 498800) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 367064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 367040) (word_to_le_bytes 8 (Z_to_bv 64 367064))) (Z_to_bv 64 366848) (word_to_le_bytes 8 (Z_to_bv 64 366848))) (Z_to_bv 64 498768) ([Z_to_bv 8 1])) (Z_to_bv 64 366888) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x3bc8c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 244132))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 498768))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)
(* [comment removed for export] *).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { (* [comment removed for export] *)
      stepb_tk F_3bc8c D_3bc8c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_3bcc4 D_3bcc4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_799e0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3bcc8 D_3bcc8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_799f0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3bccc D_3bccc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_799f8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_3bcd0 D_3bcd0.  (* [comment removed for export] *)
      sn F_3bcd4 D_3bcd4.  (* [comment removed for export] *)
      sn F_3bcd8 D_3bcd8.  (* [comment removed for export] *)
      sn F_3bcdc D_3bcdc.  (* [comment removed for export] *)
      sn F_3bce0 D_3bce0.  (* [comment removed for export] *)
      sn F_3bce4 D_3bce4.  (* [comment removed for export] *)
      sn F_3bce8 D_3bce8.  (* [comment removed for export] *)
      stw F_3bcec D_3bcec (Z_to_bv 64 498160) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3bcf0 D_3bcf0 (Z_to_bv 64 498176) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stepb_ft F_3bcf4 D_3bcf4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bcf8 D_3bcf8.  (* [comment removed for export] *)
      stw F_3bcfc D_3bcfc (Z_to_bv 64 498168) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_3bd00 D_3bd00.  (* [comment removed for export] *)
      sn F_3bd04 D_3bd04.  (* [comment removed for export] *)
      sn F_3bd08 D_3bd08.  (* [comment removed for export] *)
      sn F_3bd0c D_3bd0c.  (* [comment removed for export] *)
      sn F_3bd10 D_3bd10.  (* [comment removed for export] *)
      sn F_3bd14 D_3bd14.  (* [comment removed for export] *)
      stw F_3bd18 D_3bd18 (Z_to_bv 64 498792) (Z_to_bv 64 224) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3bd1c D_3bd1c (Z_to_bv 64 498800) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
      stepb_tk F_3bd20 D_3bd20 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bd54 D_3bd54.  (* [comment removed for export] *)
      ld_step F_3bd58 D_3bd58 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_79c60_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3bd5c D_3bd5c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_79c78_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_3bd60 D_3bd60.  (* [comment removed for export] *)
      sn F_3bd64 D_3bd64.  (* [comment removed for export] *)
      sn F_3bd68 D_3bd68.  (* [comment removed for export] *)
      sn F_3bd6c D_3bd6c.  (* [comment removed for export] *)
      sn F_3bd70 D_3bd70.  (* [comment removed for export] *)
      sn F_3bd74 D_3bd74.  (* [comment removed for export] *)
      sn F_3bd78 D_3bd78.  (* [comment removed for export] *)
      sn F_3bd7c D_3bd7c.  (* [comment removed for export] *)
      sn F_3bd80 D_3bd80.  (* [comment removed for export] *)
      sn F_3bd84 D_3bd84.  (* [comment removed for export] *)
      sn F_3bd88 D_3bd88.  (* [comment removed for export] *)
      stepb_tk F_3bd8c D_3bd8c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stw F_3bdd4 D_3bdd4 (Z_to_bv 64 367064) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3bdd8 D_3bdd8 (Z_to_bv 64 367040) (Z_to_bv 64 367064) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3bddc D_3bddc (Z_to_bv 64 366848) (Z_to_bv 64 366848) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_3bde0 D_3bde0.  (* [comment removed for export] *)
      sn F_3bde4 D_3bde4.  (* [comment removed for export] *)
      sn F_43bac D_43bac.  (* [comment removed for export] *)
      sn F_43bb0 D_43bb0.  (* [comment removed for export] *)
      stepret F_43bb4 D_43bb4 (0x3bde8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      stepb_ft F_3bde8 D_3bde8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_ft F_3bdec D_3bdec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bdf0 D_3bdf0.  (* [comment removed for export] *)
      stw F_3bdf4 D_3bdf4 (Z_to_bv 64 498768) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_3bdf8 D_3bdf8.  (* [comment removed for export] *)
      sn F_3bdfc D_3bdfc.  (* [comment removed for export] *)
      stw F_3be00 D_3be00 (Z_to_bv 64 366888) (Z_to_bv 64 2) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_3be04 D_3be04.  (* [comment removed for export] *)
      sn F_3be08 D_3be08.  (* [comment removed for export] *)
      sn F_3be0c D_3be0c.  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 367048 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 498824 ->
getr regs 18 = Z_to_bv 64 366848 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 367048) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 18; 19; 20; 21]%list) regs regs' ->
G (mkst regs' (0x3b9a4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 244132))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 498768))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 498160) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 498176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 498168) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 498792) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 498800) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 367064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 367040) (word_to_le_bytes 8 (Z_to_bv 64 367064))) (Z_to_bv 64 366848) (word_to_le_bytes 8 (Z_to_bv 64 366848))) (Z_to_bv 64 498768) ([Z_to_bv 8 1])) (Z_to_bv 64 366888) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 366880) (word_to_le_bytes 4 tid)) (Z_to_bv 64 367000) (word_to_le_bytes 8 (Z_to_bv 64 498824))) (Z_to_bv 64 366968) (word_to_le_bytes 8 (Z_to_bv 64 366968))) (Z_to_bv 64 366856) (word_to_le_bytes 8 (Z_to_bv 64 366848))) (Z_to_bv 64 366864) (word_to_le_bytes 8 (Z_to_bv 64 366848))) (Z_to_bv 64 366872) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x3be14 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 244132))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 498768))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 498160) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 498176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 498168) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 498792) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 498800) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 367064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 367040) (word_to_le_bytes 8 (Z_to_bv 64 367064))) (Z_to_bv 64 366848) (word_to_le_bytes 8 (Z_to_bv 64 366848))) (Z_to_bv 64 498768) ([Z_to_bv 8 1])) (Z_to_bv 64 366888) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)
(* [comment removed for export] *).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sn F_3be14 D_3be14.  (* [comment removed for export] *)
      stw F_3be18 D_3be18 (Z_to_bv 64 366880) tid ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3be1c D_3be1c (Z_to_bv 64 367000) (Z_to_bv 64 498824) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3be20 D_3be20 (Z_to_bv 64 366968) (Z_to_bv 64 366968) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_3be24 D_3be24.  (* [comment removed for export] *)
      ld_step F_3be28 D_3be28 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_79c38_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_3be2c D_3be2c (Z_to_bv 64 366856) (Z_to_bv 64 366848) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3be30 D_3be30 (Z_to_bv 64 366864) (Z_to_bv 64 366848) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3be34 D_3be34 (Z_to_bv 64 366872) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_3be38 D_3be38.  (* [comment removed for export] *)
      ld_step F_3be40 D_3be40 (word_to_le_bytes 8 (Z_to_bv 64 244132)) (Z_to_bv 64 244132) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3be44 D_3be44 (word_to_le_bytes 8 (pn_w inp rdraw)) (pn_w inp rdraw) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3be48 D_3be48 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3be4c D_3be4c (word_to_le_bytes 8 (Z_to_bv 64 498768)) (Z_to_bv 64 498768) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3be50 D_3be50 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3be54 D_3be54 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3be58 D_3be58 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_3be5c D_3be5c (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_3be60 D_3be60 (0x3b9a4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
