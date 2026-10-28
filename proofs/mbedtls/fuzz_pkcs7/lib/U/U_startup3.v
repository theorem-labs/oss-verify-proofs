(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StartupTac ArgvEnv Layout.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_img U_startup_defs.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_startup3 () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.BB.StartupTac.bwd"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BB.MemSplit.wfJ"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.U.U_startup_defs.pn_w"; "RocqVerifyHarness.AgentSubmission.BB.Hoare.regs_agree"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.BB.MemSplit.cmem"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.wrap_mem"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.phdrs"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "RocqVerifyHarness.AgentSubmission.U.U_startup_defs.J_aux"; "RocqVerifyHarness.AgentSubmission.U.U_startup_defs.J_lsm"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "RocqVerifyHarness.AgentSubmission.U.U_startup_defs.D_libc"].


Module U_startup3_rc2.
Definition W_3bbb4 : bv 32 := 0xfc010113.
Lemma F_3bbb4 : fetch_word Ubsan.M.loaded_segments (0x3f2ac : word) = Some W_3bbb4.
Proof. vm_refl_bv. Qed.
Lemma D_3bbb4 : decode_any W_3bbb4 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbb8 : bv 32 := 0x02113c23.
Lemma F_3bbb8 : fetch_word Ubsan.M.loaded_segments (0x3f2b0 : word) = Some W_3bbb8.
Proof. vm_refl_bv. Qed.
Lemma D_3bbb8 : decode_any W_3bbb8 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbbc : bv 32 := 0x02813823.
Lemma F_3bbbc : fetch_word Ubsan.M.loaded_segments (0x3f2b4 : word) = Some W_3bbbc.
Proof. vm_refl_bv. Qed.
Lemma D_3bbbc : decode_any W_3bbbc = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbc0 : bv 32 := 0x02913423.
Lemma F_3bbc0 : fetch_word Ubsan.M.loaded_segments (0x3f2b8 : word) = Some W_3bbc0.
Proof. vm_refl_bv. Qed.
Lemma D_3bbc0 : decode_any W_3bbc0 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbc4 : bv 32 := 0x03213023.
Lemma F_3bbc4 : fetch_word Ubsan.M.loaded_segments (0x3f2bc : word) = Some W_3bbc4.
Proof. vm_refl_bv. Qed.
Lemma D_3bbc4 : decode_any W_3bbc4 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbc8 : bv 32 := 0x01313c23.
Lemma F_3bbc8 : fetch_word Ubsan.M.loaded_segments (0x3f2c0 : word) = Some W_3bbc8.
Proof. vm_refl_bv. Qed.
Lemma D_3bbc8 : decode_any W_3bbc8 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbcc : bv 32 := 0x01413823.
Lemma F_3bbcc : fetch_word Ubsan.M.loaded_segments (0x3f2c4 : word) = Some W_3bbcc.
Proof. vm_refl_bv. Qed.
Lemma D_3bbcc : decode_any W_3bbcc = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbd0 : bv 32 := 0x01513423.
Lemma F_3bbd0 : fetch_word Ubsan.M.loaded_segments (0x3f2c8 : word) = Some W_3bbd0.
Proof. vm_refl_bv. Qed.
Lemma D_3bbd0 : decode_any W_3bbd0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbd4 : bv 32 := 0x02853683.
Lemma F_3bbd4 : fetch_word Ubsan.M.loaded_segments (0x3f2cc : word) = Some W_3bbd4.
Proof. vm_refl_bv. Qed.
Lemma D_3bbd4 : decode_any W_3bbd4 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbd8 : bv 32 := 0x0003e597.
Lemma F_3bbd8 : fetch_word Ubsan.M.loaded_segments (0x3f2d0 : word) = Some W_3bbd8.
Proof. vm_refl_bv. Qed.
Lemma D_3bbd8 : decode_any W_3bbd8 = Some (Auipc 11 62, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbdc : bv 32 := 0xe0058593.
Lemma F_3bbdc : fetch_word Ubsan.M.loaded_segments (0x3f2d4 : word) = Some W_3bbdc.
Proof. vm_refl_bv. Qed.
Lemma D_3bbdc : decode_any W_3bbdc = Some (OpImm ALU_ADD 11 11 3584, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbe0 : bv 32 := 0x0003e617.
Lemma F_3bbe0 : fetch_word Ubsan.M.loaded_segments (0x3f2d8 : word) = Some W_3bbe0.
Proof. vm_refl_bv. Qed.
Lemma D_3bbe0 : decode_any W_3bbe0 = Some (Auipc 12 62, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbe4 : bv 32 := 0x07860493.
Lemma F_3bbe4 : fetch_word Ubsan.M.loaded_segments (0x3f2dc : word) = Some W_3bbe4.
Proof. vm_refl_bv. Qed.
Lemma D_3bbe4 : decode_any W_3bbe4 = Some (OpImm ALU_ADD 9 12 120, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbe8 : bv 32 := 0x0c068e63.
Lemma F_3bbe8 : fetch_word Ubsan.M.loaded_segments (0x3f2e0 : word) = Some W_3bbe8.
Proof. vm_refl_bv. Qed.
Lemma D_3bbe8 : decode_any W_3bbe8 = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbec : bv 32 := 0x00000613.
Lemma F_3bbec : fetch_word Ubsan.M.loaded_segments (0x3f2e4 : word) = Some W_3bbec.
Proof. vm_refl_bv. Qed.
Lemma D_3bbec : decode_any W_3bbec = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbf0 : bv 32 := 0x00000893.
Lemma F_3bbf0 : fetch_word Ubsan.M.loaded_segments (0x3f2e8 : word) = Some W_3bbf0.
Proof. vm_refl_bv. Qed.
Lemma D_3bbf0 : decode_any W_3bbf0 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbf4 : bv 32 := 0x0000e717.
Lemma F_3bbf4 : fetch_word Ubsan.M.loaded_segments (0x3f2ec : word) = Some W_3bbf4.
Proof. vm_refl_bv. Qed.
Lemma D_3bbf4 : decode_any W_3bbf4 = Some (Auipc 14 14, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbf8 : bv 32 := 0x01853783.
Lemma F_3bbf8 : fetch_word Ubsan.M.loaded_segments (0x3f2f0 : word) = Some W_3bbf8.
Proof. vm_refl_bv. Qed.
Lemma D_3bbf8 : decode_any W_3bbf8 = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bbfc : bv 32 := 0x02053503.
Lemma F_3bbfc : fetch_word Ubsan.M.loaded_segments (0x3f2f4 : word) = Some W_3bbfc.
Proof. vm_refl_bv. Qed.
Lemma D_3bbfc : decode_any W_3bbfc = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc00 : bv 32 := 0x00600813.
Lemma F_3bc00 : fetch_word Ubsan.M.loaded_segments (0x3f2f8 : word) = Some W_3bc00.
Proof. vm_refl_bv. Qed.
Lemma D_3bc00 : decode_any W_3bc00 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc04 : bv 32 := 0x0000d297.
Lemma F_3bc04 : fetch_word Ubsan.M.loaded_segments (0x3f2fc : word) = Some W_3bc04.
Proof. vm_refl_bv. Qed.
Lemma D_3bc04 : decode_any W_3bc04 = Some (Auipc 5 13, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc08 : bv 32 := 0xc2476f03.
Lemma F_3bc08 : fetch_word Ubsan.M.loaded_segments (0x3f300 : word) = Some W_3bc08.
Proof. vm_refl_bv. Qed.
Lemma D_3bc08 : decode_any W_3bc08 = Some (Load SZ4 false 30 14 3108, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc0c : bv 32 := 0x95c2b283.
Lemma F_3bc0c : fetch_word Ubsan.M.loaded_segments (0x3f304 : word) = Some W_3bc0c.
Proof. vm_refl_bv. Qed.
Lemma D_3bc0c : decode_any W_3bc0c = Some (Load SZ8 true 5 5 2396, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc10 : bv 32 := 0x00200313.
Lemma F_3bc10 : fetch_word Ubsan.M.loaded_segments (0x3f308 : word) = Some W_3bc10.
Proof. vm_refl_bv. Qed.
Lemma D_3bc10 : decode_any W_3bc10 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc14 : bv 32 := 0x00700393.
Lemma F_3bc14 : fetch_word Ubsan.M.loaded_segments (0x3f30c : word) = Some W_3bc14.
Proof. vm_refl_bv. Qed.
Lemma D_3bc14 : decode_any W_3bc14 = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc18 : bv 32 := 0x6474ee37.
Lemma F_3bc18 : fetch_word Ubsan.M.loaded_segments (0x3f310 : word) = Some W_3bc18.
Proof. vm_refl_bv. Qed.
Lemma D_3bc18 : decode_any W_3bc18 = Some (Lui 28 411470, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc1c : bv 32 := 0x551e0e1b.
Lemma F_3bc1c : fetch_word Ubsan.M.loaded_segments (0x3f314 : word) = Some W_3bc1c.
Proof. vm_refl_bv. Qed.
Lemma D_3bc1c : decode_any W_3bc1c = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc20 : bv 32 := 0x00078e93.
Lemma F_3bc20 : fetch_word Ubsan.M.loaded_segments (0x3f318 : word) = Some W_3bc20.
Proof. vm_refl_bv. Qed.
Lemma D_3bc20 : decode_any W_3bc20 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc24 : bv 32 := 0x0180006f.
Lemma F_3bc24 : fetch_word Ubsan.M.loaded_segments (0x3f31c : word) = Some W_3bc24.
Proof. vm_refl_bv. Qed.
Lemma D_3bc24 : decode_any W_3bc24 = Some (Jal 0 24, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc28 : bv 32 := 0x010eb603.
Lemma F_3bc28 : fetch_word Ubsan.M.loaded_segments (0x3f320 : word) = Some W_3bc28.
Proof. vm_refl_bv. Qed.
Lemma D_3bc28 : decode_any W_3bc28 = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc2c : bv 32 := 0x40c78633.
Lemma F_3bc2c : fetch_word Ubsan.M.loaded_segments (0x3f324 : word) = Some W_3bc2c.
Proof. vm_refl_bv. Qed.
Lemma D_3bc2c : decode_any W_3bc2c = Some (Op ALU_SUB 12 15 12, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc30 : bv 32 := 0xfff68693.
Lemma F_3bc30 : fetch_word Ubsan.M.loaded_segments (0x3f328 : word) = Some W_3bc30.
Proof. vm_refl_bv. Qed.
Lemma D_3bc30 : decode_any W_3bc30 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc34 : bv 32 := 0x00ae8eb3.
Lemma F_3bc34 : fetch_word Ubsan.M.loaded_segments (0x3f32c : word) = Some W_3bc34.
Proof. vm_refl_bv. Qed.
Lemma D_3bc34 : decode_any W_3bc34 = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc38 : bv 32 := 0x04068a63.
Lemma F_3bc38 : fetch_word Ubsan.M.loaded_segments (0x3f330 : word) = Some W_3bc38.
Proof. vm_refl_bv. Qed.
Lemma D_3bc38 : decode_any W_3bc38 = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc3c : bv 32 := 0x000ea403.
Lemma F_3bc3c : fetch_word Ubsan.M.loaded_segments (0x3f334 : word) = Some W_3bc3c.
Proof. vm_refl_bv. Qed.
Lemma D_3bc3c : decode_any W_3bc3c = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc40 : bv 32 := 0xff0404e3.
Lemma F_3bc40 : fetch_word Ubsan.M.loaded_segments (0x3f338 : word) = Some W_3bc40.
Proof. vm_refl_bv. Qed.
Lemma D_3bc40 : decode_any W_3bc40 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc44 : bv 32 := 0x00028a63.
Lemma F_3bc44 : fetch_word Ubsan.M.loaded_segments (0x3f33c : word) = Some W_3bc44.
Proof. vm_refl_bv. Qed.
Lemma D_3bc44 : decode_any W_3bc44 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc58 : bv 32 := 0x000e8f93.
Lemma F_3bc58 : fetch_word Ubsan.M.loaded_segments (0x3f350 : word) = Some W_3bc58.
Proof. vm_refl_bv. Qed.
Lemma D_3bc58 : decode_any W_3bc58 = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc5c : bv 32 := 0x00740463.
Lemma F_3bc5c : fetch_word Ubsan.M.loaded_segments (0x3f354 : word) = Some W_3bc5c.
Proof. vm_refl_bv. Qed.
Lemma D_3bc5c : decode_any W_3bc5c = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc60 : bv 32 := 0x00088f93.
Lemma F_3bc60 : fetch_word Ubsan.M.loaded_segments (0x3f358 : word) = Some W_3bc60.
Proof. vm_refl_bv. Qed.
Lemma D_3bc60 : decode_any W_3bc60 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc64 : bv 32 := 0x03c41063.
Lemma F_3bc64 : fetch_word Ubsan.M.loaded_segments (0x3f35c : word) = Some W_3bc64.
Proof. vm_refl_bv. Qed.
Lemma D_3bc64 : decode_any W_3bc64 = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc68 : bv 32 := 0x028eb883.
Lemma F_3bc68 : fetch_word Ubsan.M.loaded_segments (0x3f360 : word) = Some W_3bc68.
Proof. vm_refl_bv. Qed.
Lemma D_3bc68 : decode_any W_3bc68 = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc6c : bv 32 := 0x011f7c63.
Lemma F_3bc6c : fetch_word Ubsan.M.loaded_segments (0x3f364 : word) = Some W_3bc6c.
Proof. vm_refl_bv. Qed.
Lemma D_3bc6c : decode_any W_3bc6c = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc84 : bv 32 := 0x000f8893.
Lemma F_3bc84 : fetch_word Ubsan.M.loaded_segments (0x3f37c : word) = Some W_3bc84.
Proof. vm_refl_bv. Qed.
Lemma D_3bc84 : decode_any W_3bc84 = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc88 : bv 32 := 0xfa9ff06f.
Lemma F_3bc88 : fetch_word Ubsan.M.loaded_segments (0x3f380 : word) = Some W_3bc88.
Proof. vm_refl_bv. Qed.
Lemma D_3bc88 : decode_any W_3bc88 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bc8c : bv 32 := 0x02088c63.
Lemma F_3bc8c : fetch_word Ubsan.M.loaded_segments (0x3f384 : word) = Some W_3bc8c.
Proof. vm_refl_bv. Qed.
Lemma D_3bc8c : decode_any W_3bc8c = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcc4 : bv 32 := 0x0105b603.
Lemma F_3bcc4 : fetch_word Ubsan.M.loaded_segments (0x3f3bc : word) = Some W_3bcc4.
Proof. vm_refl_bv. Qed.
Lemma D_3bcc4 : decode_any W_3bcc4 = Some (Load SZ8 true 12 11 16, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcc8 : bv 32 := 0x0205b683.
Lemma F_3bcc8 : fetch_word Ubsan.M.loaded_segments (0x3f3c0 : word) = Some W_3bcc8.
Proof. vm_refl_bv. Qed.
Lemma D_3bcc8 : decode_any W_3bcc8 = Some (Load SZ8 true 13 11 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bccc : bv 32 := 0x0285b503.
Lemma F_3bccc : fetch_word Ubsan.M.loaded_segments (0x3f3c4 : word) = Some W_3bccc.
Proof. vm_refl_bv. Qed.
Lemma D_3bccc : decode_any W_3bccc = Some (Load SZ8 true 10 11 40, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcd0 : bv 32 := 0x00c68733.
Lemma F_3bcd0 : fetch_word Ubsan.M.loaded_segments (0x3f3c8 : word) = Some W_3bcd0.
Proof. vm_refl_bv. Qed.
Lemma D_3bcd0 : decode_any W_3bcd0 = Some (Op ALU_ADD 14 13 12, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcd4 : bv 32 := 0xfff50793.
Lemma F_3bcd4 : fetch_word Ubsan.M.loaded_segments (0x3f3cc : word) = Some W_3bcd4.
Proof. vm_refl_bv. Qed.
Lemma D_3bcd4 : decode_any W_3bcd4 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcd8 : bv 32 := 0x40e00733.
Lemma F_3bcd8 : fetch_word Ubsan.M.loaded_segments (0x3f3d0 : word) = Some W_3bcd8.
Proof. vm_refl_bv. Qed.
Lemma D_3bcd8 : decode_any W_3bcd8 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcdc : bv 32 := 0x00c7f633.
Lemma F_3bcdc : fetch_word Ubsan.M.loaded_segments (0x3f3d4 : word) = Some W_3bcdc.
Proof. vm_refl_bv. Qed.
Lemma D_3bcdc : decode_any W_3bcdc = Some (Op ALU_AND 12 15 12, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bce0 : bv 32 := 0x00e7f733.
Lemma F_3bce0 : fetch_word Ubsan.M.loaded_segments (0x3f3d8 : word) = Some W_3bce0.
Proof. vm_refl_bv. Qed.
Lemma D_3bce0 : decode_any W_3bce0 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bce4 : bv 32 := 0x00700793.
Lemma F_3bce4 : fetch_word Ubsan.M.loaded_segments (0x3f3dc : word) = Some W_3bce4.
Proof. vm_refl_bv. Qed.
Lemma D_3bce4 : decode_any W_3bce4 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bce8 : bv 32 := 0x00d706b3.
Lemma F_3bce8 : fetch_word Ubsan.M.loaded_segments (0x3f3e0 : word) = Some W_3bce8.
Proof. vm_refl_bv. Qed.
Lemma D_3bce8 : decode_any W_3bce8 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcec : bv 32 := 0x02d5b023.
Lemma F_3bcec : fetch_word Ubsan.M.loaded_segments (0x3f3e4 : word) = Some W_3bcec.
Proof. vm_refl_bv. Qed.
Lemma D_3bcec : decode_any W_3bcec = Some (Store SZ8 11 13 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcf0 : bv 32 := 0x02c5b823.
Lemma F_3bcf0 : fetch_word Ubsan.M.loaded_segments (0x3f3e8 : word) = Some W_3bcf0.
Proof. vm_refl_bv. Qed.
Lemma D_3bcf0 : decode_any W_3bcf0 = Some (Store SZ8 11 12 48, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcf4 : bv 32 := 0x00a7e663.
Lemma F_3bcf4 : fetch_word Ubsan.M.loaded_segments (0x3f3ec : word) = Some W_3bcf4.
Proof. vm_refl_bv. Qed.
Lemma D_3bcf4 : decode_any W_3bcf4 = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcf8 : bv 32 := 0x00800513.
Lemma F_3bcf8 : fetch_word Ubsan.M.loaded_segments (0x3f3f0 : word) = Some W_3bcf8.
Proof. vm_refl_bv. Qed.
Lemma D_3bcf8 : decode_any W_3bcf8 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bcfc : bv 32 := 0x02a5b423.
Lemma F_3bcfc : fetch_word Ubsan.M.loaded_segments (0x3f3f4 : word) = Some W_3bcfc.
Proof. vm_refl_bv. Qed.
Lemma D_3bcfc : decode_any W_3bcfc = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd00 : bv 32 := 0x00d60633.
Lemma F_3bd00 : fetch_word Ubsan.M.loaded_segments (0x3f3f8 : word) = Some W_3bd00.
Proof. vm_refl_bv. Qed.
Lemma D_3bd00 : decode_any W_3bd00 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd04 : bv 32 := 0x000205b7.
Lemma F_3bd04 : fetch_word Ubsan.M.loaded_segments (0x3f3fc : word) = Some W_3bd04.
Proof. vm_refl_bv. Qed.
Lemma D_3bd04 : decode_any W_3bd04 = Some (Lui 11 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd08 : bv 32 := 0x00a60633.
Lemma F_3bd08 : fetch_word Ubsan.M.loaded_segments (0x3f400 : word) = Some W_3bd08.
Proof. vm_refl_bv. Qed.
Lemma D_3bd08 : decode_any W_3bd08 = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd0c : bv 32 := 0x0d15869b.
Lemma F_3bd0c : fetch_word Ubsan.M.loaded_segments (0x3f404 : word) = Some W_3bd0c.
Proof. vm_refl_bv. Qed.
Lemma D_3bd0c : decode_any W_3bd0c = Some (OpImm32 13 11 209, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd10 : bv 32 := 0x0df60593.
Lemma F_3bd10 : fetch_word Ubsan.M.loaded_segments (0x3f408 : word) = Some W_3bd10.
Proof. vm_refl_bv. Qed.
Lemma D_3bd10 : decode_any W_3bd10 = Some (OpImm ALU_ADD 11 12 223, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd14 : bv 32 := 0xff85f593.
Lemma F_3bd14 : fetch_word Ubsan.M.loaded_segments (0x3f40c : word) = Some W_3bd14.
Proof. vm_refl_bv. Qed.
Lemma D_3bd14 : decode_any W_3bd14 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd18 : bv 32 := 0x00b4bc23.
Lemma F_3bd18 : fetch_word Ubsan.M.loaded_segments (0x3f410 : word) = Some W_3bd18.
Proof. vm_refl_bv. Qed.
Lemma D_3bd18 : decode_any W_3bd18 = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd1c : bv 32 := 0x02a4b023.
Lemma F_3bd1c : fetch_word Ubsan.M.loaded_segments (0x3f414 : word) = Some W_3bd1c.
Proof. vm_refl_bv. Qed.
Lemma D_3bd1c : decode_any W_3bd1c = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd20 : bv 32 := 0x02d5ea63.
Lemma F_3bd20 : fetch_word Ubsan.M.loaded_segments (0x3f418 : word) = Some W_3bd20.
Proof. vm_refl_bv. Qed.
Lemma D_3bd20 : decode_any W_3bd20 = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd54 : bv 32 := 0x0001e697.
Lemma F_3bd54 : fetch_word Ubsan.M.loaded_segments (0x3f44c : word) = Some W_3bd54.
Proof. vm_refl_bv. Qed.
Lemma D_3bd54 : decode_any W_3bd54 = Some (Auipc 13 30, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd58 : bv 32 := 0x0104b983.
Lemma F_3bd58 : fetch_word Ubsan.M.loaded_segments (0x3f450 : word) = Some W_3bd58.
Proof. vm_refl_bv. Qed.
Lemma D_3bd58 : decode_any W_3bd58 = Some (Load SZ8 true 19 9 16, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd5c : bv 32 := 0x0284b603.
Lemma F_3bd5c : fetch_word Ubsan.M.loaded_segments (0x3f454 : word) = Some W_3bd5c.
Proof. vm_refl_bv. Qed.
Lemma D_3bd5c : decode_any W_3bd5c = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd60 : bv 32 := 0xfff50713.
Lemma F_3bd60 : fetch_word Ubsan.M.loaded_segments (0x3f458 : word) = Some W_3bd60.
Proof. vm_refl_bv. Qed.
Lemma D_3bd60 : decode_any W_3bd60 = Some (OpImm ALU_ADD 14 10 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd64 : bv 32 := 0xf3800793.
Lemma F_3bd64 : fetch_word Ubsan.M.loaded_segments (0x3f45c : word) = Some W_3bd64.
Proof. vm_refl_bv. Qed.
Lemma D_3bd64 : decode_any W_3bd64 = Some (OpImm ALU_ADD 15 0 3896, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd68 : bv 32 := 0xbb468513.
Lemma F_3bd68 : fetch_word Ubsan.M.loaded_segments (0x3f460 : word) = Some W_3bd68.
Proof. vm_refl_bv. Qed.
Lemma D_3bd68 : decode_any W_3bd68 = Some (OpImm ALU_ADD 10 13 2996, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd6c : bv 32 := 0x40a787b3.
Lemma F_3bd6c : fetch_word Ubsan.M.loaded_segments (0x3f464 : word) = Some W_3bd6c.
Proof. vm_refl_bv. Qed.
Lemma D_3bd6c : decode_any W_3bd6c = Some (Op ALU_SUB 15 15 10, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd70 : bv 32 := 0x00f77733.
Lemma F_3bd70 : fetch_word Ubsan.M.loaded_segments (0x3f468 : word) = Some W_3bd70.
Proof. vm_refl_bv. Qed.
Lemma D_3bd70 : decode_any W_3bd70 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd74 : bv 32 := 0xfff64693.
Lemma F_3bd74 : fetch_word Ubsan.M.loaded_segments (0x3f46c : word) = Some W_3bd74.
Proof. vm_refl_bv. Qed.
Lemma D_3bd74 : decode_any W_3bd74 = Some (OpImm ALU_XOR 13 12 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd78 : bv 32 := 0x00e50933.
Lemma F_3bd78 : fetch_word Ubsan.M.loaded_segments (0x3f470 : word) = Some W_3bd78.
Proof. vm_refl_bv. Qed.
Lemma D_3bd78 : decode_any W_3bd78 = Some (Op ALU_ADD 18 10 14, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd7c : bv 32 := 0x00369693.
Lemma F_3bd7c : fetch_word Ubsan.M.loaded_segments (0x3f474 : word) = Some W_3bd7c.
Proof. vm_refl_bv. Qed.
Lemma D_3bd7c : decode_any W_3bd7c = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd80 : bv 32 := 0x00d506b3.
Lemma F_3bd80 : fetch_word Ubsan.M.loaded_segments (0x3f478 : word) = Some W_3bd80.
Proof. vm_refl_bv. Qed.
Lemma D_3bd80 : decode_any W_3bd80 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd84 : bv 32 := 0x00b68a33.
Lemma F_3bd84 : fetch_word Ubsan.M.loaded_segments (0x3f47c : word) = Some W_3bd84.
Proof. vm_refl_bv. Qed.
Lemma D_3bd84 : decode_any W_3bd84 = Some (Op ALU_ADD 20 13 11, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd88 : bv 32 := 0x0c890413.
Lemma F_3bd88 : fetch_word Ubsan.M.loaded_segments (0x3f480 : word) = Some W_3bd88.
Proof. vm_refl_bv. Qed.
Lemma D_3bd88 : decode_any W_3bd88 = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bd8c : bv 32 := 0x04098463.
Lemma F_3bd8c : fetch_word Ubsan.M.loaded_segments (0x3f484 : word) = Some W_3bd8c.
Proof. vm_refl_bv. Qed.
Lemma D_3bd8c : decode_any W_3bd8c = Some (Branch BC_EQ 19 0 72, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bdd4 : bv 32 := 0x00ca3023.
Lemma F_3bdd4 : fetch_word Ubsan.M.loaded_segments (0x3f4cc : word) = Some W_3bdd4.
Proof. vm_refl_bv. Qed.
Lemma D_3bdd4 : decode_any W_3bdd4 = Some (Store SZ8 20 12 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bdd8 : bv 32 := 0x0d493023.
Lemma F_3bdd8 : fetch_word Ubsan.M.loaded_segments (0x3f4d0 : word) = Some W_3bdd8.
Proof. vm_refl_bv. Qed.
Lemma D_3bdd8 : decode_any W_3bdd8 = Some (Store SZ8 18 20 192, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bddc : bv 32 := 0x01293023.
Lemma F_3bddc : fetch_word Ubsan.M.loaded_segments (0x3f4d4 : word) = Some W_3bddc.
Proof. vm_refl_bv. Qed.
Lemma D_3bddc : decode_any W_3bddc = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bde0 : bv 32 := 0x00040513.
Lemma F_3bde0 : fetch_word Ubsan.M.loaded_segments (0x3f4d8 : word) = Some W_3bde0.
Proof. vm_refl_bv. Qed.
Lemma D_3bde0 : decode_any W_3bde0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bde4 : bv 32 := 0x5c9070ef.
Lemma F_3bde4 : fetch_word Ubsan.M.loaded_segments (0x3f4dc : word) = Some W_3bde4.
Proof. vm_refl_bv. Qed.
Lemma D_3bde4 : decode_any W_3bde4 = Some (Jal 1 32200, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bde8 : bv 32 := 0x04054a63.
Lemma F_3bde8 : fetch_word Ubsan.M.loaded_segments (0x3f4e0 : word) = Some W_3bde8.
Proof. vm_refl_bv. Qed.
Lemma D_3bde8 : decode_any W_3bde8 = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bdec : bv 32 := 0x00051663.
Lemma F_3bdec : fetch_word Ubsan.M.loaded_segments (0x3f4e4 : word) = Some W_3bdec.
Proof. vm_refl_bv. Qed.
Lemma D_3bdec : decode_any W_3bdec = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bdf0 : bv 32 := 0x00100513.
Lemma F_3bdf0 : fetch_word Ubsan.M.loaded_segments (0x3f4e8 : word) = Some W_3bdf0.
Proof. vm_refl_bv. Qed.
Lemma D_3bdf0 : decode_any W_3bdf0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bdf4 : bv 32 := 0x00a48023.
Lemma F_3bdf4 : fetch_word Ubsan.M.loaded_segments (0x3f4ec : word) = Some W_3bdf4.
Proof. vm_refl_bv. Qed.
Lemma D_3bdf4 : decode_any W_3bdf4 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bdf8 : bv 32 := 0x00200513.
Lemma F_3bdf8 : fetch_word Ubsan.M.loaded_segments (0x3f4f0 : word) = Some W_3bdf8.
Proof. vm_refl_bv. Qed.
Lemma D_3bdf8 : decode_any W_3bdf8 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3bdfc : bv 32 := 0x0003e597.
Lemma F_3bdfc : fetch_word Ubsan.M.loaded_segments (0x3f4f4 : word) = Some W_3bdfc.
Proof. vm_refl_bv. Qed.
Lemma D_3bdfc : decode_any W_3bdfc = Some (Auipc 11 62, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be00 : bv 32 := 0x02a92423.
Lemma F_3be00 : fetch_word Ubsan.M.loaded_segments (0x3f4f8 : word) = Some W_3be00.
Proof. vm_refl_bv. Qed.
Lemma D_3be00 : decode_any W_3be00 = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be04 : bv 32 := 0x06000893.
Lemma F_3be04 : fetch_word Ubsan.M.loaded_segments (0x3f4fc : word) = Some W_3be04.
Proof. vm_refl_bv. Qed.
Lemma D_3be04 : decode_any W_3be04 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be08 : bv 32 := 0xbdc58513.
Lemma F_3be08 : fetch_word Ubsan.M.loaded_segments (0x3f500 : word) = Some W_3be08.
Proof. vm_refl_bv. Qed.
Lemma D_3be08 : decode_any W_3be08 = Some (OpImm ALU_ADD 10 11 3036, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be0c : bv 32 := 0x03848593.
Lemma F_3be0c : fetch_word Ubsan.M.loaded_segments (0x3f504 : word) = Some W_3be0c.
Proof. vm_refl_bv. Qed.
Lemma D_3be0c : decode_any W_3be0c = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be10 : bv 32 := 0x00000073.
Lemma F_3be10 : fetch_word Ubsan.M.loaded_segments (0x3f508 : word) = Some W_3be10.
Proof. vm_refl_bv. Qed.
Lemma E_3be10 : is_ecall W_3be10 = true.
Proof. reflexivity. Qed.
Definition W_3be14 : bv 32 := 0x07890613.
Lemma F_3be14 : fetch_word Ubsan.M.loaded_segments (0x3f50c : word) = Some W_3be14.
Proof. vm_refl_bv. Qed.
Lemma D_3be14 : decode_any W_3be14 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be18 : bv 32 := 0x02a92023.
Lemma F_3be18 : fetch_word Ubsan.M.loaded_segments (0x3f510 : word) = Some W_3be18.
Proof. vm_refl_bv. Qed.
Lemma D_3be18 : decode_any W_3be18 = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be1c : bv 32 := 0x08b93c23.
Lemma F_3be1c : fetch_word Ubsan.M.loaded_segments (0x3f514 : word) = Some W_3be1c.
Proof. vm_refl_bv. Qed.
Lemma D_3be1c : decode_any W_3be1c = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be20 : bv 32 := 0x06c93c23.
Lemma F_3be20 : fetch_word Ubsan.M.loaded_segments (0x3f518 : word) = Some W_3be20.
Proof. vm_refl_bv. Qed.
Lemma D_3be20 : decode_any W_3be20 = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be24 : bv 32 := 0x0003e517.
Lemma F_3be24 : fetch_word Ubsan.M.loaded_segments (0x3f51c : word) = Some W_3be24.
Proof. vm_refl_bv. Qed.
Lemma D_3be24 : decode_any W_3be24 = Some (Auipc 10 62, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be28 : bv 32 := 0xe1c53503.
Lemma F_3be28 : fetch_word Ubsan.M.loaded_segments (0x3f520 : word) = Some W_3be28.
Proof. vm_refl_bv. Qed.
Lemma D_3be28 : decode_any W_3be28 = Some (Load SZ8 true 10 10 3612, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be2c : bv 32 := 0x01293423.
Lemma F_3be2c : fetch_word Ubsan.M.loaded_segments (0x3f524 : word) = Some W_3be2c.
Proof. vm_refl_bv. Qed.
Lemma D_3be2c : decode_any W_3be2c = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be30 : bv 32 := 0x01293823.
Lemma F_3be30 : fetch_word Ubsan.M.loaded_segments (0x3f528 : word) = Some W_3be30.
Proof. vm_refl_bv. Qed.
Lemma D_3be30 : decode_any W_3be30 = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be34 : bv 32 := 0x00a93c23.
Lemma F_3be34 : fetch_word Ubsan.M.loaded_segments (0x3f52c : word) = Some W_3be34.
Proof. vm_refl_bv. Qed.
Lemma D_3be34 : decode_any W_3be34 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be38 : bv 32 := 0x0080006f.
Lemma F_3be38 : fetch_word Ubsan.M.loaded_segments (0x3f530 : word) = Some W_3be38.
Proof. vm_refl_bv. Qed.
Lemma D_3be38 : decode_any W_3be38 = Some (Jal 0 8, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be40 : bv 32 := 0x03813083.
Lemma F_3be40 : fetch_word Ubsan.M.loaded_segments (0x3f538 : word) = Some W_3be40.
Proof. vm_refl_bv. Qed.
Lemma D_3be40 : decode_any W_3be40 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be44 : bv 32 := 0x03013403.
Lemma F_3be44 : fetch_word Ubsan.M.loaded_segments (0x3f53c : word) = Some W_3be44.
Proof. vm_refl_bv. Qed.
Lemma D_3be44 : decode_any W_3be44 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be48 : bv 32 := 0x02813483.
Lemma F_3be48 : fetch_word Ubsan.M.loaded_segments (0x3f540 : word) = Some W_3be48.
Proof. vm_refl_bv. Qed.
Lemma D_3be48 : decode_any W_3be48 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be4c : bv 32 := 0x02013903.
Lemma F_3be4c : fetch_word Ubsan.M.loaded_segments (0x3f544 : word) = Some W_3be4c.
Proof. vm_refl_bv. Qed.
Lemma D_3be4c : decode_any W_3be4c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be50 : bv 32 := 0x01813983.
Lemma F_3be50 : fetch_word Ubsan.M.loaded_segments (0x3f548 : word) = Some W_3be50.
Proof. vm_refl_bv. Qed.
Lemma D_3be50 : decode_any W_3be50 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be54 : bv 32 := 0x01013a03.
Lemma F_3be54 : fetch_word Ubsan.M.loaded_segments (0x3f54c : word) = Some W_3be54.
Proof. vm_refl_bv. Qed.
Lemma D_3be54 : decode_any W_3be54 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be58 : bv 32 := 0x00813a83.
Lemma F_3be58 : fetch_word Ubsan.M.loaded_segments (0x3f550 : word) = Some W_3be58.
Proof. vm_refl_bv. Qed.
Lemma D_3be58 : decode_any W_3be58 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be5c : bv 32 := 0x04010113.
Lemma F_3be5c : fetch_word Ubsan.M.loaded_segments (0x3f554 : word) = Some W_3be5c.
Proof. vm_refl_bv. Qed.
Lemma D_3be5c : decode_any W_3be5c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_3be60 : bv 32 := 0x00008067.
Lemma F_3be60 : fetch_word Ubsan.M.loaded_segments (0x3f558 : word) = Some W_3be60.
Proof. vm_refl_bv. Qed.
Lemma D_3be60 : decode_any W_3be60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_43bac : bv 32 := 0x00050213.
Lemma F_43bac : fetch_word Ubsan.M.loaded_segments (0x472a4 : word) = Some W_43bac.
Proof. vm_refl_bv. Qed.
Lemma D_43bac : decode_any W_43bac = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_43bb0 : bv 32 := 0x00000513.
Lemma F_43bb0 : fetch_word Ubsan.M.loaded_segments (0x472a8 : word) = Some W_43bb0.
Proof. vm_refl_bv. Qed.
Lemma D_43bb0 : decode_any W_43bb0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition W_43bb4 : bv 32 := 0x00008067.
Lemma F_43bb4 : fetch_word Ubsan.M.loaded_segments (0x472ac : word) = Some W_43bb4.
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
Lemma img_48560_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 310360) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_49818_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 315152) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
Lemma img_799e0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 512224) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_799f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 512240) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_799f8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 512248) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_79c38_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 512824) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_79c60_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 512864) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_79c78_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 512888) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
End U_startup3_rc2.
Import U_startup3_rc2.

Section P4.
  Variable sp0 : word.
  Variable Jb : word -> option byte.   (* [comment removed for export] *)
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.          (* [comment removed for export] *)
  Variable rdraw : EntryDraw.  (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01C0?L11761355482.36L12243384033.36L12472498782.36L13158362499.36L13849259718.36L13902794593.36L13999799519.36L14776295533.36L16847764461.36L17791360090.36L18454684778.36L18808583149.36L20010634847.36L20900274026.36L21067643954.36L21088052577.36L22804526938.36L23057231425.36L23801962970.36L24083552966.36L24830725298.36L27413533382.36L28815628506.36L30106128178.36L30225524705.36L31203175110.36L32370296685.36L32627942707.36L33149916870.36L33371871026.36L33399687533.36L34241120498.36L34845370970.36L35538017773.36L37712470497.36L38045499757.36L38770839137.36L39144082956.36L41565400941.36L4179067590.36 L43161223137.36L44073407213.36L44373745114.36L45171463052.36L46240745569.36L46644813299.36L4746759898.36 L47574167789.36L47910928609.36L48122681030.36L48903658733.36L49265282410.36L50084013165.36L50106887647.36L50384613210.36L51648550536.36L51742694322.36L52326544712.36L52872416840.36L53602042477.36L54112840243.36L56406225114.36L57189647838.36L57498518253.36L5750520154.36 L58702473202.36L58834748168.36L59488113761.36L60389484781.36L61924970876.36L62433575514.36L62634461106.36L6293948684.36 L6295467501.36 L6550601484.36 L66336740467.36L68029267681.36L68444706778.36L68676491139.36L7327893746.36 L8454074721.36 L967128929.36  L9880704621.36 00000900B00K00P00U00^00g00l01101:01?01D01M01R01[01d01m02:02C02H02Q02V02_02h03103603;03@03E03N03S03T03]03b03k04004904>04C04H04Q04V04_04d04m05205;05@05I05N05S05X05]05f05o06406=06B06G06L06Q06Z06c06h07107207707@07E07J07S07\07]07b07g07l08508>08C08D08M08V08[S3sp03HloS3sp03HhiS3sp03HloS3sp0S3sp0S3sp03HhiS3sp03HloS3sp0S3sp0S3sp03HloS3sp0S3sp0S3sp03HloS3sp0S3sp03HhiS3sp03HhiS3sp03HloS3sp03Hlo3HhiS3sp03HloS3sp0S3sp03HhiS3sp0S3sp03HloS3sp03HhiS3sp03HhiS3sp0S3sp0S3sp0S3sp0S3sp03HhiS3sp0FS3sp03HloS3sp0S3sp03HhiS3sp0S3sp03HhiS3sp0S3sp0S3sp0S3sp03HhiS3sp0S3sp03HloS3sp0S3sp03HhiS3sp0S3sp03HloS3sp0S3sp03HhiS3sp0S3sp0S3sp0S3sp0S3sp03HloS3sp03HloS3sp0S3sp03HhiS3sp0S3sp0S3sp0S3sp0S3sp03HloS3sp03HloS3sp0S3sp03HloFS3sp0S3sp03HhiS3sp0S3sp0S3sp03HloS3sp03HhiFS3sp0S3sp0S3sp0S3sp03HhiS3sp03HloS3sp0FS3sp03HhiS3sp03HhiS3sp0". (* [comment removed for export] *)
  #[using="Hlo Hhi"] Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 258204 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w sp0 av ev ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 512848 ->
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
getr regs' 9 = (Z_to_bv 64 512848) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 512208) ->
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
G (mkst regs' (0x3f334 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258204))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 512848))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x3f2ac : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom)
(* [comment removed for export] *).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_3bbb4 D_3bbb4 (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* [comment removed for export] *)
      stw F_3bbb8 D_3bbb8 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 258204) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_3bbbc D_3bbbc (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_3bbc0 D_3bbc0 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_3bbc4 D_3bbc4 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 512848) ltac:(ok_win HJ).  (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0?L13551766915.40L14071082371.40L14664843379.40L16701113219.40L16794754803.40L21102047372.40L264257630.40  L26956607363.40L30762139870.40L33417032542.40L36149741939.40L37334555523.40L37772652296.40L38319077384.40L3847806963.40 L41844969608.40L43215346952.40L44851326835.40L49657566814.40L52359991646.40L52991333763.40L55298622430.40L57478368883.40L58288354824.40L64547395464.4000000500:00?00D00I00J00S00X00a00j00o01401901>01C01H01M01R01[01d01i02202702<02AS3sp0S3sp0S3sp0S3sp0S3sp0FS3sp03HloS3sp0S3sp03HloS3sp03HloS3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp03HloS3sp03HloS3sp0S3sp03HloS3sp0S3sp0S3sp0". (* [comment removed for export] *)
  #[using="Hlo"] Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 512848 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 512208 ->
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
getr regs' 9 = (Z_to_bv 64 512848) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 512208) ->
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
G (mkst regs' (0x3f334 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258204))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 512848))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x3f334 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258204))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 512848))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0?L14566693982.39L16774261768.39L18336576094.39L18604756339.39L18711471454.39L29339702664.39L31892319347.39L33836737758.39L34228139656.39L36661933955.39L45553235331.39L46981234163.39L47974888158.39L5038593923.39 L55196470659.39L55788868995.39L56544824200.39L56553727454.39L59912399112.39L59932376307.39L61170730508.39L6134504051.39 L63178599176.39L63583890819.39L67970814707.3900000900>00G00L00U00Z00_00h00m01201701<01E01J01O01T01Y01b01g01l01m02202702<02AS3sp03HloS3sp0S3sp03HloS3sp0S3sp03HloS3sp0S3sp0S3sp03HloS3sp0S3sp0S3sp0S3sp0S3sp03HloS3sp0S3sp0S3sp0S3sp0S3sp03HloS3sp0S3sp0FS3sp0S3sp0S3sp0S3sp0". (* [comment removed for export] *)
  #[using="Hlo"] Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 512848 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 512208 ->
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
getr regs' 9 = (Z_to_bv 64 512848) ->
getr regs' 11 = (Z_to_bv 64 512208) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x3f384 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258204))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 512848))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x3f334 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258204))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 512848))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00o0?L10235426675.31L11028151134.31L1186627459.31 L12119956355.31L12472498782.31L13581673591.31L15658923870.31L16311710630.31L1705312627.31 L18445782566.31L1872621939.31 L18839700867.31L25333220595.31L2618183176.31 L26998569694.31L27463127923.31L27575482334.31L2898355336.31 L30900358531.31L31445245357.31L3164085000.31 L31720586355.31L33535221670.31L33964216328.31L3444781448.31 L34575018334.31L35665127974.31L3714438152.31 L3847806963.31 L39922841382.31L41581083144.31L41844969608.31L41887274406.31L42127505160.31L42390875528.31L42669178888.31L43215346952.31L46161772198.31L48939898995.31L50520870189.31L53214389619.31L54764468574.31L54973040606.31L55298622430.31L55344296947.31L55503184883.31L5681040771.31 L56978809638.31L57376515798.31L57478368883.31L58803348062.31L58834748168.31L59275993510.31L61333579478.31L61986565854.31L62338024835.31L62913131656.31L63537875622.31L66174993283.31L66336740467.31L7841721950.31 L8109717747.31 L843537758.31  00000500>00C00H00Q00R00[00\00a00b00g00l01101601?01D01M01R01W01\01a01f01g01l02102:02;02@02E02F02K02P02Q02V02[02`02e02f02k03003503>03G03P03U03Z03_03`03a03f03o04404504604?04D04I04J04K04P04Y04^04gS3sp0S3sp03HloS3sp0S3sp0S3sp03HloFS3sp03HloFS3sp0FS3sp0S3sp0S3sp0S3sp0S3sp03HloS3sp0S3sp03HloS3sp0S3sp0S3sp0S3sp0S3sp0FS3sp0S3sp0S3sp03HloFS3sp0S3sp0FS3sp0S3sp0FS3sp0S3sp0S3sp0S3sp0FS3sp0S3sp0S3sp0S3sp03HloS3sp03HloS3sp03HloS3sp0S3sp0S3sp0FFS3sp0S3sp03HloS3sp0FFS3sp03HloS3sp0S3sp0FFS3sp0S3sp03HloS3sp0S3sp03Hlo". (* [comment removed for export] *)
  #[using="Hlo"] Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 512848 ->
getr regs 11 = Z_to_bv 64 512208 ->
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
getr regs' 4 = (Z_to_bv 64 381128) ->
getr regs' 10 = (Z_to_bv 64 512208) ->
getr regs' 11 = (Z_to_bv 64 512904) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 380920) ->
getr regs' 14 = (Z_to_bv 64 0) ->
getr regs' 15 = (Z_to_bv 64 18446744073709170488) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 380928) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x3f508 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258204))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 512848))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 512240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512248) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 512872) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 512880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 381144) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 381120) (word_to_le_bytes 8 (Z_to_bv 64 381144))) (Z_to_bv 64 380928) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 512848) ([Z_to_bv 8 1])) (Z_to_bv 64 380968) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x3f384 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258204))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 512848))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)
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
      stw F_3bcec D_3bcec (Z_to_bv 64 512240) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3bcf0 D_3bcf0 (Z_to_bv 64 512256) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stepb_ft F_3bcf4 D_3bcf4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bcf8 D_3bcf8.  (* [comment removed for export] *)
      stw F_3bcfc D_3bcfc (Z_to_bv 64 512248) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_3bd00 D_3bd00.  (* [comment removed for export] *)
      sn F_3bd04 D_3bd04.  (* [comment removed for export] *)
      sn F_3bd08 D_3bd08.  (* [comment removed for export] *)
      sn F_3bd0c D_3bd0c.  (* [comment removed for export] *)
      sn F_3bd10 D_3bd10.  (* [comment removed for export] *)
      sn F_3bd14 D_3bd14.  (* [comment removed for export] *)
      stw F_3bd18 D_3bd18 (Z_to_bv 64 512872) (Z_to_bv 64 224) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3bd1c D_3bd1c (Z_to_bv 64 512880) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
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
      stw F_3bdd4 D_3bdd4 (Z_to_bv 64 381144) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3bdd8 D_3bdd8 (Z_to_bv 64 381120) (Z_to_bv 64 381144) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3bddc D_3bddc (Z_to_bv 64 380928) (Z_to_bv 64 380928) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_3bde0 D_3bde0.  (* [comment removed for export] *)
      sn F_3bde4 D_3bde4.  (* [comment removed for export] *)
      sn F_43bac D_43bac.  (* [comment removed for export] *)
      sn F_43bb0 D_43bb0.  (* [comment removed for export] *)
      stepret F_43bb4 D_43bb4 (0x3f4e0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      stepb_ft F_3bde8 D_3bde8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_ft F_3bdec D_3bdec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3bdf0 D_3bdf0.  (* [comment removed for export] *)
      stw F_3bdf4 D_3bdf4 (Z_to_bv 64 512848) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_3bdf8 D_3bdf8.  (* [comment removed for export] *)
      sn F_3bdfc D_3bdfc.  (* [comment removed for export] *)
      stw F_3be00 D_3be00 (Z_to_bv 64 380968) (Z_to_bv 64 2) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_3be04 D_3be04.  (* [comment removed for export] *)
      sn F_3be08 D_3be08.  (* [comment removed for export] *)
      sn F_3be0c D_3be0c.  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01R0?L10020158943.32L10420125836.32L10617393138.32L11761355482.32L11923865906.32L13591435698.32L16931134314.32L17061478962.32L171769736.32  L17791360090.32L18590187626.32L18808583149.32L19094035827.32L20146227634.32L22130483250.32L23057231425.32L23236351326.32L24676845990.32L25508581362.32L27144413682.32L27458063235.32L27953926386.32L28254875334.32L28515492360.32L29096242526.32L30225524705.32L30763284586.32L31254830954.32L31328252397.32L32101884978.32L32370296685.32L33184619114.32L33412024072.32L34013551538.32L37002513932.32L37502699656.32L37712470497.32L37797132454.32L38279645171.32L38770839137.32L39632012594.32L4009027679.32 L40206139570.32L41123362610.32L42562522974.32L42623864031.32L43030156172.32L43421366122.32L4398546700.32 L44210207410.32L44373745114.32L4755155762.32 L4760429418.32 L47910928609.32L48291646758.32L48651771487.32L49043383564.32L49113204851.32L50384613210.32L50417621926.32L51073996531.32L51076407198.32L51393073330.32L5251296365.32 L53369083251.32L54660277215.32L54877638898.32L56406225114.32L5750520154.32 L57645075550.32L59108716966.32L59370167304.32L59488113761.32L59650863752.32L5977713267.32 L60204197362.32L60389484781.32L60687922527.32L61013710066.32L61079771148.32L61408001062.32L61418609389.32L62072736627.32L62433575514.32L6243839597.32 L62776673202.32L63720825864.32L64202643955.32L64627859934.32L66701117151.32L6670145758.32 L67107155340.32L68029267681.32L68444706778.32L68625488136.32L8454074721.32 L967128929.32  L9815509982.32 00000900>00?00H00Q00Z00_00h00m01601;01@01E01N01W01d01m01n01o02002502602;02@02I02R02W02\02a02j02o03403903B03G03L03U03V03[03d03m04604?04H04Q04Z04_04d04i05205;05D05I05R05S05\05a05f05o06006506606?06D06I06R06S06\06e06n06o07407=07B07G07H07M07V07W07\07]07b07g08008508>08C08H08Q08Z08c08h09109:09?09H09Q09ZS3sp03HloS3sp0FS3sp03HloS3sp03HhiS3sp03HhiS3sp0S3sp03HhiS3sp0S3sp03HloS3sp0S3sp0S3sp0S3sp03HhiS3sp03HhiS3sp03Hlo3HhiS3sp03HloFFFS3sp0FS3sp0S3sp0S3sp03HloS3sp03HhiS3sp0S3sp0S3sp0S3sp03HhiS3sp0S3sp0S3sp0S3sp03HhiS3sp0S3sp0S3sp03HhiFS3sp0S3sp03HhiS3sp03HhiS3sp03HloS3sp03HhiS3sp03HhiS3sp03HloS3sp03HloS3sp0S3sp0S3sp0S3sp03HhiS3sp03HloS3sp03HhiS3sp0S3sp03HhiFS3sp03HloS3sp0S3sp0S3sp03HloFS3sp0FS3sp03HhiS3sp0S3sp0S3sp03HloFS3sp03HloS3sp03HloS3sp03HloFS3sp0S3sp03HhiS3sp0S3sp0FS3sp0S3sp03HloFS3sp0FS3sp0S3sp0S3sp03HloS3sp0S3sp03HhiS3sp0S3sp0S3sp03HloS3sp03HloS3sp03HloS3sp0S3sp03HhiS3sp03HloS3sp0S3sp03HhiS3sp03HhiS3sp03Hlo". (* [comment removed for export] *)
  #[using="Hlo Hhi"] Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 381128 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 512904 ->
getr regs 18 = Z_to_bv 64 380928 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 381128) ->
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
G (mkst regs' (0x3f09c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258204))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 512848))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 512240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512248) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 512872) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 512880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 381144) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 381120) (word_to_le_bytes 8 (Z_to_bv 64 381144))) (Z_to_bv 64 380928) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 512848) ([Z_to_bv 8 1])) (Z_to_bv 64 380968) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 380960) (word_to_le_bytes 4 tid)) (Z_to_bv 64 381080) (word_to_le_bytes 8 (Z_to_bv 64 512904))) (Z_to_bv 64 381048) (word_to_le_bytes 8 (Z_to_bv 64 381048))) (Z_to_bv 64 380936) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380944) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380952) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x3f50c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258204))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 512848))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 512240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512248) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 512872) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 512880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 381144) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 381120) (word_to_le_bytes 8 (Z_to_bv 64 381144))) (Z_to_bv 64 380928) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 512848) ([Z_to_bv 8 1])) (Z_to_bv 64 380968) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)
(* [comment removed for export] *).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sn F_3be14 D_3be14.  (* [comment removed for export] *)
      stw F_3be18 D_3be18 (Z_to_bv 64 380960) tid ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3be1c D_3be1c (Z_to_bv 64 381080) (Z_to_bv 64 512904) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3be20 D_3be20 (Z_to_bv 64 381048) (Z_to_bv 64 381048) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_3be24 D_3be24.  (* [comment removed for export] *)
      ld_step F_3be28 D_3be28 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_79c38_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_3be2c D_3be2c (Z_to_bv 64 380936) (Z_to_bv 64 380928) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3be30 D_3be30 (Z_to_bv 64 380944) (Z_to_bv 64 380928) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3be34 D_3be34 (Z_to_bv 64 380952) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_3be38 D_3be38.  (* [comment removed for export] *)
      ld_step F_3be40 D_3be40 (word_to_le_bytes 8 (Z_to_bv 64 258204)) (Z_to_bv 64 258204) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3be44 D_3be44 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3be48 D_3be48 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3be4c D_3be4c (word_to_le_bytes 8 (Z_to_bv 64 512848)) (Z_to_bv 64 512848) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3be50 D_3be50 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3be54 D_3be54 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3be58 D_3be58 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_3be5c D_3be5c (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_3be60 D_3be60 (0x3f09c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
