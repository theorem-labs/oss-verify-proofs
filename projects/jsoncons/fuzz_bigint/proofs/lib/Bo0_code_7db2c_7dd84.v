(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_7db2c : bv 32 := 0xfc010113.
Lemma F_7db2c : fetch_word AsanUbsan.M.loaded_segments (0x7db2c : word) = Some W_7db2c.
Proof. vm_refl. Qed.
Lemma D_7db2c : decode_any W_7db2c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db30 : bv 32 := 0x02113c23.
Lemma F_7db30 : fetch_word AsanUbsan.M.loaded_segments (0x7db30 : word) = Some W_7db30.
Proof. vm_refl. Qed.
Lemma D_7db30 : decode_any W_7db30 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db34 : bv 32 := 0x02813823.
Lemma F_7db34 : fetch_word AsanUbsan.M.loaded_segments (0x7db34 : word) = Some W_7db34.
Proof. vm_refl. Qed.
Lemma D_7db34 : decode_any W_7db34 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db38 : bv 32 := 0x02913423.
Lemma F_7db38 : fetch_word AsanUbsan.M.loaded_segments (0x7db38 : word) = Some W_7db38.
Proof. vm_refl. Qed.
Lemma D_7db38 : decode_any W_7db38 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db3c : bv 32 := 0x03213023.
Lemma F_7db3c : fetch_word AsanUbsan.M.loaded_segments (0x7db3c : word) = Some W_7db3c.
Proof. vm_refl. Qed.
Lemma D_7db3c : decode_any W_7db3c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db40 : bv 32 := 0x01313c23.
Lemma F_7db40 : fetch_word AsanUbsan.M.loaded_segments (0x7db40 : word) = Some W_7db40.
Proof. vm_refl. Qed.
Lemma D_7db40 : decode_any W_7db40 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db44 : bv 32 := 0x01413823.
Lemma F_7db44 : fetch_word AsanUbsan.M.loaded_segments (0x7db44 : word) = Some W_7db44.
Proof. vm_refl. Qed.
Lemma D_7db44 : decode_any W_7db44 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db48 : bv 32 := 0x01513423.
Lemma F_7db48 : fetch_word AsanUbsan.M.loaded_segments (0x7db48 : word) = Some W_7db48.
Proof. vm_refl. Qed.
Lemma D_7db48 : decode_any W_7db48 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db4c : bv 32 := 0x00058993.
Lemma F_7db4c : fetch_word AsanUbsan.M.loaded_segments (0x7db4c : word) = Some W_7db4c.
Proof. vm_refl. Qed.
Lemma D_7db4c : decode_any W_7db4c = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db50 : bv 32 := 0x0085aa03.
Lemma F_7db50 : fetch_word AsanUbsan.M.loaded_segments (0x7db50 : word) = Some W_7db50.
Proof. vm_refl. Qed.
Lemma D_7db50 : decode_any W_7db50 = Some (Load SZ4 true 20 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db54 : bv 32 := 0x00c5aa83.
Lemma F_7db54 : fetch_word AsanUbsan.M.loaded_segments (0x7db54 : word) = Some W_7db54.
Proof. vm_refl. Qed.
Lemma D_7db54 : decode_any W_7db54 = Some (Load SZ4 true 21 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db58 : bv 32 := 0x015a65b3.
Lemma F_7db58 : fetch_word AsanUbsan.M.loaded_segments (0x7db58 : word) = Some W_7db58.
Proof. vm_refl. Qed.
Lemma D_7db58 : decode_any W_7db58 = Some (Op ALU_OR 11 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db5c : bv 32 := 0x00059663.
Lemma F_7db5c : fetch_word AsanUbsan.M.loaded_segments (0x7db5c : word) = Some W_7db5c.
Proof. vm_refl. Qed.
Lemma D_7db5c : decode_any W_7db5c = Some (Branch BC_NE 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db60 : bv 32 := 0x00000513.
Lemma F_7db60 : fetch_word AsanUbsan.M.loaded_segments (0x7db60 : word) = Some W_7db60.
Proof. vm_refl. Qed.
Lemma D_7db60 : decode_any W_7db60 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db64 : bv 32 := 0x0a40006f.
Lemma F_7db64 : fetch_word AsanUbsan.M.loaded_segments (0x7db64 : word) = Some W_7db64.
Proof. vm_refl. Qed.
Lemma D_7db64 : decode_any W_7db64 = Some (Jal 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db68 : bv 32 := 0x00050493.
Lemma F_7db68 : fetch_word AsanUbsan.M.loaded_segments (0x7db68 : word) = Some W_7db68.
Proof. vm_refl. Qed.
Lemma D_7db68 : decode_any W_7db68 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db6c : bv 32 := 0x10000513.
Lemma F_7db6c : fetch_word AsanUbsan.M.loaded_segments (0x7db6c : word) = Some W_7db6c.
Proof. vm_refl. Qed.
Lemma D_7db6c : decode_any W_7db6c = Some (OpImm ALU_ADD 10 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db70 : bv 32 := 0x0aaafe63.
Lemma F_7db70 : fetch_word AsanUbsan.M.loaded_segments (0x7db70 : word) = Some W_7db70.
Proof. vm_refl. Qed.
Lemma D_7db70 : decode_any W_7db70 = Some (Branch BC_GEU 21 10 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db74 : bv 32 := 0x00060413.
Lemma F_7db74 : fetch_word AsanUbsan.M.loaded_segments (0x7db74 : word) = Some W_7db74.
Proof. vm_refl. Qed.
Lemma D_7db74 : decode_any W_7db74 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db78 : bv 32 := 0x0ff00513.
Lemma F_7db78 : fetch_word AsanUbsan.M.loaded_segments (0x7db78 : word) = Some W_7db78.
Proof. vm_refl. Qed.
Lemma D_7db78 : decode_any W_7db78 = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db7c : bv 32 := 0x00aa6463.
Lemma F_7db7c : fetch_word AsanUbsan.M.loaded_segments (0x7db7c : word) = Some W_7db7c.
Proof. vm_refl. Qed.
Lemma D_7db7c : decode_any W_7db7c = Some (Branch BC_LTU 20 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db80 : bv 32 := 0x0ff00a13.
Lemma F_7db80 : fetch_word AsanUbsan.M.loaded_segments (0x7db80 : word) = Some W_7db80.
Proof. vm_refl. Qed.
Lemma D_7db80 : decode_any W_7db80 = Some (OpImm ALU_ADD 20 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db84 : bv 32 := 0x00013023.
Lemma F_7db84 : fetch_word AsanUbsan.M.loaded_segments (0x7db84 : word) = Some W_7db84.
Proof. vm_refl. Qed.
Lemma D_7db84 : decode_any W_7db84 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db88 : bv 32 := 0x00043023.
Lemma F_7db88 : fetch_word AsanUbsan.M.loaded_segments (0x7db88 : word) = Some W_7db88.
Proof. vm_refl. Qed.
Lemma D_7db88 : decode_any W_7db88 = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db8c : bv 32 := 0x001a0913.
Lemma F_7db8c : fetch_word AsanUbsan.M.loaded_segments (0x7db8c : word) = Some W_7db8c.
Proof. vm_refl. Qed.
Lemma D_7db8c : decode_any W_7db8c = Some (OpImm ALU_ADD 18 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db90 : bv 32 := 0x00010613.
Lemma F_7db90 : fetch_word AsanUbsan.M.loaded_segments (0x7db90 : word) = Some W_7db90.
Proof. vm_refl. Qed.
Lemma D_7db90 : decode_any W_7db90 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db94 : bv 32 := 0x00048513.
Lemma F_7db94 : fetch_word AsanUbsan.M.loaded_segments (0x7db94 : word) = Some W_7db94.
Proof. vm_refl. Qed.
Lemma D_7db94 : decode_any W_7db94 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db98 : bv 32 := 0x00090593.
Lemma F_7db98 : fetch_word AsanUbsan.M.loaded_segments (0x7db98 : word) = Some W_7db98.
Proof. vm_refl. Qed.
Lemma D_7db98 : decode_any W_7db98 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db9c : bv 32 := 0x00040693.
Lemma F_7db9c : fetch_word AsanUbsan.M.loaded_segments (0x7db9c : word) = Some W_7db9c.
Proof. vm_refl. Qed.
Lemma D_7db9c : decode_any W_7db9c = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dba0 : bv 32 := 0x0b0000ef.
Lemma F_7dba0 : fetch_word AsanUbsan.M.loaded_segments (0x7dba0 : word) = Some W_7dba0.
Proof. vm_refl. Qed.
Lemma D_7dba0 : decode_any W_7dba0 = Some (Jal 1 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dba4 : bv 32 := 0x06050263.
Lemma F_7dba4 : fetch_word AsanUbsan.M.loaded_segments (0x7dba4 : word) = Some W_7dba4.
Proof. vm_refl. Qed.
Lemma D_7dba4 : decode_any W_7dba4 = Some (Branch BC_EQ 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dba8 : bv 32 := 0x008a961b.
Lemma F_7dba8 : fetch_word AsanUbsan.M.loaded_segments (0x7dba8 : word) = Some W_7dba8.
Proof. vm_refl. Qed.
Lemma D_7dba8 : decode_any W_7dba8 = Some (ShiftImm32 ALU_SLL 12 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbac : bv 32 := 0x0009b583.
Lemma F_7dbac : fetch_word AsanUbsan.M.loaded_segments (0x7dbac : word) = Some W_7dbac.
Proof. vm_refl. Qed.
Lemma D_7dbac : decode_any W_7dbac = Some (Load SZ8 true 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbb0 : bv 32 := 0x01466633.
Lemma F_7dbb0 : fetch_word AsanUbsan.M.loaded_segments (0x7dbb0 : word) = Some W_7dbb0.
Proof. vm_refl. Qed.
Lemma D_7dbb0 : decode_any W_7dbb0 = Some (Op ALU_OR 12 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbb4 : bv 32 := 0x00c53023.
Lemma F_7dbb4 : fetch_word AsanUbsan.M.loaded_segments (0x7dbb4 : word) = Some W_7dbb4.
Proof. vm_refl. Qed.
Lemma D_7dbb4 : decode_any W_7dbb4 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbb8 : bv 32 := 0x00850513.
Lemma F_7dbb8 : fetch_word AsanUbsan.M.loaded_segments (0x7dbb8 : word) = Some W_7dbb8.
Proof. vm_refl. Qed.
Lemma D_7dbb8 : decode_any W_7dbb8 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbbc : bv 32 := 0x003a1613.
Lemma F_7dbbc : fetch_word AsanUbsan.M.loaded_segments (0x7dbbc : word) = Some W_7dbbc.
Proof. vm_refl. Qed.
Lemma D_7dbbc : decode_any W_7dbbc = Some (ShiftImm ALU_SLL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbc0 : bv 32 := 0x9a5f30ef.
Lemma F_7dbc0 : fetch_word AsanUbsan.M.loaded_segments (0x7dbc0 : word) = Some W_7dbc0.
Proof. vm_refl. Qed.
Lemma D_7dbc0 : decode_any W_7dbc0 = Some (Jal 1 2046372, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbc4 : bv 32 := 0x00013503.
Lemma F_7dbc4 : fetch_word AsanUbsan.M.loaded_segments (0x7dbc4 : word) = Some W_7dbc4.
Proof. vm_refl. Qed.
Lemma D_7dbc4 : decode_any W_7dbc4 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbc8 : bv 32 := 0x01055513.
Lemma F_7dbc8 : fetch_word AsanUbsan.M.loaded_segments (0x7dbc8 : word) = Some W_7dbc8.
Proof. vm_refl. Qed.
Lemma D_7dbc8 : decode_any W_7dbc8 = Some (ShiftImm ALU_SRL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbcc : bv 32 := 0xff057513.
Lemma F_7dbcc : fetch_word AsanUbsan.M.loaded_segments (0x7dbcc : word) = Some W_7dbcc.
Proof. vm_refl. Qed.
Lemma D_7dbcc : decode_any W_7dbcc = Some (OpImm ALU_AND 10 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbd0 : bv 32 := 0x00a48533.
Lemma F_7dbd0 : fetch_word AsanUbsan.M.loaded_segments (0x7dbd0 : word) = Some W_7dbd0.
Proof. vm_refl. Qed.
Lemma D_7dbd0 : decode_any W_7dbd0 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbd4 : bv 32 := 0x01850513.
Lemma F_7dbd4 : fetch_word AsanUbsan.M.loaded_segments (0x7dbd4 : word) = Some W_7dbd4.
Proof. vm_refl. Qed.
Lemma D_7dbd4 : decode_any W_7dbd4 = Some (OpImm ALU_ADD 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbd8 : bv 32 := 0x0325252f.
Lemma F_7dbd8 : fetch_word AsanUbsan.M.loaded_segments (0x7dbd8 : word) = Some W_7dbd8.
Proof. vm_refl. Qed.
Lemma D_7dbd8 : decode_any W_7dbd8 = Some (Amo AMO_ADD AW false true 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbdc : bv 32 := 0x001005b7.
Lemma F_7dbdc : fetch_word AsanUbsan.M.loaded_segments (0x7dbdc : word) = Some W_7dbdc.
Proof. vm_refl. Qed.
Lemma D_7dbdc : decode_any W_7dbdc = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbe0 : bv 32 := 0x02051513.
Lemma F_7dbe0 : fetch_word AsanUbsan.M.loaded_segments (0x7dbe0 : word) = Some W_7dbe0.
Proof. vm_refl. Qed.
Lemma D_7dbe0 : decode_any W_7dbe0 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbe4 : bv 32 := 0x02055513.
Lemma F_7dbe4 : fetch_word AsanUbsan.M.loaded_segments (0x7dbe4 : word) = Some W_7dbe4.
Proof. vm_refl. Qed.
Lemma D_7dbe4 : decode_any W_7dbe4 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbe8 : bv 32 := 0x00a90533.
Lemma F_7dbe8 : fetch_word AsanUbsan.M.loaded_segments (0x7dbe8 : word) = Some W_7dbe8.
Proof. vm_refl. Qed.
Lemma D_7dbe8 : decode_any W_7dbe8 = Some (Op ALU_ADD 10 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbec : bv 32 := 0x00043603.
Lemma F_7dbec : fetch_word AsanUbsan.M.loaded_segments (0x7dbec : word) = Some W_7dbec.
Proof. vm_refl. Qed.
Lemma D_7dbec : decode_any W_7dbec = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbf0 : bv 32 := 0x00b54533.
Lemma F_7dbf0 : fetch_word AsanUbsan.M.loaded_segments (0x7dbf0 : word) = Some W_7dbf0.
Proof. vm_refl. Qed.
Lemma D_7dbf0 : decode_any W_7dbf0 = Some (Op ALU_XOR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbf4 : bv 32 := 0x00012583.
Lemma F_7dbf4 : fetch_word AsanUbsan.M.loaded_segments (0x7dbf4 : word) = Some W_7dbf4.
Proof. vm_refl. Qed.
Lemma D_7dbf4 : decode_any W_7dbf4 = Some (Load SZ4 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbf8 : bv 32 := 0x00153513.
Lemma F_7dbf8 : fetch_word AsanUbsan.M.loaded_segments (0x7dbf8 : word) = Some W_7dbf8.
Proof. vm_refl. Qed.
Lemma D_7dbf8 : decode_any W_7dbf8 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dbfc : bv 32 := 0x00a60533.
Lemma F_7dbfc : fetch_word AsanUbsan.M.loaded_segments (0x7dbfc : word) = Some W_7dbfc.
Proof. vm_refl. Qed.
Lemma D_7dbfc : decode_any W_7dbfc = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc00 : bv 32 := 0x00a43023.
Lemma F_7dc00 : fetch_word AsanUbsan.M.loaded_segments (0x7dc00 : word) = Some W_7dc00.
Proof. vm_refl. Qed.
Lemma D_7dc00 : decode_any W_7dc00 = Some (Store SZ8 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc04 : bv 32 := 0x0015851b.
Lemma F_7dc04 : fetch_word AsanUbsan.M.loaded_segments (0x7dc04 : word) = Some W_7dc04.
Proof. vm_refl. Qed.
Lemma D_7dc04 : decode_any W_7dc04 = Some (OpImm32 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc08 : bv 32 := 0x03813083.
Lemma F_7dc08 : fetch_word AsanUbsan.M.loaded_segments (0x7dc08 : word) = Some W_7dc08.
Proof. vm_refl. Qed.
Lemma D_7dc08 : decode_any W_7dc08 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc0c : bv 32 := 0x03013403.
Lemma F_7dc0c : fetch_word AsanUbsan.M.loaded_segments (0x7dc0c : word) = Some W_7dc0c.
Proof. vm_refl. Qed.
Lemma D_7dc0c : decode_any W_7dc0c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc10 : bv 32 := 0x02813483.
Lemma F_7dc10 : fetch_word AsanUbsan.M.loaded_segments (0x7dc10 : word) = Some W_7dc10.
Proof. vm_refl. Qed.
Lemma D_7dc10 : decode_any W_7dc10 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc14 : bv 32 := 0x02013903.
Lemma F_7dc14 : fetch_word AsanUbsan.M.loaded_segments (0x7dc14 : word) = Some W_7dc14.
Proof. vm_refl. Qed.
Lemma D_7dc14 : decode_any W_7dc14 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc18 : bv 32 := 0x01813983.
Lemma F_7dc18 : fetch_word AsanUbsan.M.loaded_segments (0x7dc18 : word) = Some W_7dc18.
Proof. vm_refl. Qed.
Lemma D_7dc18 : decode_any W_7dc18 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc1c : bv 32 := 0x01013a03.
Lemma F_7dc1c : fetch_word AsanUbsan.M.loaded_segments (0x7dc1c : word) = Some W_7dc1c.
Proof. vm_refl. Qed.
Lemma D_7dc1c : decode_any W_7dc1c = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc20 : bv 32 := 0x00813a83.
Lemma F_7dc20 : fetch_word AsanUbsan.M.loaded_segments (0x7dc20 : word) = Some W_7dc20.
Proof. vm_refl. Qed.
Lemma D_7dc20 : decode_any W_7dc20 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc24 : bv 32 := 0x04010113.
Lemma F_7dc24 : fetch_word AsanUbsan.M.loaded_segments (0x7dc24 : word) = Some W_7dc24.
Proof. vm_refl. Qed.
Lemma D_7dc24 : decode_any W_7dc24 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc28 : bv 32 := 0x00008067.
Lemma F_7dc28 : fetch_word AsanUbsan.M.loaded_segments (0x7dc28 : word) = Some W_7dc28.
Proof. vm_refl. Qed.
Lemma D_7dc28 : decode_any W_7dc28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc2c : bv 32 := 0x020a9693.
Lemma F_7dc2c : fetch_word AsanUbsan.M.loaded_segments (0x7dc2c : word) = Some W_7dc2c.
Proof. vm_refl. Qed.
Lemma D_7dc2c : decode_any W_7dc2c = Some (ShiftImm ALU_SLL 13 21 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc30 : bv 32 := 0x0206d693.
Lemma F_7dc30 : fetch_word AsanUbsan.M.loaded_segments (0x7dc30 : word) = Some W_7dc30.
Proof. vm_refl. Qed.
Lemma D_7dc30 : decode_any W_7dc30 = Some (ShiftImm ALU_SRL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc34 : bv 32 := 0x0ff6f713.
Lemma F_7dc34 : fetch_word AsanUbsan.M.loaded_segments (0x7dc34 : word) = Some W_7dc34.
Proof. vm_refl. Qed.
Lemma D_7dc34 : decode_any W_7dc34 = Some (OpImm ALU_AND 14 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc38 : bv 32 := 0xfffa3517.
Lemma F_7dc38 : fetch_word AsanUbsan.M.loaded_segments (0x7dc38 : word) = Some W_7dc38.
Proof. vm_refl. Qed.
Lemma D_7dc38 : decode_any W_7dc38 = Some (Auipc 10 1048483, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc3c : bv 32 := 0xfff9a597.
Lemma F_7dc3c : fetch_word AsanUbsan.M.loaded_segments (0x7dc3c : word) = Some W_7dc3c.
Proof. vm_refl. Qed.
Lemma D_7dc3c : decode_any W_7dc3c = Some (Auipc 11 1048474, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc40 : bv 32 := 0x46050513.
Lemma F_7dc40 : fetch_word AsanUbsan.M.loaded_segments (0x7dc40 : word) = Some W_7dc40.
Proof. vm_refl. Qed.
Lemma D_7dc40 : decode_any W_7dc40 = Some (OpImm ALU_ADD 10 10 1120, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc44 : bv 32 := 0xa1c58613.
Lemma F_7dc44 : fetch_word AsanUbsan.M.loaded_segments (0x7dc44 : word) = Some W_7dc44.
Proof. vm_refl. Qed.
Lemma D_7dc44 : decode_any W_7dc44 = Some (OpImm ALU_ADD 12 11 2588, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc48 : bv 32 := 0x01d00593.
Lemma F_7dc48 : fetch_word AsanUbsan.M.loaded_segments (0x7dc48 : word) = Some W_7dc48.
Proof. vm_refl. Qed.
Lemma D_7dc48 : decode_any W_7dc48 = Some (OpImm ALU_ADD 11 0 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc4c : bv 32 := 0xe9cfb0ef.
Lemma F_7dc4c : fetch_word AsanUbsan.M.loaded_segments (0x7dc4c : word) = Some W_7dc4c.
Proof. vm_refl. Qed.
Lemma D_7dc4c : decode_any W_7dc4c = Some (Jal 1 2078364, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc50 : bv 32 := 0xff010113.
Lemma F_7dc50 : fetch_word AsanUbsan.M.loaded_segments (0x7dc50 : word) = Some W_7dc50.
Proof. vm_refl. Qed.
Lemma D_7dc50 : decode_any W_7dc50 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc54 : bv 32 := 0x00113423.
Lemma F_7dc54 : fetch_word AsanUbsan.M.loaded_segments (0x7dc54 : word) = Some W_7dc54.
Proof. vm_refl. Qed.
Lemma D_7dc54 : decode_any W_7dc54 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc58 : bv 32 := 0x00813023.
Lemma F_7dc58 : fetch_word AsanUbsan.M.loaded_segments (0x7dc58 : word) = Some W_7dc58.
Proof. vm_refl. Qed.
Lemma D_7dc58 : decode_any W_7dc58 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc5c : bv 32 := 0x00058793.
Lemma F_7dc5c : fetch_word AsanUbsan.M.loaded_segments (0x7dc5c : word) = Some W_7dc5c.
Proof. vm_refl. Qed.
Lemma D_7dc5c : decode_any W_7dc5c = Some (OpImm ALU_ADD 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc60 : bv 32 := 0x00050593.
Lemma F_7dc60 : fetch_word AsanUbsan.M.loaded_segments (0x7dc60 : word) = Some W_7dc60.
Proof. vm_refl. Qed.
Lemma D_7dc60 : decode_any W_7dc60 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc64 : bv 32 := 0x00f5342f.
Lemma F_7dc64 : fetch_word AsanUbsan.M.loaded_segments (0x7dc64 : word) = Some W_7dc64.
Proof. vm_refl. Qed.
Lemma D_7dc64 : decode_any W_7dc64 = Some (Amo AMO_ADD AD false false 8 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc68 : bv 32 := 0xfff78513.
Lemma F_7dc68 : fetch_word AsanUbsan.M.loaded_segments (0x7dc68 : word) = Some W_7dc68.
Proof. vm_refl. Qed.
Lemma D_7dc68 : decode_any W_7dc68 = Some (OpImm ALU_ADD 10 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc6c : bv 32 := 0x01445293.
Lemma F_7dc6c : fetch_word AsanUbsan.M.loaded_segments (0x7dc6c : word) = Some W_7dc6c.
Proof. vm_refl. Qed.
Lemma D_7dc6c : decode_any W_7dc6c = Some (ShiftImm ALU_SRL 5 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc70 : bv 32 := 0x00850733.
Lemma F_7dc70 : fetch_word AsanUbsan.M.loaded_segments (0x7dc70 : word) = Some W_7dc70.
Proof. vm_refl. Qed.
Lemma D_7dc70 : decode_any W_7dc70 = Some (Op ALU_ADD 14 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc74 : bv 32 := 0x01475313.
Lemma F_7dc74 : fetch_word AsanUbsan.M.loaded_segments (0x7dc74 : word) = Some W_7dc74.
Proof. vm_refl. Qed.
Lemma D_7dc74 : decode_any W_7dc74 = Some (ShiftImm ALU_SRL 6 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc78 : bv 32 := 0x04629863.
Lemma F_7dc78 : fetch_word AsanUbsan.M.loaded_segments (0x7dc78 : word) = Some W_7dc78.
Proof. vm_refl. Qed.
Lemma D_7dc78 : decode_any W_7dc78 = Some (Branch BC_NE 5 6 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc7c : bv 32 := 0x02045513.
Lemma F_7dc7c : fetch_word AsanUbsan.M.loaded_segments (0x7dc7c : word) = Some W_7dc7c.
Proof. vm_refl. Qed.
Lemma D_7dc7c : decode_any W_7dc7c = Some (ShiftImm ALU_SRL 10 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc80 : bv 32 := 0x00050c63.
Lemma F_7dc80 : fetch_word AsanUbsan.M.loaded_segments (0x7dc80 : word) = Some W_7dc80.
Proof. vm_refl. Qed.
Lemma D_7dc80 : decode_any W_7dc80 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc84 : bv 32 := 0x00000513.
Lemma F_7dc84 : fetch_word AsanUbsan.M.loaded_segments (0x7dc84 : word) = Some W_7dc84.
Proof. vm_refl. Qed.
Lemma D_7dc84 : decode_any W_7dc84 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc88 : bv 32 := 0x00813083.
Lemma F_7dc88 : fetch_word AsanUbsan.M.loaded_segments (0x7dc88 : word) = Some W_7dc88.
Proof. vm_refl. Qed.
Lemma D_7dc88 : decode_any W_7dc88 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc8c : bv 32 := 0x00013403.
Lemma F_7dc8c : fetch_word AsanUbsan.M.loaded_segments (0x7dc8c : word) = Some W_7dc8c.
Proof. vm_refl. Qed.
Lemma D_7dc8c : decode_any W_7dc8c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc90 : bv 32 := 0x01010113.
Lemma F_7dc90 : fetch_word AsanUbsan.M.loaded_segments (0x7dc90 : word) = Some W_7dc90.
Proof. vm_refl. Qed.
Lemma D_7dc90 : decode_any W_7dc90 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc94 : bv 32 := 0x00008067.
Lemma F_7dc94 : fetch_word AsanUbsan.M.loaded_segments (0x7dc94 : word) = Some W_7dc94.
Proof. vm_refl. Qed.
Lemma D_7dc94 : decode_any W_7dc94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc98 : bv 32 := 0x00863023.
Lemma F_7dc98 : fetch_word AsanUbsan.M.loaded_segments (0x7dc98 : word) = Some W_7dc98.
Proof. vm_refl. Qed.
Lemma D_7dc98 : decode_any W_7dc98 = Some (Store SZ8 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dc9c : bv 32 := 0x00429613.
Lemma F_7dc9c : fetch_word AsanUbsan.M.loaded_segments (0x7dc9c : word) = Some W_7dc9c.
Proof. vm_refl. Qed.
Lemma D_7dc9c : decode_any W_7dc9c = Some (ShiftImm ALU_SLL 12 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dca0 : bv 32 := 0x00c58633.
Lemma F_7dca0 : fetch_word AsanUbsan.M.loaded_segments (0x7dca0 : word) = Some W_7dca0.
Proof. vm_refl. Qed.
Lemma D_7dca0 : decode_any W_7dca0 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dca4 : bv 32 := 0x01063503.
Lemma F_7dca4 : fetch_word AsanUbsan.M.loaded_segments (0x7dca4 : word) = Some W_7dca4.
Proof. vm_refl. Qed.
Lemma D_7dca4 : decode_any W_7dca4 = Some (Load SZ8 true 10 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dca8 : bv 32 := 0x0a050a63.
Lemma F_7dca8 : fetch_word AsanUbsan.M.loaded_segments (0x7dca8 : word) = Some W_7dca8.
Proof. vm_refl. Qed.
Lemma D_7dca8 : decode_any W_7dca8 = Some (Branch BC_EQ 10 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dcac : bv 32 := 0x02c41413.
Lemma F_7dcac : fetch_word AsanUbsan.M.loaded_segments (0x7dcac : word) = Some W_7dcac.
Proof. vm_refl. Qed.
Lemma D_7dcac : decode_any W_7dcac = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dcb0 : bv 32 := 0x02945413.
Lemma F_7dcb0 : fetch_word AsanUbsan.M.loaded_segments (0x7dcb0 : word) = Some W_7dcb0.
Proof. vm_refl. Qed.
Lemma D_7dcb0 : decode_any W_7dcb0 = Some (ShiftImm ALU_SRL 8 8 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dcb4 : bv 32 := 0x00850533.
Lemma F_7dcb4 : fetch_word AsanUbsan.M.loaded_segments (0x7dcb4 : word) = Some W_7dcb4.
Proof. vm_refl. Qed.
Lemma D_7dcb4 : decode_any W_7dcb4 = Some (Op ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dcb8 : bv 32 := 0x00813083.
Lemma F_7dcb8 : fetch_word AsanUbsan.M.loaded_segments (0x7dcb8 : word) = Some W_7dcb8.
Proof. vm_refl. Qed.
Lemma D_7dcb8 : decode_any W_7dcb8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dcbc : bv 32 := 0x00013403.
Lemma F_7dcbc : fetch_word AsanUbsan.M.loaded_segments (0x7dcbc : word) = Some W_7dcbc.
Proof. vm_refl. Qed.
Lemma D_7dcbc : decode_any W_7dcbc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dcc0 : bv 32 := 0x01010113.
Lemma F_7dcc0 : fetch_word AsanUbsan.M.loaded_segments (0x7dcc0 : word) = Some W_7dcc0.
Proof. vm_refl. Qed.
Lemma D_7dcc0 : decode_any W_7dcc0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dcc4 : bv 32 := 0x00008067.
Lemma F_7dcc4 : fetch_word AsanUbsan.M.loaded_segments (0x7dcc4 : word) = Some W_7dcc4.
Proof. vm_refl. Qed.
Lemma D_7dcc4 : decode_any W_7dcc4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dcc8 : bv 32 := 0x00100737.
Lemma F_7dcc8 : fetch_word AsanUbsan.M.loaded_segments (0x7dcc8 : word) = Some W_7dcc8.
Proof. vm_refl. Qed.
Lemma D_7dcc8 : decode_any W_7dcc8 = Some (Lui 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dccc : bv 32 := 0x08f76e63.
Lemma F_7dccc : fetch_word AsanUbsan.M.loaded_segments (0x7dccc : word) = Some W_7dccc.
Proof. vm_refl. Qed.
Lemma D_7dccc : decode_any W_7dccc = Some (Branch BC_LTU 14 15 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dcd0 : bv 32 := 0x01058813.
Lemma F_7dcd0 : fetch_word AsanUbsan.M.loaded_segments (0x7dcd0 : word) = Some W_7dcd0.
Proof. vm_refl. Qed.
Lemma D_7dcd0 : decode_any W_7dcd0 = Some (OpImm ALU_ADD 16 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dcd4 : bv 32 := 0xfff7089b.
Lemma F_7dcd4 : fetch_word AsanUbsan.M.loaded_segments (0x7dcd4 : word) = Some W_7dcd4.
Proof. vm_refl. Qed.
Lemma D_7dcd4 : decode_any W_7dcd4 = Some (OpImm32 17 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dcd8 : bv 32 := 0x011473b3.
Lemma F_7dcd8 : fetch_word AsanUbsan.M.loaded_segments (0x7dcd8 : word) = Some W_7dcd8.
Proof. vm_refl. Qed.
Lemma D_7dcd8 : decode_any W_7dcd8 = Some (Op ALU_AND 7 8 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dcdc : bv 32 := 0x00429293.
Lemma F_7dcdc : fetch_word AsanUbsan.M.loaded_segments (0x7dcdc : word) = Some W_7dcdc.
Proof. vm_refl. Qed.
Lemma D_7dcdc : decode_any W_7dcdc = Some (ShiftImm ALU_SLL 5 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dce0 : bv 32 := 0x407703b3.
Lemma F_7dce0 : fetch_word AsanUbsan.M.loaded_segments (0x7dce0 : word) = Some W_7dce0.
Proof. vm_refl. Qed.
Lemma D_7dce0 : decode_any W_7dce0 = Some (Op ALU_SUB 7 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dce4 : bv 32 := 0x005802b3.
Lemma F_7dce4 : fetch_word AsanUbsan.M.loaded_segments (0x7dce4 : word) = Some W_7dce4.
Proof. vm_refl. Qed.
Lemma D_7dce4 : decode_any W_7dce4 = Some (Op ALU_ADD 5 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dce8 : bv 32 := 0x00828293.
Lemma F_7dce8 : fetch_word AsanUbsan.M.loaded_segments (0x7dce8 : word) = Some W_7dce8.
Proof. vm_refl. Qed.
Lemma D_7dce8 : decode_any W_7dce8 = Some (OpImm ALU_ADD 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dcec : bv 32 := 0x0272a2af.
Lemma F_7dcec : fetch_word AsanUbsan.M.loaded_segments (0x7dcec : word) = Some W_7dcec.
Proof. vm_refl. Qed.
Lemma D_7dcec : decode_any W_7dcec = Some (Amo AMO_ADD AW false true 5 5 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dcf0 : bv 32 := 0x00431313.
Lemma F_7dcf0 : fetch_word AsanUbsan.M.loaded_segments (0x7dcf0 : word) = Some W_7dcf0.
Proof. vm_refl. Qed.
Lemma D_7dcf0 : decode_any W_7dcf0 = Some (ShiftImm ALU_SLL 6 6 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dcf4 : bv 32 := 0x00680333.
Lemma F_7dcf4 : fetch_word AsanUbsan.M.loaded_segments (0x7dcf4 : word) = Some W_7dcf4.
Proof. vm_refl. Qed.
Lemma D_7dcf4 : decode_any W_7dcf4 = Some (Op ALU_ADD 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dcf8 : bv 32 := 0x40778e33.
Lemma F_7dcf8 : fetch_word AsanUbsan.M.loaded_segments (0x7dcf8 : word) = Some W_7dcf8.
Proof. vm_refl. Qed.
Lemma D_7dcf8 : decode_any W_7dcf8 = Some (Op ALU_SUB 28 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dcfc : bv 32 := 0x02029293.
Lemma F_7dcfc : fetch_word AsanUbsan.M.loaded_segments (0x7dcfc : word) = Some W_7dcfc.
Proof. vm_refl. Qed.
Lemma D_7dcfc : decode_any W_7dcfc = Some (ShiftImm ALU_SLL 5 5 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd00 : bv 32 := 0x0202d293.
Lemma F_7dd00 : fetch_word AsanUbsan.M.loaded_segments (0x7dd00 : word) = Some W_7dd00.
Proof. vm_refl. Qed.
Lemma D_7dd00 : decode_any W_7dd00 = Some (ShiftImm ALU_SRL 5 5 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd04 : bv 32 := 0x005382b3.
Lemma F_7dd04 : fetch_word AsanUbsan.M.loaded_segments (0x7dd04 : word) = Some W_7dd04.
Proof. vm_refl. Qed.
Lemma D_7dd04 : decode_any W_7dd04 = Some (Op ALU_ADD 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd08 : bv 32 := 0x0006b383.
Lemma F_7dd08 : fetch_word AsanUbsan.M.loaded_segments (0x7dd08 : word) = Some W_7dd08.
Proof. vm_refl. Qed.
Lemma D_7dd08 : decode_any W_7dd08 = Some (Load SZ8 true 7 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd0c : bv 32 := 0x00830313.
Lemma F_7dd0c : fetch_word AsanUbsan.M.loaded_segments (0x7dd0c : word) = Some W_7dd0c.
Proof. vm_refl. Qed.
Lemma D_7dd0c : decode_any W_7dd0c = Some (OpImm ALU_ADD 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd10 : bv 32 := 0x00e2c2b3.
Lemma F_7dd10 : fetch_word AsanUbsan.M.loaded_segments (0x7dd10 : word) = Some W_7dd10.
Proof. vm_refl. Qed.
Lemma D_7dd10 : decode_any W_7dd10 = Some (Op ALU_XOR 5 5 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd14 : bv 32 := 0x0012b293.
Lemma F_7dd14 : fetch_word AsanUbsan.M.loaded_segments (0x7dd14 : word) = Some W_7dd14.
Proof. vm_refl. Qed.
Lemma D_7dd14 : decode_any W_7dd14 = Some (OpImm ALU_SLTU 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd18 : bv 32 := 0x005382b3.
Lemma F_7dd18 : fetch_word AsanUbsan.M.loaded_segments (0x7dd18 : word) = Some W_7dd18.
Proof. vm_refl. Qed.
Lemma D_7dd18 : decode_any W_7dd18 = Some (Op ALU_ADD 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd1c : bv 32 := 0x0056b023.
Lemma F_7dd1c : fetch_word AsanUbsan.M.loaded_segments (0x7dd1c : word) = Some W_7dd1c.
Proof. vm_refl. Qed.
Lemma D_7dd1c : decode_any W_7dd1c = Some (Store SZ8 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd20 : bv 32 := 0x03c322af.
Lemma F_7dd20 : fetch_word AsanUbsan.M.loaded_segments (0x7dd20 : word) = Some W_7dd20.
Proof. vm_refl. Qed.
Lemma D_7dd20 : decode_any W_7dd20 = Some (Amo AMO_ADD AW false true 5 6 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd24 : bv 32 := 0x0006b303.
Lemma F_7dd24 : fetch_word AsanUbsan.M.loaded_segments (0x7dd24 : word) = Some W_7dd24.
Proof. vm_refl. Qed.
Lemma D_7dd24 : decode_any W_7dd24 = Some (Load SZ8 true 6 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd28 : bv 32 := 0x02029293.
Lemma F_7dd28 : fetch_word AsanUbsan.M.loaded_segments (0x7dd28 : word) = Some W_7dd28.
Proof. vm_refl. Qed.
Lemma D_7dd28 : decode_any W_7dd28 = Some (ShiftImm ALU_SLL 5 5 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd2c : bv 32 := 0x0202d293.
Lemma F_7dd2c : fetch_word AsanUbsan.M.loaded_segments (0x7dd2c : word) = Some W_7dd2c.
Proof. vm_refl. Qed.
Lemma D_7dd2c : decode_any W_7dd2c = Some (ShiftImm ALU_SRL 5 5 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd30 : bv 32 := 0x005e02b3.
Lemma F_7dd30 : fetch_word AsanUbsan.M.loaded_segments (0x7dd30 : word) = Some W_7dd30.
Proof. vm_refl. Qed.
Lemma D_7dd30 : decode_any W_7dd30 = Some (Op ALU_ADD 5 28 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd34 : bv 32 := 0x00e2c2b3.
Lemma F_7dd34 : fetch_word AsanUbsan.M.loaded_segments (0x7dd34 : word) = Some W_7dd34.
Proof. vm_refl. Qed.
Lemma D_7dd34 : decode_any W_7dd34 = Some (Op ALU_XOR 5 5 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd38 : bv 32 := 0x0012b293.
Lemma F_7dd38 : fetch_word AsanUbsan.M.loaded_segments (0x7dd38 : word) = Some W_7dd38.
Proof. vm_refl. Qed.
Lemma D_7dd38 : decode_any W_7dd38 = Some (OpImm ALU_SLTU 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd3c : bv 32 := 0x005302b3.
Lemma F_7dd3c : fetch_word AsanUbsan.M.loaded_segments (0x7dd3c : word) = Some W_7dd3c.
Proof. vm_refl. Qed.
Lemma D_7dd3c : decode_any W_7dd3c = Some (Op ALU_ADD 5 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd40 : bv 32 := 0x0056b023.
Lemma F_7dd40 : fetch_word AsanUbsan.M.loaded_segments (0x7dd40 : word) = Some W_7dd40.
Proof. vm_refl. Qed.
Lemma D_7dd40 : decode_any W_7dd40 = Some (Store SZ8 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd44 : bv 32 := 0x00f5b42f.
Lemma F_7dd44 : fetch_word AsanUbsan.M.loaded_segments (0x7dd44 : word) = Some W_7dd44.
Proof. vm_refl. Qed.
Lemma D_7dd44 : decode_any W_7dd44 = Some (Amo AMO_ADD AD false false 8 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd48 : bv 32 := 0x01445293.
Lemma F_7dd48 : fetch_word AsanUbsan.M.loaded_segments (0x7dd48 : word) = Some W_7dd48.
Proof. vm_refl. Qed.
Lemma D_7dd48 : decode_any W_7dd48 = Some (ShiftImm ALU_SRL 5 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd4c : bv 32 := 0x00850333.
Lemma F_7dd4c : fetch_word AsanUbsan.M.loaded_segments (0x7dd4c : word) = Some W_7dd4c.
Proof. vm_refl. Qed.
Lemma D_7dd4c : decode_any W_7dd4c = Some (Op ALU_ADD 6 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd50 : bv 32 := 0x01435313.
Lemma F_7dd50 : fetch_word AsanUbsan.M.loaded_segments (0x7dd50 : word) = Some W_7dd50.
Proof. vm_refl. Qed.
Lemma D_7dd50 : decode_any W_7dd50 = Some (ShiftImm ALU_SRL 6 6 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd54 : bv 32 := 0xf26284e3.
Lemma F_7dd54 : fetch_word AsanUbsan.M.loaded_segments (0x7dd54 : word) = Some W_7dd54.
Proof. vm_refl. Qed.
Lemma D_7dd54 : decode_any W_7dd54 = Some (Branch BC_EQ 5 6 7976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd58 : bv 32 := 0xf81ff06f.
Lemma F_7dd58 : fetch_word AsanUbsan.M.loaded_segments (0x7dd58 : word) = Some W_7dd58.
Proof. vm_refl. Qed.
Lemma D_7dd58 : decode_any W_7dd58 = Some (Jal 0 2097024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd5c : bv 32 := 0x01060513.
Lemma F_7dd5c : fetch_word AsanUbsan.M.loaded_segments (0x7dd5c : word) = Some W_7dd5c.
Proof. vm_refl. Qed.
Lemma D_7dd5c : decode_any W_7dd5c = Some (OpImm ALU_ADD 10 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd60 : bv 32 := 0x0d9000ef.
Lemma F_7dd60 : fetch_word AsanUbsan.M.loaded_segments (0x7dd60 : word) = Some W_7dd60.
Proof. vm_refl. Qed.
Lemma D_7dd60 : decode_any W_7dd60 = Some (Jal 1 2264, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd64 : bv 32 := 0xf49ff06f.
Lemma F_7dd64 : fetch_word AsanUbsan.M.loaded_segments (0x7dd64 : word) = Some W_7dd64.
Proof. vm_refl. Qed.
Lemma D_7dd64 : decode_any W_7dd64 = Some (Jal 0 2096968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd68 : bv 32 := 0xfffa3517.
Lemma F_7dd68 : fetch_word AsanUbsan.M.loaded_segments (0x7dd68 : word) = Some W_7dd68.
Proof. vm_refl. Qed.
Lemma D_7dd68 : decode_any W_7dd68 = Some (Auipc 10 1048483, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd6c : bv 32 := 0xfff9d617.
Lemma F_7dd6c : fetch_word AsanUbsan.M.loaded_segments (0x7dd6c : word) = Some W_7dd6c.
Proof. vm_refl. Qed.
Lemma D_7dd6c : decode_any W_7dd6c = Some (Auipc 12 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd70 : bv 32 := 0x05b00593.
Lemma F_7dd70 : fetch_word AsanUbsan.M.loaded_segments (0x7dd70 : word) = Some W_7dd70.
Proof. vm_refl. Qed.
Lemma D_7dd70 : decode_any W_7dd70 = Some (OpImm ALU_ADD 11 0 91, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd74 : bv 32 := 0x33050513.
Lemma F_7dd74 : fetch_word AsanUbsan.M.loaded_segments (0x7dd74 : word) = Some W_7dd74.
Proof. vm_refl. Qed.
Lemma D_7dd74 : decode_any W_7dd74 = Some (OpImm ALU_ADD 10 10 816, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd78 : bv 32 := 0xeca60613.
Lemma F_7dd78 : fetch_word AsanUbsan.M.loaded_segments (0x7dd78 : word) = Some W_7dd78.
Proof. vm_refl. Qed.
Lemma D_7dd78 : decode_any W_7dd78 = Some (OpImm ALU_ADD 12 12 3786, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd7c : bv 32 := 0x00078693.
Lemma F_7dd7c : fetch_word AsanUbsan.M.loaded_segments (0x7dd7c : word) = Some W_7dd7c.
Proof. vm_refl. Qed.
Lemma D_7dd7c : decode_any W_7dd7c = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dd80 : bv 32 := 0xd68fb0ef.
Lemma F_7dd80 : fetch_word AsanUbsan.M.loaded_segments (0x7dd80 : word) = Some W_7dd80.
Proof. vm_refl. Qed.
Lemma D_7dd80 : decode_any W_7dd80 = Some (Jal 1 2078056, 4%Z).
Proof. vm_refl. Qed.
