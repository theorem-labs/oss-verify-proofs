(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition Wx_66b70 : bv 32 := 0xfa010113.
Lemma Fx_66b70 : fetch_word Asan.M.loaded_segments (0x66bc0 : word) = Some Wx_66b70.
Proof. vm_refl. Qed.
Lemma Dx_66b70 : decode_any Wx_66b70 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66b74 : bv 32 := 0x04113c23.
Lemma Fx_66b74 : fetch_word Asan.M.loaded_segments (0x66bc4 : word) = Some Wx_66b74.
Proof. vm_refl. Qed.
Lemma Dx_66b74 : decode_any Wx_66b74 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66b78 : bv 32 := 0x04813823.
Lemma Fx_66b78 : fetch_word Asan.M.loaded_segments (0x66bc8 : word) = Some Wx_66b78.
Proof. vm_refl. Qed.
Lemma Dx_66b78 : decode_any Wx_66b78 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66b7c : bv 32 := 0x04913423.
Lemma Fx_66b7c : fetch_word Asan.M.loaded_segments (0x66bcc : word) = Some Wx_66b7c.
Proof. vm_refl. Qed.
Lemma Dx_66b7c : decode_any Wx_66b7c = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66b80 : bv 32 := 0x05213023.
Lemma Fx_66b80 : fetch_word Asan.M.loaded_segments (0x66bd0 : word) = Some Wx_66b80.
Proof. vm_refl. Qed.
Lemma Dx_66b80 : decode_any Wx_66b80 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66b84 : bv 32 := 0x03313c23.
Lemma Fx_66b84 : fetch_word Asan.M.loaded_segments (0x66bd4 : word) = Some Wx_66b84.
Proof. vm_refl. Qed.
Lemma Dx_66b84 : decode_any Wx_66b84 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66b88 : bv 32 := 0x03413823.
Lemma Fx_66b88 : fetch_word Asan.M.loaded_segments (0x66bd8 : word) = Some Wx_66b88.
Proof. vm_refl. Qed.
Lemma Dx_66b88 : decode_any Wx_66b88 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66b8c : bv 32 := 0x03513423.
Lemma Fx_66b8c : fetch_word Asan.M.loaded_segments (0x66bdc : word) = Some Wx_66b8c.
Proof. vm_refl. Qed.
Lemma Dx_66b8c : decode_any Wx_66b8c = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66b90 : bv 32 := 0x03613023.
Lemma Fx_66b90 : fetch_word Asan.M.loaded_segments (0x66be0 : word) = Some Wx_66b90.
Proof. vm_refl. Qed.
Lemma Dx_66b90 : decode_any Wx_66b90 = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66b94 : bv 32 := 0x01713c23.
Lemma Fx_66b94 : fetch_word Asan.M.loaded_segments (0x66be4 : word) = Some Wx_66b94.
Proof. vm_refl. Qed.
Lemma Dx_66b94 : decode_any Wx_66b94 = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66b98 : bv 32 := 0x01813823.
Lemma Fx_66b98 : fetch_word Asan.M.loaded_segments (0x66be8 : word) = Some Wx_66b98.
Proof. vm_refl. Qed.
Lemma Dx_66b98 : decode_any Wx_66b98 = Some (Store SZ8 2 24 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66b9c : bv 32 := 0x01913423.
Lemma Fx_66b9c : fetch_word Asan.M.loaded_segments (0x66bec : word) = Some Wx_66b9c.
Proof. vm_refl. Qed.
Lemma Dx_66b9c : decode_any Wx_66b9c = Some (Store SZ8 2 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66ba0 : bv 32 := 0x000ec517.
Lemma Fx_66ba0 : fetch_word Asan.M.loaded_segments (0x66bf0 : word) = Some Wx_66ba0.
Proof. vm_refl. Qed.
Lemma Dx_66ba0 : decode_any Wx_66ba0 = Some (Auipc 10 236, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66ba4 : bv 32 := 0x54053a03.
Lemma Fx_66ba4 : fetch_word Asan.M.loaded_segments (0x66bf4 : word) = Some Wx_66ba4.
Proof. vm_refl. Qed.
Lemma Dx_66ba4 : decode_any Wx_66ba4 = Some (Load SZ8 true 20 10 1344, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66ba8 : bv 32 := 0x01ca4503.
Lemma Fx_66ba8 : fetch_word Asan.M.loaded_segments (0x66bf8 : word) = Some Wx_66ba8.
Proof. vm_refl. Qed.
Lemma Dx_66ba8 : decode_any Wx_66ba8 = Some (Load SZ1 false 10 20 28, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66bac : bv 32 := 0x1e050e63.
Lemma Fx_66bac : fetch_word Asan.M.loaded_segments (0x66bfc : word) = Some Wx_66bac.
Proof. vm_refl. Qed.
Lemma Dx_66bac : decode_any Wx_66bac = Some (Branch BC_EQ 10 0 508, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66da8 : bv 32 := 0x05813083.
Lemma Fx_66da8 : fetch_word Asan.M.loaded_segments (0x66df8 : word) = Some Wx_66da8.
Proof. vm_refl. Qed.
Lemma Dx_66da8 : decode_any Wx_66da8 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66dac : bv 32 := 0x05013403.
Lemma Fx_66dac : fetch_word Asan.M.loaded_segments (0x66dfc : word) = Some Wx_66dac.
Proof. vm_refl. Qed.
Lemma Dx_66dac : decode_any Wx_66dac = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66db0 : bv 32 := 0x04813483.
Lemma Fx_66db0 : fetch_word Asan.M.loaded_segments (0x66e00 : word) = Some Wx_66db0.
Proof. vm_refl. Qed.
Lemma Dx_66db0 : decode_any Wx_66db0 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66db4 : bv 32 := 0x04013903.
Lemma Fx_66db4 : fetch_word Asan.M.loaded_segments (0x66e04 : word) = Some Wx_66db4.
Proof. vm_refl. Qed.
Lemma Dx_66db4 : decode_any Wx_66db4 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66db8 : bv 32 := 0x03813983.
Lemma Fx_66db8 : fetch_word Asan.M.loaded_segments (0x66e08 : word) = Some Wx_66db8.
Proof. vm_refl. Qed.
Lemma Dx_66db8 : decode_any Wx_66db8 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66dbc : bv 32 := 0x03013a03.
Lemma Fx_66dbc : fetch_word Asan.M.loaded_segments (0x66e0c : word) = Some Wx_66dbc.
Proof. vm_refl. Qed.
Lemma Dx_66dbc : decode_any Wx_66dbc = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66dc0 : bv 32 := 0x02813a83.
Lemma Fx_66dc0 : fetch_word Asan.M.loaded_segments (0x66e10 : word) = Some Wx_66dc0.
Proof. vm_refl. Qed.
Lemma Dx_66dc0 : decode_any Wx_66dc0 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66dc4 : bv 32 := 0x02013b03.
Lemma Fx_66dc4 : fetch_word Asan.M.loaded_segments (0x66e14 : word) = Some Wx_66dc4.
Proof. vm_refl. Qed.
Lemma Dx_66dc4 : decode_any Wx_66dc4 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66dc8 : bv 32 := 0x01813b83.
Lemma Fx_66dc8 : fetch_word Asan.M.loaded_segments (0x66e18 : word) = Some Wx_66dc8.
Proof. vm_refl. Qed.
Lemma Dx_66dc8 : decode_any Wx_66dc8 = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66dcc : bv 32 := 0x01013c03.
Lemma Fx_66dcc : fetch_word Asan.M.loaded_segments (0x66e1c : word) = Some Wx_66dcc.
Proof. vm_refl. Qed.
Lemma Dx_66dcc : decode_any Wx_66dcc = Some (Load SZ8 true 24 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66dd0 : bv 32 := 0x00813c83.
Lemma Fx_66dd0 : fetch_word Asan.M.loaded_segments (0x66e20 : word) = Some Wx_66dd0.
Proof. vm_refl. Qed.
Lemma Dx_66dd0 : decode_any Wx_66dd0 = Some (Load SZ8 true 25 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66dd4 : bv 32 := 0x06010113.
Lemma Fx_66dd4 : fetch_word Asan.M.loaded_segments (0x66e24 : word) = Some Wx_66dd4.
Proof. vm_refl. Qed.
Lemma Dx_66dd4 : decode_any Wx_66dd4 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_66dd8 : bv 32 := 0x00008067.
Lemma Fx_66dd8 : fetch_word Asan.M.loaded_segments (0x66e28 : word) = Some Wx_66dd8.
Proof. vm_refl. Qed.
Lemma Dx_66dd8 : decode_any Wx_66dd8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6a5dc : bv 32 := 0x5cc0a06f.
Lemma Fx_6a5dc : fetch_word Asan.M.loaded_segments (0x6a62c : word) = Some Wx_6a5dc.
Proof. vm_refl. Qed.
Lemma Dx_6a5dc : decode_any Wx_6a5dc = Some (Jal 0 42444, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74ba8 : bv 32 := 0xfd010113.
Lemma Fx_74ba8 : fetch_word Asan.M.loaded_segments (0x74bf8 : word) = Some Wx_74ba8.
Proof. vm_refl. Qed.
Lemma Dx_74ba8 : decode_any Wx_74ba8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bac : bv 32 := 0x02113423.
Lemma Fx_74bac : fetch_word Asan.M.loaded_segments (0x74bfc : word) = Some Wx_74bac.
Proof. vm_refl. Qed.
Lemma Dx_74bac : decode_any Wx_74bac = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bb0 : bv 32 := 0x02813023.
Lemma Fx_74bb0 : fetch_word Asan.M.loaded_segments (0x74c00 : word) = Some Wx_74bb0.
Proof. vm_refl. Qed.
Lemma Dx_74bb0 : decode_any Wx_74bb0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bb4 : bv 32 := 0x00913c23.
Lemma Fx_74bb4 : fetch_word Asan.M.loaded_segments (0x74c04 : word) = Some Wx_74bb4.
Proof. vm_refl. Qed.
Lemma Dx_74bb4 : decode_any Wx_74bb4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bb8 : bv 32 := 0x01213823.
Lemma Fx_74bb8 : fetch_word Asan.M.loaded_segments (0x74c08 : word) = Some Wx_74bb8.
Proof. vm_refl. Qed.
Lemma Dx_74bb8 : decode_any Wx_74bb8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bbc : bv 32 := 0x01313423.
Lemma Fx_74bbc : fetch_word Asan.M.loaded_segments (0x74c0c : word) = Some Wx_74bbc.
Proof. vm_refl. Qed.
Lemma Dx_74bbc : decode_any Wx_74bbc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bc0 : bv 32 := 0x00060413.
Lemma Fx_74bc0 : fetch_word Asan.M.loaded_segments (0x74c10 : word) = Some Wx_74bc0.
Proof. vm_refl. Qed.
Lemma Dx_74bc0 : decode_any Wx_74bc0 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bc4 : bv 32 := 0x00058493.
Lemma Fx_74bc4 : fetch_word Asan.M.loaded_segments (0x74c14 : word) = Some Wx_74bc4.
Proof. vm_refl. Qed.
Lemma Dx_74bc4 : decode_any Wx_74bc4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bc8 : bv 32 := 0x00050913.
Lemma Fx_74bc8 : fetch_word Asan.M.loaded_segments (0x74c18 : word) = Some Wx_74bc8.
Proof. vm_refl. Qed.
Lemma Dx_74bc8 : decode_any Wx_74bc8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bcc : bv 32 := 0x364130ef.
Lemma Fx_74bcc : fetch_word Asan.M.loaded_segments (0x74c1c : word) = Some Wx_74bcc.
Proof. vm_refl. Qed.
Lemma Dx_74bcc : decode_any Wx_74bcc = Some (Jal 1 78692, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bd0 : bv 32 := 0x29d390ef.
Lemma Fx_74bd0 : fetch_word Asan.M.loaded_segments (0x74c20 : word) = Some Wx_74bd0.
Proof. vm_refl. Qed.
Lemma Dx_74bd0 : decode_any Wx_74bd0 = Some (Jal 1 236188, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bd4 : bv 32 := 0x000e0997.
Lemma Fx_74bd4 : fetch_word Asan.M.loaded_segments (0x74c24 : word) = Some Wx_74bd4.
Proof. vm_refl. Qed.
Lemma Dx_74bd4 : decode_any Wx_74bd4 = Some (Auipc 19 224, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bd8 : bv 32 := 0x4dc9b683.
Lemma Fx_74bd8 : fetch_word Asan.M.loaded_segments (0x74c28 : word) = Some Wx_74bd8.
Proof. vm_refl. Qed.
Lemma Dx_74bd8 : decode_any Wx_74bd8 = Some (Load SZ8 true 13 19 1244, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bdc : bv 32 := 0x00090513.
Lemma Fx_74bdc : fetch_word Asan.M.loaded_segments (0x74c2c : word) = Some Wx_74bdc.
Proof. vm_refl. Qed.
Lemma Dx_74bdc : decode_any Wx_74bdc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74be0 : bv 32 := 0x00048593.
Lemma Fx_74be0 : fetch_word Asan.M.loaded_segments (0x74c30 : word) = Some Wx_74be0.
Proof. vm_refl. Qed.
Lemma Dx_74be0 : decode_any Wx_74be0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74be4 : bv 32 := 0x00040613.
Lemma Fx_74be4 : fetch_word Asan.M.loaded_segments (0x74c34 : word) = Some Wx_74be4.
Proof. vm_refl. Qed.
Lemma Dx_74be4 : decode_any Wx_74be4 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74be8 : bv 32 := 0x000680e7.
Lemma Fx_74be8 : fetch_word Asan.M.loaded_segments (0x74c38 : word) = Some Wx_74be8.
Proof. vm_refl. Qed.
Lemma Dx_74be8 : decode_any Wx_74be8 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bec : bv 32 := 0x4dc9b683.
Lemma Fx_74bec : fetch_word Asan.M.loaded_segments (0x74c3c : word) = Some Wx_74bec.
Proof. vm_refl. Qed.
Lemma Dx_74bec : decode_any Wx_74bec = Some (Load SZ8 true 13 19 1244, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bf0 : bv 32 := 0x00050413.
Lemma Fx_74bf0 : fetch_word Asan.M.loaded_segments (0x74c40 : word) = Some Wx_74bf0.
Proof. vm_refl. Qed.
Lemma Dx_74bf0 : decode_any Wx_74bf0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bf4 : bv 32 := 0x00000517.
Lemma Fx_74bf4 : fetch_word Asan.M.loaded_segments (0x74c44 : word) = Some Wx_74bf4.
Proof. vm_refl. Qed.
Lemma Dx_74bf4 : decode_any Wx_74bf4 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bf8 : bv 32 := 0x03850513.
Lemma Fx_74bf8 : fetch_word Asan.M.loaded_segments (0x74c48 : word) = Some Wx_74bf8.
Proof. vm_refl. Qed.
Lemma Dx_74bf8 : decode_any Wx_74bf8 = Some (OpImm ALU_ADD 10 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74bfc : bv 32 := 0x00000593.
Lemma Fx_74bfc : fetch_word Asan.M.loaded_segments (0x74c4c : word) = Some Wx_74bfc.
Proof. vm_refl. Qed.
Lemma Dx_74bfc : decode_any Wx_74bfc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74c00 : bv 32 := 0x00000613.
Lemma Fx_74c00 : fetch_word Asan.M.loaded_segments (0x74c50 : word) = Some Wx_74c00.
Proof. vm_refl. Qed.
Lemma Dx_74c00 : decode_any Wx_74c00 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74c04 : bv 32 := 0x000680e7.
Lemma Fx_74c04 : fetch_word Asan.M.loaded_segments (0x74c54 : word) = Some Wx_74c04.
Proof. vm_refl. Qed.
Lemma Dx_74c04 : decode_any Wx_74c04 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74c08 : bv 32 := 0x281390ef.
Lemma Fx_74c08 : fetch_word Asan.M.loaded_segments (0x74c58 : word) = Some Wx_74c08.
Proof. vm_refl. Qed.
Lemma Dx_74c08 : decode_any Wx_74c08 = Some (Jal 1 236160, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74c0c : bv 32 := 0x00040513.
Lemma Fx_74c0c : fetch_word Asan.M.loaded_segments (0x74c5c : word) = Some Wx_74c0c.
Proof. vm_refl. Qed.
Lemma Dx_74c0c : decode_any Wx_74c0c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74c10 : bv 32 := 0x02813083.
Lemma Fx_74c10 : fetch_word Asan.M.loaded_segments (0x74c60 : word) = Some Wx_74c10.
Proof. vm_refl. Qed.
Lemma Dx_74c10 : decode_any Wx_74c10 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74c14 : bv 32 := 0x02013403.
Lemma Fx_74c14 : fetch_word Asan.M.loaded_segments (0x74c64 : word) = Some Wx_74c14.
Proof. vm_refl. Qed.
Lemma Dx_74c14 : decode_any Wx_74c14 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74c18 : bv 32 := 0x01813483.
Lemma Fx_74c18 : fetch_word Asan.M.loaded_segments (0x74c68 : word) = Some Wx_74c18.
Proof. vm_refl. Qed.
Lemma Dx_74c18 : decode_any Wx_74c18 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74c1c : bv 32 := 0x01013903.
Lemma Fx_74c1c : fetch_word Asan.M.loaded_segments (0x74c6c : word) = Some Wx_74c1c.
Proof. vm_refl. Qed.
Lemma Dx_74c1c : decode_any Wx_74c1c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74c20 : bv 32 := 0x00813983.
Lemma Fx_74c20 : fetch_word Asan.M.loaded_segments (0x74c70 : word) = Some Wx_74c20.
Proof. vm_refl. Qed.
Lemma Dx_74c20 : decode_any Wx_74c20 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74c24 : bv 32 := 0x03010113.
Lemma Fx_74c24 : fetch_word Asan.M.loaded_segments (0x74c74 : word) = Some Wx_74c24.
Proof. vm_refl. Qed.
Lemma Dx_74c24 : decode_any Wx_74c24 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74c28 : bv 32 := 0x00008067.
Lemma Fx_74c28 : fetch_word Asan.M.loaded_segments (0x74c78 : word) = Some Wx_74c28.
Proof. vm_refl. Qed.
Lemma Dx_74c28 : decode_any Wx_74c28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_74c2c : bv 32 := 0xf45f106f.
Lemma Fx_74c2c : fetch_word Asan.M.loaded_segments (0x74c7c : word) = Some Wx_74c2c.
Proof. vm_refl. Qed.
Lemma Dx_74c2c : decode_any Wx_74c2c = Some (Jal 0 2039620, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87f30 : bv 32 := 0xff010113.
Lemma Fx_87f30 : fetch_word Asan.M.loaded_segments (0x87f80 : word) = Some Wx_87f30.
Proof. vm_refl. Qed.
Lemma Dx_87f30 : decode_any Wx_87f30 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87f34 : bv 32 := 0x00113423.
Lemma Fx_87f34 : fetch_word Asan.M.loaded_segments (0x87f84 : word) = Some Wx_87f34.
Proof. vm_refl. Qed.
Lemma Dx_87f34 : decode_any Wx_87f34 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87f38 : bv 32 := 0x00813023.
Lemma Fx_87f38 : fetch_word Asan.M.loaded_segments (0x87f88 : word) = Some Wx_87f38.
Proof. vm_refl. Qed.
Lemma Dx_87f38 : decode_any Wx_87f38 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87f3c : bv 32 := 0x000d5517.
Lemma Fx_87f3c : fetch_word Asan.M.loaded_segments (0x87f8c : word) = Some Wx_87f3c.
Proof. vm_refl. Qed.
Lemma Dx_87f3c : decode_any Wx_87f3c = Some (Auipc 10 213, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87f40 : bv 32 := 0x70c50413.
Lemma Fx_87f40 : fetch_word Asan.M.loaded_segments (0x87f90 : word) = Some Wx_87f40.
Proof. vm_refl. Qed.
Lemma Dx_87f40 : decode_any Wx_87f40 = Some (OpImm ALU_ADD 8 10 1804, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87f44 : bv 32 := 0x00040503.
Lemma Fx_87f44 : fetch_word Asan.M.loaded_segments (0x87f94 : word) = Some Wx_87f44.
Proof. vm_refl. Qed.
Lemma Dx_87f44 : decode_any Wx_87f44 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87f48 : bv 32 := 0x00100593.
Lemma Fx_87f48 : fetch_word Asan.M.loaded_segments (0x87f98 : word) = Some Wx_87f48.
Proof. vm_refl. Qed.
Lemma Dx_87f48 : decode_any Wx_87f48 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87f4c : bv 32 := 0x0230000f.
Lemma Fx_87f4c : fetch_word Asan.M.loaded_segments (0x87f9c : word) = Some Wx_87f4c.
Proof. vm_refl. Qed.
Lemma Dx_87f4c : decode_any Wx_87f4c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87f50 : bv 32 := 0x00b51a63.
Lemma Fx_87f50 : fetch_word Asan.M.loaded_segments (0x87fa0 : word) = Some Wx_87f50.
Proof. vm_refl. Qed.
Lemma Dx_87f50 : decode_any Wx_87f50 = Some (Branch BC_NE 10 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87f54 : bv 32 := 0x00813083.
Lemma Fx_87f54 : fetch_word Asan.M.loaded_segments (0x87fa4 : word) = Some Wx_87f54.
Proof. vm_refl. Qed.
Lemma Dx_87f54 : decode_any Wx_87f54 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87f58 : bv 32 := 0x00013403.
Lemma Fx_87f58 : fetch_word Asan.M.loaded_segments (0x87fa8 : word) = Some Wx_87f58.
Proof. vm_refl. Qed.
Lemma Dx_87f58 : decode_any Wx_87f58 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87f5c : bv 32 := 0x01010113.
Lemma Fx_87f5c : fetch_word Asan.M.loaded_segments (0x87fac : word) = Some Wx_87f5c.
Proof. vm_refl. Qed.
Lemma Dx_87f5c : decode_any Wx_87f5c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87f60 : bv 32 := 0x00008067.
Lemma Fx_87f60 : fetch_word Asan.M.loaded_segments (0x87fb0 : word) = Some Wx_87f60.
Proof. vm_refl. Qed.
Lemma Dx_87f60 : decode_any Wx_87f60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae66c : bv 32 := 0x000a5517.
Lemma Fx_ae66c : fetch_word Asan.M.loaded_segments (0xae6bc : word) = Some Wx_ae66c.
Proof. vm_refl. Qed.
Lemma Dx_ae66c : decode_any Wx_ae66c = Some (Auipc 10 165, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae670 : bv 32 := 0x6dc53503.
Lemma Fx_ae670 : fetch_word Asan.M.loaded_segments (0xae6c0 : word) = Some Wx_ae670.
Proof. vm_refl. Qed.
Lemma Dx_ae670 : decode_any Wx_ae670 = Some (Load SZ8 true 10 10 1756, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae674 : bv 32 := 0x00450533.
Lemma Fx_ae674 : fetch_word Asan.M.loaded_segments (0xae6c4 : word) = Some Wx_ae674.
Proof. vm_refl. Qed.
Lemma Dx_ae674 : decode_any Wx_ae674 = Some (Op ALU_ADD 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae678 : bv 32 := 0x00052583.
Lemma Fx_ae678 : fetch_word Asan.M.loaded_segments (0xae6c8 : word) = Some Wx_ae678.
Proof. vm_refl. Qed.
Lemma Dx_ae678 : decode_any Wx_ae678 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae67c : bv 32 := 0x00158593.
Lemma Fx_ae67c : fetch_word Asan.M.loaded_segments (0xae6cc : word) = Some Wx_ae67c.
Proof. vm_refl. Qed.
Lemma Dx_ae67c : decode_any Wx_ae67c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae680 : bv 32 := 0x00b52023.
Lemma Fx_ae680 : fetch_word Asan.M.loaded_segments (0xae6d0 : word) = Some Wx_ae680.
Proof. vm_refl. Qed.
Lemma Dx_ae680 : decode_any Wx_ae680 = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae684 : bv 32 := 0x00008067.
Lemma Fx_ae684 : fetch_word Asan.M.loaded_segments (0xae6d4 : word) = Some Wx_ae684.
Proof. vm_refl. Qed.
Lemma Dx_ae684 : decode_any Wx_ae684 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae688 : bv 32 := 0xff010113.
Lemma Fx_ae688 : fetch_word Asan.M.loaded_segments (0xae6d8 : word) = Some Wx_ae688.
Proof. vm_refl. Qed.
Lemma Dx_ae688 : decode_any Wx_ae688 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae68c : bv 32 := 0x00113423.
Lemma Fx_ae68c : fetch_word Asan.M.loaded_segments (0xae6dc : word) = Some Wx_ae68c.
Proof. vm_refl. Qed.
Lemma Dx_ae68c : decode_any Wx_ae68c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae690 : bv 32 := 0x00813023.
Lemma Fx_ae690 : fetch_word Asan.M.loaded_segments (0xae6e0 : word) = Some Wx_ae690.
Proof. vm_refl. Qed.
Lemma Dx_ae690 : decode_any Wx_ae690 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae694 : bv 32 := 0x000a5517.
Lemma Fx_ae694 : fetch_word Asan.M.loaded_segments (0xae6e4 : word) = Some Wx_ae694.
Proof. vm_refl. Qed.
Lemma Dx_ae694 : decode_any Wx_ae694 = Some (Auipc 10 165, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae698 : bv 32 := 0x6b453403.
Lemma Fx_ae698 : fetch_word Asan.M.loaded_segments (0xae6e8 : word) = Some Wx_ae698.
Proof. vm_refl. Qed.
Lemma Dx_ae698 : decode_any Wx_ae698 = Some (Load SZ8 true 8 10 1716, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae69c : bv 32 := 0x00440433.
Lemma Fx_ae69c : fetch_word Asan.M.loaded_segments (0xae6ec : word) = Some Wx_ae69c.
Proof. vm_refl. Qed.
Lemma Dx_ae69c : decode_any Wx_ae69c = Some (Op ALU_ADD 8 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae6a0 : bv 32 := 0x00042503.
Lemma Fx_ae6a0 : fetch_word Asan.M.loaded_segments (0xae6f0 : word) = Some Wx_ae6a0.
Proof. vm_refl. Qed.
Lemma Dx_ae6a0 : decode_any Wx_ae6a0 = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae6a4 : bv 32 := 0x00050e63.
Lemma Fx_ae6a4 : fetch_word Asan.M.loaded_segments (0xae6f4 : word) = Some Wx_ae6a4.
Proof. vm_refl. Qed.
Lemma Dx_ae6a4 : decode_any Wx_ae6a4 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae6a8 : bv 32 := 0xfff50513.
Lemma Fx_ae6a8 : fetch_word Asan.M.loaded_segments (0xae6f8 : word) = Some Wx_ae6a8.
Proof. vm_refl. Qed.
Lemma Dx_ae6a8 : decode_any Wx_ae6a8 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae6ac : bv 32 := 0x00a42023.
Lemma Fx_ae6ac : fetch_word Asan.M.loaded_segments (0xae6fc : word) = Some Wx_ae6ac.
Proof. vm_refl. Qed.
Lemma Dx_ae6ac : decode_any Wx_ae6ac = Some (Store SZ4 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae6b0 : bv 32 := 0x00813083.
Lemma Fx_ae6b0 : fetch_word Asan.M.loaded_segments (0xae700 : word) = Some Wx_ae6b0.
Proof. vm_refl. Qed.
Lemma Dx_ae6b0 : decode_any Wx_ae6b0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae6b4 : bv 32 := 0x00013403.
Lemma Fx_ae6b4 : fetch_word Asan.M.loaded_segments (0xae704 : word) = Some Wx_ae6b4.
Proof. vm_refl. Qed.
Lemma Dx_ae6b4 : decode_any Wx_ae6b4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae6b8 : bv 32 := 0x01010113.
Lemma Fx_ae6b8 : fetch_word Asan.M.loaded_segments (0xae708 : word) = Some Wx_ae6b8.
Proof. vm_refl. Qed.
Lemma Dx_ae6b8 : decode_any Wx_ae6b8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_ae6bc : bv 32 := 0x00008067.
Lemma Fx_ae6bc : fetch_word Asan.M.loaded_segments (0xae70c : word) = Some Wx_ae6bc.
Proof. vm_refl. Qed.
Lemma Dx_ae6bc : decode_any Wx_ae6bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

