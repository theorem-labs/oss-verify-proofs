(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_7bdf4 : bv 32 := 0xfc010113.
Lemma F_7bdf4 : fetch_word Asan.M.loaded_segments (0x7be44 : word) = Some W_7bdf4.
Proof. vm_refl. Qed.
Lemma D_7bdf4 : decode_any W_7bdf4 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdf8 : bv 32 := 0x02113c23.
Lemma F_7bdf8 : fetch_word Asan.M.loaded_segments (0x7be48 : word) = Some W_7bdf8.
Proof. vm_refl. Qed.
Lemma D_7bdf8 : decode_any W_7bdf8 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdfc : bv 32 := 0x02813823.
Lemma F_7bdfc : fetch_word Asan.M.loaded_segments (0x7be4c : word) = Some W_7bdfc.
Proof. vm_refl. Qed.
Lemma D_7bdfc : decode_any W_7bdfc = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be00 : bv 32 := 0x02913423.
Lemma F_7be00 : fetch_word Asan.M.loaded_segments (0x7be50 : word) = Some W_7be00.
Proof. vm_refl. Qed.
Lemma D_7be00 : decode_any W_7be00 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be04 : bv 32 := 0x03213023.
Lemma F_7be04 : fetch_word Asan.M.loaded_segments (0x7be54 : word) = Some W_7be04.
Proof. vm_refl. Qed.
Lemma D_7be04 : decode_any W_7be04 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be08 : bv 32 := 0x01313c23.
Lemma F_7be08 : fetch_word Asan.M.loaded_segments (0x7be58 : word) = Some W_7be08.
Proof. vm_refl. Qed.
Lemma D_7be08 : decode_any W_7be08 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be0c : bv 32 := 0x01413823.
Lemma F_7be0c : fetch_word Asan.M.loaded_segments (0x7be5c : word) = Some W_7be0c.
Proof. vm_refl. Qed.
Lemma D_7be0c : decode_any W_7be0c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be10 : bv 32 := 0x01513423.
Lemma F_7be10 : fetch_word Asan.M.loaded_segments (0x7be60 : word) = Some W_7be10.
Proof. vm_refl. Qed.
Lemma D_7be10 : decode_any W_7be10 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be14 : bv 32 := 0x14058c63.
Lemma F_7be14 : fetch_word Asan.M.loaded_segments (0x7be64 : word) = Some W_7be14.
Proof. vm_refl. Qed.
Lemma D_7be14 : decode_any W_7be14 = Some (Branch BC_EQ 11 0 344, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be18 : bv 32 := 0x00058493.
Lemma F_7be18 : fetch_word Asan.M.loaded_segments (0x7be68 : word) = Some W_7be18.
Proof. vm_refl. Qed.
Lemma D_7be18 : decode_any W_7be18 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be1c : bv 32 := 0x00050413.
Lemma F_7be1c : fetch_word Asan.M.loaded_segments (0x7be6c : word) = Some W_7be1c.
Proof. vm_refl. Qed.
Lemma D_7be1c : decode_any W_7be1c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be20 : bv 32 := 0x000bd517.
Lemma F_7be20 : fetch_word Asan.M.loaded_segments (0x7be70 : word) = Some W_7be20.
Proof. vm_refl. Qed.
Lemma D_7be20 : decode_any W_7be20 = Some (Auipc 10 189, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be24 : bv 32 := 0x34853a83.
Lemma F_7be24 : fetch_word Asan.M.loaded_segments (0x7be74 : word) = Some W_7be24.
Proof. vm_refl. Qed.
Lemma D_7be24 : decode_any W_7be24 = Some (Load SZ8 true 21 10 840, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be28 : bv 32 := 0x000ab583.
Lemma F_7be28 : fetch_word Asan.M.loaded_segments (0x7be78 : word) = Some W_7be28.
Proof. vm_refl. Qed.
Lemma D_7be28 : decode_any W_7be28 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be2c : bv 32 := 0xfff58513.
Lemma F_7be2c : fetch_word Asan.M.loaded_segments (0x7be7c : word) = Some W_7be2c.
Proof. vm_refl. Qed.
Lemma D_7be2c : decode_any W_7be2c = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be30 : bv 32 := 0x00a5b633.
Lemma F_7be30 : fetch_word Asan.M.loaded_segments (0x7be80 : word) = Some W_7be30.
Proof. vm_refl. Qed.
Lemma D_7be30 : decode_any W_7be30 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be34 : bv 32 := 0xfff60613.
Lemma F_7be34 : fetch_word Asan.M.loaded_segments (0x7be84 : word) = Some W_7be34.
Proof. vm_refl. Qed.
Lemma D_7be34 : decode_any W_7be34 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be38 : bv 32 := 0x00a67633.
Lemma F_7be38 : fetch_word Asan.M.loaded_segments (0x7be88 : word) = Some W_7be38.
Proof. vm_refl. Qed.
Lemma D_7be38 : decode_any W_7be38 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be3c : bv 32 := 0x04867263.
Lemma F_7be3c : fetch_word Asan.M.loaded_segments (0x7be8c : word) = Some W_7be3c.
Proof. vm_refl. Qed.
Lemma D_7be3c : decode_any W_7be3c = Some (Branch BC_GEU 12 8 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be40 : bv 32 := 0x000bd697.
Lemma F_7be40 : fetch_word Asan.M.loaded_segments (0x7be90 : word) = Some W_7be40.
Proof. vm_refl. Qed.
Lemma D_7be40 : decode_any W_7be40 = Some (Auipc 13 189, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be44 : bv 32 := 0x3306b683.
Lemma F_7be44 : fetch_word Asan.M.loaded_segments (0x7be94 : word) = Some W_7be44.
Proof. vm_refl. Qed.
Lemma D_7be44 : decode_any W_7be44 = Some (Load SZ8 true 13 13 816, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be48 : bv 32 := 0x000bd717.
Lemma F_7be48 : fetch_word Asan.M.loaded_segments (0x7be98 : word) = Some W_7be48.
Proof. vm_refl. Qed.
Lemma D_7be48 : decode_any W_7be48 = Some (Auipc 14 189, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be4c : bv 32 := 0x33073703.
Lemma F_7be4c : fetch_word Asan.M.loaded_segments (0x7be9c : word) = Some W_7be4c.
Proof. vm_refl. Qed.
Lemma D_7be4c : decode_any W_7be4c = Some (Load SZ8 true 14 14 816, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be50 : bv 32 := 0x0006b803.
Lemma F_7be50 : fetch_word Asan.M.loaded_segments (0x7bea0 : word) = Some W_7be50.
Proof. vm_refl. Qed.
Lemma D_7be50 : decode_any W_7be50 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be54 : bv 32 := 0x00073683.
Lemma F_7be54 : fetch_word Asan.M.loaded_segments (0x7bea4 : word) = Some W_7be54.
Proof. vm_refl. Qed.
Lemma D_7be54 : decode_any W_7be54 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be58 : bv 32 := 0xfff80793.
Lemma F_7be58 : fetch_word Asan.M.loaded_segments (0x7bea8 : word) = Some W_7be58.
Proof. vm_refl. Qed.
Lemma D_7be58 : decode_any W_7be58 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be5c : bv 32 := 0x0087f463.
Lemma F_7be5c : fetch_word Asan.M.loaded_segments (0x7beac : word) = Some W_7be5c.
Proof. vm_refl. Qed.
Lemma D_7be5c : decode_any W_7be5c = Some (Branch BC_GEU 15 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be64 : bv 32 := 0x000bd717.
Lemma F_7be64 : fetch_word Asan.M.loaded_segments (0x7beb4 : word) = Some W_7be64.
Proof. vm_refl. Qed.
Lemma D_7be64 : decode_any W_7be64 = Some (Auipc 14 189, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be68 : bv 32 := 0x31c73703.
Lemma F_7be68 : fetch_word Asan.M.loaded_segments (0x7beb8 : word) = Some W_7be68.
Proof. vm_refl. Qed.
Lemma D_7be68 : decode_any W_7be68 = Some (Load SZ8 true 14 14 796, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be6c : bv 32 := 0x00073283.
Lemma F_7be6c : fetch_word Asan.M.loaded_segments (0x7bebc : word) = Some W_7be6c.
Proof. vm_refl. Qed.
Lemma D_7be6c : decode_any W_7be6c = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be70 : bv 32 := 0x0032d713.
Lemma F_7be70 : fetch_word Asan.M.loaded_segments (0x7bec0 : word) = Some W_7be70.
Proof. vm_refl. Qed.
Lemma D_7be70 : decode_any W_7be70 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be74 : bv 32 := 0x00b708b3.
Lemma F_7be74 : fetch_word Asan.M.loaded_segments (0x7bec4 : word) = Some W_7be74.
Proof. vm_refl. Qed.
Lemma D_7be74 : decode_any W_7be74 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be78 : bv 32 := 0x1282e063.
Lemma F_7be78 : fetch_word Asan.M.loaded_segments (0x7bec8 : word) = Some W_7be78.
Proof. vm_refl. Qed.
Lemma D_7be78 : decode_any W_7be78 = Some (Branch BC_LTU 5 8 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be7c : bv 32 := 0x1088fe63.
Lemma F_7be7c : fetch_word Asan.M.loaded_segments (0x7becc : word) = Some W_7be7c.
Proof. vm_refl. Qed.
Lemma D_7be7c : decode_any W_7be7c = Some (Branch BC_GEU 17 8 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be80 : bv 32 := 0x00848933.
Lemma F_7be80 : fetch_word Asan.M.loaded_segments (0x7bed0 : word) = Some W_7be80.
Proof. vm_refl. Qed.
Lemma D_7be80 : decode_any W_7be80 = Some (Op ALU_ADD 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be84 : bv 32 := 0x05267263.
Lemma F_7be84 : fetch_word Asan.M.loaded_segments (0x7bed4 : word) = Some W_7be84.
Proof. vm_refl. Qed.
Lemma D_7be84 : decode_any W_7be84 = Some (Branch BC_GEU 12 18 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be88 : bv 32 := 0x000bd617.
Lemma F_7be88 : fetch_word Asan.M.loaded_segments (0x7bed8 : word) = Some W_7be88.
Proof. vm_refl. Qed.
Lemma D_7be88 : decode_any W_7be88 = Some (Auipc 12 189, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be8c : bv 32 := 0x2e863603.
Lemma F_7be8c : fetch_word Asan.M.loaded_segments (0x7bedc : word) = Some W_7be8c.
Proof. vm_refl. Qed.
Lemma D_7be8c : decode_any W_7be8c = Some (Load SZ8 true 12 12 744, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be90 : bv 32 := 0x000bd697.
Lemma F_7be90 : fetch_word Asan.M.loaded_segments (0x7bee0 : word) = Some W_7be90.
Proof. vm_refl. Qed.
Lemma D_7be90 : decode_any W_7be90 = Some (Auipc 13 189, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be94 : bv 32 := 0x2e86b683.
Lemma F_7be94 : fetch_word Asan.M.loaded_segments (0x7bee4 : word) = Some W_7be94.
Proof. vm_refl. Qed.
Lemma D_7be94 : decode_any W_7be94 = Some (Load SZ8 true 13 13 744, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be98 : bv 32 := 0x00063783.
Lemma F_7be98 : fetch_word Asan.M.loaded_segments (0x7bee8 : word) = Some W_7be98.
Proof. vm_refl. Qed.
Lemma D_7be98 : decode_any W_7be98 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be9c : bv 32 := 0x0006b603.
Lemma F_7be9c : fetch_word Asan.M.loaded_segments (0x7beec : word) = Some W_7be9c.
Proof. vm_refl. Qed.
Lemma D_7be9c : decode_any W_7be9c = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bea0 : bv 32 := 0xfff78713.
Lemma F_7bea0 : fetch_word Asan.M.loaded_segments (0x7bef0 : word) = Some W_7bea0.
Proof. vm_refl. Qed.
Lemma D_7bea0 : decode_any W_7bea0 = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bea4 : bv 32 := 0x01277463.
Lemma F_7bea4 : fetch_word Asan.M.loaded_segments (0x7bef4 : word) = Some W_7bea4.
Proof. vm_refl. Qed.
Lemma D_7bea4 : decode_any W_7bea4 = Some (Branch BC_GEU 14 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7beac : bv 32 := 0x000bd697.
Lemma F_7beac : fetch_word Asan.M.loaded_segments (0x7befc : word) = Some W_7beac.
Proof. vm_refl. Qed.
Lemma D_7beac : decode_any W_7beac = Some (Auipc 13 189, 4%Z).
Proof. vm_refl. Qed.

Definition W_7beb0 : bv 32 := 0x2d46b683.
Lemma F_7beb0 : fetch_word Asan.M.loaded_segments (0x7bf00 : word) = Some W_7beb0.
Proof. vm_refl. Qed.
Lemma D_7beb0 : decode_any W_7beb0 = Some (Load SZ8 true 13 13 724, 4%Z).
Proof. vm_refl. Qed.

Definition W_7beb4 : bv 32 := 0x0006b883.
Lemma F_7beb4 : fetch_word Asan.M.loaded_segments (0x7bf04 : word) = Some W_7beb4.
Proof. vm_refl. Qed.
Lemma D_7beb4 : decode_any W_7beb4 = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7beb8 : bv 32 := 0x0038d693.
Lemma F_7beb8 : fetch_word Asan.M.loaded_segments (0x7bf08 : word) = Some W_7beb8.
Proof. vm_refl. Qed.
Lemma D_7beb8 : decode_any W_7beb8 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bebc : bv 32 := 0x00b68833.
Lemma F_7bebc : fetch_word Asan.M.loaded_segments (0x7bf0c : word) = Some W_7bebc.
Proof. vm_refl. Qed.
Lemma D_7bebc : decode_any W_7bebc = Some (Op ALU_ADD 16 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bec0 : bv 32 := 0x1328e463.
Lemma F_7bec0 : fetch_word Asan.M.loaded_segments (0x7bf10 : word) = Some W_7bec0.
Proof. vm_refl. Qed.
Lemma D_7bec0 : decode_any W_7bec0 = Some (Branch BC_LTU 17 18 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bec4 : bv 32 := 0x13287263.
Lemma F_7bec4 : fetch_word Asan.M.loaded_segments (0x7bf14 : word) = Some W_7bec4.
Proof. vm_refl. Qed.
Lemma D_7bec4 : decode_any W_7bec4 = Some (Branch BC_GEU 16 18 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bec8 : bv 32 := 0x23247863.
Lemma F_7bec8 : fetch_word Asan.M.loaded_segments (0x7bf18 : word) = Some W_7bec8.
Proof. vm_refl. Qed.
Lemma D_7bec8 : decode_any W_7bec8 = Some (Branch BC_GEU 8 18 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_7becc : bv 32 := 0x00740513.
Lemma F_7becc : fetch_word Asan.M.loaded_segments (0x7bf1c : word) = Some W_7becc.
Proof. vm_refl. Qed.
Lemma D_7becc : decode_any W_7becc = Some (OpImm ALU_ADD 10 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bed0 : bv 32 := 0xff857513.
Lemma F_7bed0 : fetch_word Asan.M.loaded_segments (0x7bf20 : word) = Some W_7bed0.
Proof. vm_refl. Qed.
Lemma D_7bed0 : decode_any W_7bed0 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bed4 : bv 32 := 0xff897a13.
Lemma F_7bed4 : fetch_word Asan.M.loaded_segments (0x7bf24 : word) = Some W_7bed4.
Proof. vm_refl. Qed.
Lemma D_7bed4 : decode_any W_7bed4 = Some (OpImm ALU_AND 20 18 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bed8 : bv 32 := 0xa91ff0ef.
Lemma F_7bed8 : fetch_word Asan.M.loaded_segments (0x7bf28 : word) = Some W_7bed8.
Proof. vm_refl. Qed.
Lemma D_7bed8 : decode_any W_7bed8 = Some (Jal 1 2095760, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bedc : bv 32 := 0x00050993.
Lemma F_7bedc : fetch_word Asan.M.loaded_segments (0x7bf2c : word) = Some W_7bedc.
Proof. vm_refl. Qed.
Lemma D_7bedc : decode_any W_7bedc = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bee0 : bv 32 := 0x000a0513.
Lemma F_7bee0 : fetch_word Asan.M.loaded_segments (0x7bf30 : word) = Some W_7bee0.
Proof. vm_refl. Qed.
Lemma D_7bee0 : decode_any W_7bee0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bee4 : bv 32 := 0xa85ff0ef.
Lemma F_7bee4 : fetch_word Asan.M.loaded_segments (0x7bf34 : word) = Some W_7bee4.
Proof. vm_refl. Qed.
Lemma D_7bee4 : decode_any W_7bee4 = Some (Jal 1 2095748, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bee8 : bv 32 := 0x000ab583.
Lemma F_7bee8 : fetch_word Asan.M.loaded_segments (0x7bf38 : word) = Some W_7bee8.
Proof. vm_refl. Qed.
Lemma D_7bee8 : decode_any W_7bee8 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7beec : bv 32 := 0x00345613.
Lemma F_7beec : fetch_word Asan.M.loaded_segments (0x7bf3c : word) = Some W_7beec.
Proof. vm_refl. Qed.
Lemma D_7beec : decode_any W_7beec = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bef0 : bv 32 := 0x00c58633.
Lemma F_7bef0 : fetch_word Asan.M.loaded_segments (0x7bf40 : word) = Some W_7bef0.
Proof. vm_refl. Qed.
Lemma D_7bef0 : decode_any W_7bef0 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bef4 : bv 32 := 0x00060603.
Lemma F_7bef4 : fetch_word Asan.M.loaded_segments (0x7bf44 : word) = Some W_7bef4.
Proof. vm_refl. Qed.
Lemma D_7bef4 : decode_any W_7bef4 = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bef8 : bv 32 := 0x00060663.
Lemma F_7bef8 : fetch_word Asan.M.loaded_segments (0x7bf48 : word) = Some W_7bef8.
Proof. vm_refl. Qed.
Lemma D_7bef8 : decode_any W_7bef8 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7befc : bv 32 := 0x00747693.
Lemma F_7befc : fetch_word Asan.M.loaded_segments (0x7bf4c : word) = Some W_7befc.
Proof. vm_refl. Qed.
Lemma D_7befc : decode_any W_7befc = Some (OpImm ALU_AND 13 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf00 : bv 32 := 0x02c6d063.
Lemma F_7bf00 : fetch_word Asan.M.loaded_segments (0x7bf50 : word) = Some W_7bf00.
Proof. vm_refl. Qed.
Lemma D_7bf00 : decode_any W_7bf00 = Some (Branch BC_GE 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf04 : bv 32 := 0xfff90913.
Lemma F_7bf04 : fetch_word Asan.M.loaded_segments (0x7bf54 : word) = Some W_7bf04.
Proof. vm_refl. Qed.
Lemma D_7bf04 : decode_any W_7bf04 = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf08 : bv 32 := 0x00395613.
Lemma F_7bf08 : fetch_word Asan.M.loaded_segments (0x7bf58 : word) = Some W_7bf08.
Proof. vm_refl. Qed.
Lemma D_7bf08 : decode_any W_7bf08 = Some (ShiftImm ALU_SRL 12 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf0c : bv 32 := 0x00c585b3.
Lemma F_7bf0c : fetch_word Asan.M.loaded_segments (0x7bf5c : word) = Some W_7bf0c.
Proof. vm_refl. Qed.
Lemma D_7bf0c : decode_any W_7bf0c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf10 : bv 32 := 0x00058583.
Lemma F_7bf10 : fetch_word Asan.M.loaded_segments (0x7bf60 : word) = Some W_7bf10.
Proof. vm_refl. Qed.
Lemma D_7bf10 : decode_any W_7bf10 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf14 : bv 32 := 0x04058263.
Lemma F_7bf14 : fetch_word Asan.M.loaded_segments (0x7bf64 : word) = Some W_7bf14.
Proof. vm_refl. Qed.
Lemma D_7bf14 : decode_any W_7bf14 = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf18 : bv 32 := 0x00797613.
Lemma F_7bf18 : fetch_word Asan.M.loaded_segments (0x7bf68 : word) = Some W_7bf18.
Proof. vm_refl. Qed.
Lemma D_7bf18 : decode_any W_7bf18 = Some (OpImm ALU_AND 12 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf1c : bv 32 := 0x02b64e63.
Lemma F_7bf1c : fetch_word Asan.M.loaded_segments (0x7bf6c : word) = Some W_7bf1c.
Proof. vm_refl. Qed.
Lemma D_7bf1c : decode_any W_7bf1c = Some (Branch BC_LT 12 11 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf58 : bv 32 := 0x00a9fa63.
Lemma F_7bf58 : fetch_word Asan.M.loaded_segments (0x7bfa8 : word) = Some W_7bf58.
Proof. vm_refl. Qed.
Lemma D_7bf58 : decode_any W_7bf58 = Some (Branch BC_GEU 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf5c : bv 32 := 0x413505b3.
Lemma F_7bf5c : fetch_word Asan.M.loaded_segments (0x7bfac : word) = Some W_7bf5c.
Proof. vm_refl. Qed.
Lemma D_7bf5c : decode_any W_7bf5c = Some (Op ALU_SUB 11 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf60 : bv 32 := 0x00098513.
Lemma F_7bf60 : fetch_word Asan.M.loaded_segments (0x7bfb0 : word) = Some W_7bf60.
Proof. vm_refl. Qed.
Lemma D_7bf60 : decode_any W_7bf60 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf64 : bv 32 := 0x37c100ef.
Lemma F_7bf64 : fetch_word Asan.M.loaded_segments (0x7bfb4 : word) = Some W_7bf64.
Proof. vm_refl. Qed.
Lemma D_7bf64 : decode_any W_7bf64 = Some (Jal 1 66428, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf68 : bv 32 := 0xfa050ce3.
Lemma F_7bf68 : fetch_word Asan.M.loaded_segments (0x7bfb8 : word) = Some W_7bf68.
Proof. vm_refl. Qed.
Lemma D_7bf68 : decode_any W_7bf68 = Some (Branch BC_EQ 10 0 8120, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf6c : bv 32 := 0x00000413.
Lemma F_7bf6c : fetch_word Asan.M.loaded_segments (0x7bfbc : word) = Some W_7bf6c.
Proof. vm_refl. Qed.
Lemma D_7bf6c : decode_any W_7bf6c = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf70 : bv 32 := 0x00040513.
Lemma F_7bf70 : fetch_word Asan.M.loaded_segments (0x7bfc0 : word) = Some W_7bf70.
Proof. vm_refl. Qed.
Lemma D_7bf70 : decode_any W_7bf70 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf74 : bv 32 := 0x03813083.
Lemma F_7bf74 : fetch_word Asan.M.loaded_segments (0x7bfc4 : word) = Some W_7bf74.
Proof. vm_refl. Qed.
Lemma D_7bf74 : decode_any W_7bf74 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf78 : bv 32 := 0x03013403.
Lemma F_7bf78 : fetch_word Asan.M.loaded_segments (0x7bfc8 : word) = Some W_7bf78.
Proof. vm_refl. Qed.
Lemma D_7bf78 : decode_any W_7bf78 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf7c : bv 32 := 0x02813483.
Lemma F_7bf7c : fetch_word Asan.M.loaded_segments (0x7bfcc : word) = Some W_7bf7c.
Proof. vm_refl. Qed.
Lemma D_7bf7c : decode_any W_7bf7c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf80 : bv 32 := 0x02013903.
Lemma F_7bf80 : fetch_word Asan.M.loaded_segments (0x7bfd0 : word) = Some W_7bf80.
Proof. vm_refl. Qed.
Lemma D_7bf80 : decode_any W_7bf80 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf84 : bv 32 := 0x01813983.
Lemma F_7bf84 : fetch_word Asan.M.loaded_segments (0x7bfd4 : word) = Some W_7bf84.
Proof. vm_refl. Qed.
Lemma D_7bf84 : decode_any W_7bf84 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf88 : bv 32 := 0x01013a03.
Lemma F_7bf88 : fetch_word Asan.M.loaded_segments (0x7bfd8 : word) = Some W_7bf88.
Proof. vm_refl. Qed.
Lemma D_7bf88 : decode_any W_7bf88 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf8c : bv 32 := 0x00813a83.
Lemma F_7bf8c : fetch_word Asan.M.loaded_segments (0x7bfdc : word) = Some W_7bf8c.
Proof. vm_refl. Qed.
Lemma D_7bf8c : decode_any W_7bf8c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf90 : bv 32 := 0x04010113.
Lemma F_7bf90 : fetch_word Asan.M.loaded_segments (0x7bfe0 : word) = Some W_7bf90.
Proof. vm_refl. Qed.
Lemma D_7bf90 : decode_any W_7bf90 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf94 : bv 32 := 0x00008067.
Lemma F_7bf94 : fetch_word Asan.M.loaded_segments (0x7bfe4 : word) = Some W_7bf94.
Proof. vm_refl. Qed.
Lemma D_7bf94 : decode_any W_7bf94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
