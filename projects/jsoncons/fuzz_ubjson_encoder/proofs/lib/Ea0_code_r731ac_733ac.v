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

Definition W_8de00 : bv 32 := 0xfd010113.
Lemma F_8de00 : fetch_word Asan.M.loaded_segments (0x8de50 : word) = Some W_8de00.
Proof. vm_refl. Qed.
Lemma D_8de00 : decode_any W_8de00 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de04 : bv 32 := 0x02113423.
Lemma F_8de04 : fetch_word Asan.M.loaded_segments (0x8de54 : word) = Some W_8de04.
Proof. vm_refl. Qed.
Lemma D_8de04 : decode_any W_8de04 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de08 : bv 32 := 0x02813023.
Lemma F_8de08 : fetch_word Asan.M.loaded_segments (0x8de58 : word) = Some W_8de08.
Proof. vm_refl. Qed.
Lemma D_8de08 : decode_any W_8de08 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de0c : bv 32 := 0x00913c23.
Lemma F_8de0c : fetch_word Asan.M.loaded_segments (0x8de5c : word) = Some W_8de0c.
Proof. vm_refl. Qed.
Lemma D_8de0c : decode_any W_8de0c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de10 : bv 32 := 0x01213823.
Lemma F_8de10 : fetch_word Asan.M.loaded_segments (0x8de60 : word) = Some W_8de10.
Proof. vm_refl. Qed.
Lemma D_8de10 : decode_any W_8de10 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de14 : bv 32 := 0x02050e63.
Lemma F_8de14 : fetch_word Asan.M.loaded_segments (0x8de64 : word) = Some W_8de14.
Proof. vm_refl. Qed.
Lemma D_8de14 : decode_any W_8de14 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de18 : bv 32 := 0x00058413.
Lemma F_8de18 : fetch_word Asan.M.loaded_segments (0x8de68 : word) = Some W_8de18.
Proof. vm_refl. Qed.
Lemma D_8de18 : decode_any W_8de18 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de1c : bv 32 := 0x02058a63.
Lemma F_8de1c : fetch_word Asan.M.loaded_segments (0x8de6c : word) = Some W_8de1c.
Proof. vm_refl. Qed.
Lemma D_8de1c : decode_any W_8de1c = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de20 : bv 32 := 0x00060493.
Lemma F_8de20 : fetch_word Asan.M.loaded_segments (0x8de70 : word) = Some W_8de20.
Proof. vm_refl. Qed.
Lemma D_8de20 : decode_any W_8de20 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de24 : bv 32 := 0x00050913.
Lemma F_8de24 : fetch_word Asan.M.loaded_segments (0x8de74 : word) = Some W_8de24.
Proof. vm_refl. Qed.
Lemma D_8de24 : decode_any W_8de24 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de28 : bv 32 := 0x00040593.
Lemma F_8de28 : fetch_word Asan.M.loaded_segments (0x8de78 : word) = Some W_8de28.
Proof. vm_refl. Qed.
Lemma D_8de28 : decode_any W_8de28 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de2c : bv 32 := 0xf90fe0ef.
Lemma F_8de2c : fetch_word Asan.M.loaded_segments (0x8de7c : word) = Some W_8de2c.
Proof. vm_refl. Qed.
Lemma D_8de2c : decode_any W_8de2c = Some (Jal 1 2090896, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de30 : bv 32 := 0xaaaab5b7.
Lemma F_8de30 : fetch_word Asan.M.loaded_segments (0x8de80 : word) = Some W_8de30.
Proof. vm_refl. Qed.
Lemma D_8de30 : decode_any W_8de30 = Some (Lui 11 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de34 : bv 32 := 0xaaa58593.
Lemma F_8de34 : fetch_word Asan.M.loaded_segments (0x8de84 : word) = Some W_8de34.
Proof. vm_refl. Qed.
Lemma D_8de34 : decode_any W_8de34 = Some (OpImm ALU_ADD 11 11 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de38 : bv 32 := 0x00b12623.
Lemma F_8de38 : fetch_word Asan.M.loaded_segments (0x8de88 : word) = Some W_8de38.
Proof. vm_refl. Qed.
Lemma D_8de38 : decode_any W_8de38 = Some (Store SZ4 2 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de3c : bv 32 := 0x00c10593.
Lemma F_8de3c : fetch_word Asan.M.loaded_segments (0x8de8c : word) = Some W_8de3c.
Proof. vm_refl. Qed.
Lemma D_8de3c : decode_any W_8de3c = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de40 : bv 32 := 0xf50fe0ef.
Lemma F_8de40 : fetch_word Asan.M.loaded_segments (0x8de90 : word) = Some W_8de40.
Proof. vm_refl. Qed.
Lemma D_8de40 : decode_any W_8de40 = Some (Jal 1 2090832, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de44 : bv 32 := 0x02051263.
Lemma F_8de44 : fetch_word Asan.M.loaded_segments (0x8de94 : word) = Some W_8de44.
Proof. vm_refl. Qed.
Lemma D_8de44 : decode_any W_8de44 = Some (Branch BC_NE 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de48 : bv 32 := 0x00040513.
Lemma F_8de48 : fetch_word Asan.M.loaded_segments (0x8de98 : word) = Some W_8de48.
Proof. vm_refl. Qed.
Lemma D_8de48 : decode_any W_8de48 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de4c : bv 32 := 0xe70fa0ef.
Lemma F_8de4c : fetch_word Asan.M.loaded_segments (0x8de9c : word) = Some W_8de4c.
Proof. vm_refl. Qed.
Lemma D_8de4c : decode_any W_8de4c = Some (Jal 1 2074224, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de50 : bv 32 := 0x02813083.
Lemma F_8de50 : fetch_word Asan.M.loaded_segments (0x8dea0 : word) = Some W_8de50.
Proof. vm_refl. Qed.
Lemma D_8de50 : decode_any W_8de50 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de54 : bv 32 := 0x02013403.
Lemma F_8de54 : fetch_word Asan.M.loaded_segments (0x8dea4 : word) = Some W_8de54.
Proof. vm_refl. Qed.
Lemma D_8de54 : decode_any W_8de54 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de58 : bv 32 := 0x01813483.
Lemma F_8de58 : fetch_word Asan.M.loaded_segments (0x8dea8 : word) = Some W_8de58.
Proof. vm_refl. Qed.
Lemma D_8de58 : decode_any W_8de58 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de5c : bv 32 := 0x01013903.
Lemma F_8de5c : fetch_word Asan.M.loaded_segments (0x8deac : word) = Some W_8de5c.
Proof. vm_refl. Qed.
Lemma D_8de5c : decode_any W_8de5c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de60 : bv 32 := 0x03010113.
Lemma F_8de60 : fetch_word Asan.M.loaded_segments (0x8deb0 : word) = Some W_8de60.
Proof. vm_refl. Qed.
Lemma D_8de60 : decode_any W_8de60 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de64 : bv 32 := 0x00008067.
Lemma F_8de64 : fetch_word Asan.M.loaded_segments (0x8deb4 : word) = Some W_8de64.
Proof. vm_refl. Qed.
Lemma D_8de64 : decode_any W_8de64 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de7c : bv 32 := 0xfd010113.
Lemma F_8de7c : fetch_word Asan.M.loaded_segments (0x8decc : word) = Some W_8de7c.
Proof. vm_refl. Qed.
Lemma D_8de7c : decode_any W_8de7c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de80 : bv 32 := 0x02113423.
Lemma F_8de80 : fetch_word Asan.M.loaded_segments (0x8ded0 : word) = Some W_8de80.
Proof. vm_refl. Qed.
Lemma D_8de80 : decode_any W_8de80 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de84 : bv 32 := 0x02813023.
Lemma F_8de84 : fetch_word Asan.M.loaded_segments (0x8ded4 : word) = Some W_8de84.
Proof. vm_refl. Qed.
Lemma D_8de84 : decode_any W_8de84 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de88 : bv 32 := 0x00913c23.
Lemma F_8de88 : fetch_word Asan.M.loaded_segments (0x8ded8 : word) = Some W_8de88.
Proof. vm_refl. Qed.
Lemma D_8de88 : decode_any W_8de88 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de8c : bv 32 := 0x01213823.
Lemma F_8de8c : fetch_word Asan.M.loaded_segments (0x8dedc : word) = Some W_8de8c.
Proof. vm_refl. Qed.
Lemma D_8de8c : decode_any W_8de8c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de90 : bv 32 := 0x00058413.
Lemma F_8de90 : fetch_word Asan.M.loaded_segments (0x8dee0 : word) = Some W_8de90.
Proof. vm_refl. Qed.
Lemma D_8de90 : decode_any W_8de90 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de94 : bv 32 := 0x000ab597.
Lemma F_8de94 : fetch_word Asan.M.loaded_segments (0x8dee4 : word) = Some W_8de94.
Proof. vm_refl. Qed.
Lemma D_8de94 : decode_any W_8de94 = Some (Auipc 11 171, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de98 : bv 32 := 0x2b45b903.
Lemma F_8de98 : fetch_word Asan.M.loaded_segments (0x8dee8 : word) = Some W_8de98.
Proof. vm_refl. Qed.
Lemma D_8de98 : decode_any W_8de98 = Some (Load SZ8 true 18 11 692, 4%Z).
Proof. vm_refl. Qed.

Definition W_8de9c : bv 32 := 0x00093583.
Lemma F_8de9c : fetch_word Asan.M.loaded_segments (0x8deec : word) = Some W_8de9c.
Proof. vm_refl. Qed.
Lemma D_8de9c : decode_any W_8de9c = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8dea0 : bv 32 := 0x00050493.
Lemma F_8dea0 : fetch_word Asan.M.loaded_segments (0x8def0 : word) = Some W_8dea0.
Proof. vm_refl. Qed.
Lemma D_8dea0 : decode_any W_8dea0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8dea4 : bv 32 := 0x00059863.
Lemma F_8dea4 : fetch_word Asan.M.loaded_segments (0x8def4 : word) = Some W_8dea4.
Proof. vm_refl. Qed.
Lemma D_8dea4 : decode_any W_8dea4 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8deb4 : bv 32 := 0xfff58513.
Lemma F_8deb4 : fetch_word Asan.M.loaded_segments (0x8df04 : word) = Some W_8deb4.
Proof. vm_refl. Qed.
Lemma D_8deb4 : decode_any W_8deb4 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8deb8 : bv 32 := 0x00a5f533.
Lemma F_8deb8 : fetch_word Asan.M.loaded_segments (0x8df08 : word) = Some W_8deb8.
Proof. vm_refl. Qed.
Lemma D_8deb8 : decode_any W_8deb8 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8debc : bv 32 := 0x08051a63.
Lemma F_8debc : fetch_word Asan.M.loaded_segments (0x8df0c : word) = Some W_8debc.
Proof. vm_refl. Qed.
Lemma D_8debc : decode_any W_8debc = Some (Branch BC_NE 10 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_8dec0 : bv 32 := 0x00b484b3.
Lemma F_8dec0 : fetch_word Asan.M.loaded_segments (0x8df10 : word) = Some W_8dec0.
Proof. vm_refl. Qed.
Lemma D_8dec0 : decode_any W_8dec0 = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8dec4 : bv 32 := 0x40b00533.
Lemma F_8dec4 : fetch_word Asan.M.loaded_segments (0x8df14 : word) = Some W_8dec4.
Proof. vm_refl. Qed.
Lemma D_8dec4 : decode_any W_8dec4 = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8dec8 : bv 32 := 0xfff48493.
Lemma F_8dec8 : fetch_word Asan.M.loaded_segments (0x8df18 : word) = Some W_8dec8.
Proof. vm_refl. Qed.
Lemma D_8dec8 : decode_any W_8dec8 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8decc : bv 32 := 0x00a4f4b3.
Lemma F_8decc : fetch_word Asan.M.loaded_segments (0x8df1c : word) = Some W_8decc.
Proof. vm_refl. Qed.
Lemma D_8decc : decode_any W_8decc = Some (Op ALU_AND 9 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ded0 : bv 32 := 0x02200513.
Lemma F_8ded0 : fetch_word Asan.M.loaded_segments (0x8df20 : word) = Some W_8ded0.
Proof. vm_refl. Qed.
Lemma D_8ded0 : decode_any W_8ded0 = Some (OpImm ALU_ADD 10 0 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ded4 : bv 32 := 0x00a12623.
Lemma F_8ded4 : fetch_word Asan.M.loaded_segments (0x8df24 : word) = Some W_8ded4.
Proof. vm_refl. Qed.
Lemma D_8ded4 : decode_any W_8ded4 = Some (Store SZ4 2 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ded8 : bv 32 := 0x00c10613.
Lemma F_8ded8 : fetch_word Asan.M.loaded_segments (0x8df28 : word) = Some W_8ded8.
Proof. vm_refl. Qed.
Lemma D_8ded8 : decode_any W_8ded8 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8dedc : bv 32 := 0x00040513.
Lemma F_8dedc : fetch_word Asan.M.loaded_segments (0x8df2c : word) = Some W_8dedc.
Proof. vm_refl. Qed.
Lemma D_8dedc : decode_any W_8dedc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8dee0 : bv 32 := 0x00048593.
Lemma F_8dee0 : fetch_word Asan.M.loaded_segments (0x8df30 : word) = Some W_8dee0.
Proof. vm_refl. Qed.
Lemma D_8dee0 : decode_any W_8dee0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8dee4 : bv 32 := 0x279000ef.
Lemma F_8dee4 : fetch_word Asan.M.loaded_segments (0x8df34 : word) = Some W_8dee4.
Proof. vm_refl. Qed.
Lemma D_8dee4 : decode_any W_8dee4 = Some (Jal 1 2680, 4%Z).
Proof. vm_refl. Qed.

Definition W_8dee8 : bv 32 := 0x00c12683.
Lemma F_8dee8 : fetch_word Asan.M.loaded_segments (0x8df38 : word) = Some W_8dee8.
Proof. vm_refl. Qed.
Lemma D_8dee8 : decode_any W_8dee8 = Some (Load SZ4 true 13 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8deec : bv 32 := 0x00050713.
Lemma F_8deec : fetch_word Asan.M.loaded_segments (0x8df3c : word) = Some W_8deec.
Proof. vm_refl. Qed.
Lemma D_8deec : decode_any W_8deec = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8def0 : bv 32 := 0x00300613.
Lemma F_8def0 : fetch_word Asan.M.loaded_segments (0x8df40 : word) = Some W_8def0.
Proof. vm_refl. Qed.
Lemma D_8def0 : decode_any W_8def0 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8def4 : bv 32 := 0x00000513.
Lemma F_8def4 : fetch_word Asan.M.loaded_segments (0x8df44 : word) = Some W_8def4.
Proof. vm_refl. Qed.
Lemma D_8def4 : decode_any W_8def4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8def8 : bv 32 := 0x00048593.
Lemma F_8def8 : fetch_word Asan.M.loaded_segments (0x8df48 : word) = Some W_8def8.
Proof. vm_refl. Qed.
Lemma D_8def8 : decode_any W_8def8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8defc : bv 32 := 0x00000793.
Lemma F_8defc : fetch_word Asan.M.loaded_segments (0x8df4c : word) = Some W_8defc.
Proof. vm_refl. Qed.
Lemma D_8defc : decode_any W_8defc = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df00 : bv 32 := 0xeb0fe0ef.
Lemma F_8df00 : fetch_word Asan.M.loaded_segments (0x8df50 : word) = Some W_8df00.
Proof. vm_refl. Qed.
Lemma D_8df00 : decode_any W_8df00 = Some (Jal 1 2090672, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df04 : bv 32 := 0x00050913.
Lemma F_8df04 : fetch_word Asan.M.loaded_segments (0x8df54 : word) = Some W_8df04.
Proof. vm_refl. Qed.
Lemma D_8df04 : decode_any W_8df04 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df08 : bv 32 := 0x00000593.
Lemma F_8df08 : fetch_word Asan.M.loaded_segments (0x8df58 : word) = Some W_8df08.
Proof. vm_refl. Qed.
Lemma D_8df08 : decode_any W_8df08 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df0c : bv 32 := 0xe84fe0ef.
Lemma F_8df0c : fetch_word Asan.M.loaded_segments (0x8df5c : word) = Some W_8df0c.
Proof. vm_refl. Qed.
Lemma D_8df0c : decode_any W_8df0c = Some (Jal 1 2090628, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df10 : bv 32 := 0xaaaab537.
Lemma F_8df10 : fetch_word Asan.M.loaded_segments (0x8df60 : word) = Some W_8df10.
Proof. vm_refl. Qed.
Lemma D_8df10 : decode_any W_8df10 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df14 : bv 32 := 0xaaa50513.
Lemma F_8df14 : fetch_word Asan.M.loaded_segments (0x8df64 : word) = Some W_8df14.
Proof. vm_refl. Qed.
Lemma D_8df14 : decode_any W_8df14 = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df18 : bv 32 := 0x00a12423.
Lemma F_8df18 : fetch_word Asan.M.loaded_segments (0x8df68 : word) = Some W_8df18.
Proof. vm_refl. Qed.
Lemma D_8df18 : decode_any W_8df18 = Some (Store SZ4 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df1c : bv 32 := 0x00810593.
Lemma F_8df1c : fetch_word Asan.M.loaded_segments (0x8df6c : word) = Some W_8df1c.
Proof. vm_refl. Qed.
Lemma D_8df1c : decode_any W_8df1c = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df20 : bv 32 := 0x00090513.
Lemma F_8df20 : fetch_word Asan.M.loaded_segments (0x8df70 : word) = Some W_8df20.
Proof. vm_refl. Qed.
Lemma D_8df20 : decode_any W_8df20 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df24 : bv 32 := 0xe6cfe0ef.
Lemma F_8df24 : fetch_word Asan.M.loaded_segments (0x8df74 : word) = Some W_8df24.
Proof. vm_refl. Qed.
Lemma D_8df24 : decode_any W_8df24 = Some (Jal 1 2090604, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df28 : bv 32 := 0x02051c63.
Lemma F_8df28 : fetch_word Asan.M.loaded_segments (0x8df78 : word) = Some W_8df28.
Proof. vm_refl. Qed.
Lemma D_8df28 : decode_any W_8df28 = Some (Branch BC_NE 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df2c : bv 32 := 0x00048513.
Lemma F_8df2c : fetch_word Asan.M.loaded_segments (0x8df7c : word) = Some W_8df2c.
Proof. vm_refl. Qed.
Lemma D_8df2c : decode_any W_8df2c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df30 : bv 32 := 0xd48fa0ef.
Lemma F_8df30 : fetch_word Asan.M.loaded_segments (0x8df80 : word) = Some W_8df30.
Proof. vm_refl. Qed.
Lemma D_8df30 : decode_any W_8df30 = Some (Jal 1 2073928, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df34 : bv 32 := 0x00090513.
Lemma F_8df34 : fetch_word Asan.M.loaded_segments (0x8df84 : word) = Some W_8df34.
Proof. vm_refl. Qed.
Lemma D_8df34 : decode_any W_8df34 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df38 : bv 32 := 0x02813083.
Lemma F_8df38 : fetch_word Asan.M.loaded_segments (0x8df88 : word) = Some W_8df38.
Proof. vm_refl. Qed.
Lemma D_8df38 : decode_any W_8df38 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df3c : bv 32 := 0x02013403.
Lemma F_8df3c : fetch_word Asan.M.loaded_segments (0x8df8c : word) = Some W_8df3c.
Proof. vm_refl. Qed.
Lemma D_8df3c : decode_any W_8df3c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df40 : bv 32 := 0x01813483.
Lemma F_8df40 : fetch_word Asan.M.loaded_segments (0x8df90 : word) = Some W_8df40.
Proof. vm_refl. Qed.
Lemma D_8df40 : decode_any W_8df40 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df44 : bv 32 := 0x01013903.
Lemma F_8df44 : fetch_word Asan.M.loaded_segments (0x8df94 : word) = Some W_8df44.
Proof. vm_refl. Qed.
Lemma D_8df44 : decode_any W_8df44 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df48 : bv 32 := 0x03010113.
Lemma F_8df48 : fetch_word Asan.M.loaded_segments (0x8df98 : word) = Some W_8df48.
Proof. vm_refl. Qed.
Lemma D_8df48 : decode_any W_8df48 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8df4c : bv 32 := 0x00008067.
Lemma F_8df4c : fetch_word Asan.M.loaded_segments (0x8df9c : word) = Some W_8df4c.
Proof. vm_refl. Qed.
Lemma D_8df4c : decode_any W_8df4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
