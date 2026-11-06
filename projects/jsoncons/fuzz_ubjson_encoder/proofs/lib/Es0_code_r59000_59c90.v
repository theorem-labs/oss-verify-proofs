(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_ad3ec : bv 32 := 0x00008067.
Lemma F_ad3ec : fetch_word Plain.M.loaded_segments (0xad438 : word) = Some W_ad3ec.
Proof. vm_refl. Qed.
Lemma D_ad3ec : decode_any W_ad3ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad3f0 : bv 32 := 0xfddff06f.
Lemma F_ad3f0 : fetch_word Plain.M.loaded_segments (0xad43c : word) = Some W_ad3f0.
Proof. vm_refl. Qed.
Lemma D_ad3f0 : decode_any W_ad3f0 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

Definition W_aeb00 : bv 32 := 0x00050213.
Lemma F_aeb00 : fetch_word Plain.M.loaded_segments (0xaeb4c : word) = Some W_aeb00.
Proof. vm_refl. Qed.
Lemma D_aeb00 : decode_any W_aeb00 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aeb04 : bv 32 := 0x00000513.
Lemma F_aeb04 : fetch_word Plain.M.loaded_segments (0xaeb50 : word) = Some W_aeb04.
Proof. vm_refl. Qed.
Lemma D_aeb04 : decode_any W_aeb04 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aeb08 : bv 32 := 0x00008067.
Lemma F_aeb08 : fetch_word Plain.M.loaded_segments (0xaeb54 : word) = Some W_aeb08.
Proof. vm_refl. Qed.
Lemma D_aeb08 : decode_any W_aeb08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b12e4 : bv 32 := 0xff010113.
Lemma F_b12e4 : fetch_word Plain.M.loaded_segments (0xb1330 : word) = Some W_b12e4.
Proof. vm_refl. Qed.
Lemma D_b12e4 : decode_any W_b12e4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_b12e8 : bv 32 := 0x00113423.
Lemma F_b12e8 : fetch_word Plain.M.loaded_segments (0xb1334 : word) = Some W_b12e8.
Proof. vm_refl. Qed.
Lemma D_b12e8 : decode_any W_b12e8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b12ec : bv 32 := 0xe5def0ef.
Lemma F_b12ec : fetch_word Plain.M.loaded_segments (0xb1338 : word) = Some W_b12ec.
Proof. vm_refl. Qed.
Lemma D_b12ec : decode_any W_b12ec = Some (Jal 1 2031196, 4%Z).
Proof. vm_refl. Qed.

Definition W_b12f0 : bv 32 := 0x00050593.
Lemma F_b12f0 : fetch_word Plain.M.loaded_segments (0xb133c : word) = Some W_b12f0.
Proof. vm_refl. Qed.
Lemma D_b12f0 : decode_any W_b12f0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b12f4 : bv 32 := 0x03900513.
Lemma F_b12f4 : fetch_word Plain.M.loaded_segments (0xb1340 : word) = Some W_b12f4.
Proof. vm_refl. Qed.
Lemma D_b12f4 : decode_any W_b12f4 = Some (OpImm ALU_ADD 10 0 57, 4%Z).
Proof. vm_refl. Qed.

Definition W_b12f8 : bv 32 := 0x00000613.
Lemma F_b12f8 : fetch_word Plain.M.loaded_segments (0xb1344 : word) = Some W_b12f8.
Proof. vm_refl. Qed.
Lemma D_b12f8 : decode_any W_b12f8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b12fc : bv 32 := 0x00000693.
Lemma F_b12fc : fetch_word Plain.M.loaded_segments (0xb1348 : word) = Some W_b12fc.
Proof. vm_refl. Qed.
Lemma D_b12fc : decode_any W_b12fc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1300 : bv 32 := 0x00000713.
Lemma F_b1300 : fetch_word Plain.M.loaded_segments (0xb134c : word) = Some W_b1300.
Proof. vm_refl. Qed.
Lemma D_b1300 : decode_any W_b1300 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1304 : bv 32 := 0x00000793.
Lemma F_b1304 : fetch_word Plain.M.loaded_segments (0xb1350 : word) = Some W_b1304.
Proof. vm_refl. Qed.
Lemma D_b1304 : decode_any W_b1304 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1308 : bv 32 := 0x00000813.
Lemma F_b1308 : fetch_word Plain.M.loaded_segments (0xb1354 : word) = Some W_b1308.
Proof. vm_refl. Qed.
Lemma D_b1308 : decode_any W_b1308 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b130c : bv 32 := 0x8e4fc0ef.
Lemma F_b130c : fetch_word Plain.M.loaded_segments (0xb1358 : word) = Some W_b130c.
Proof. vm_refl. Qed.
Lemma D_b130c : decode_any W_b130c = Some (Jal 1 2080996, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1310 : bv 32 := 0x0005051b.
Lemma F_b1310 : fetch_word Plain.M.loaded_segments (0xb135c : word) = Some W_b1310.
Proof. vm_refl. Qed.
Lemma D_b1310 : decode_any W_b1310 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1314 : bv 32 := 0x00450593.
Lemma F_b1314 : fetch_word Plain.M.loaded_segments (0xb1360 : word) = Some W_b1314.
Proof. vm_refl. Qed.
Lemma D_b1314 : decode_any W_b1314 = Some (OpImm ALU_ADD 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1318 : bv 32 := 0x0015b593.
Lemma F_b1318 : fetch_word Plain.M.loaded_segments (0xb1364 : word) = Some W_b1318.
Proof. vm_refl. Qed.
Lemma D_b1318 : decode_any W_b1318 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b131c : bv 32 := 0xfff58593.
Lemma F_b131c : fetch_word Plain.M.loaded_segments (0xb1368 : word) = Some W_b131c.
Proof. vm_refl. Qed.
Lemma D_b131c : decode_any W_b131c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1320 : bv 32 := 0x00a5f533.
Lemma F_b1320 : fetch_word Plain.M.loaded_segments (0xb136c : word) = Some W_b1320.
Proof. vm_refl. Qed.
Lemma D_b1320 : decode_any W_b1320 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1324 : bv 32 := 0xc49ea0ef.
Lemma F_b1324 : fetch_word Plain.M.loaded_segments (0xb1370 : word) = Some W_b1324.
Proof. vm_refl. Qed.
Lemma D_b1324 : decode_any W_b1324 = Some (Jal 1 2010184, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1328 : bv 32 := 0x0005051b.
Lemma F_b1328 : fetch_word Plain.M.loaded_segments (0xb1374 : word) = Some W_b1328.
Proof. vm_refl. Qed.
Lemma D_b1328 : decode_any W_b1328 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b132c : bv 32 := 0x00813083.
Lemma F_b132c : fetch_word Plain.M.loaded_segments (0xb1378 : word) = Some W_b132c.
Proof. vm_refl. Qed.
Lemma D_b132c : decode_any W_b132c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1330 : bv 32 := 0x01010113.
Lemma F_b1330 : fetch_word Plain.M.loaded_segments (0xb137c : word) = Some W_b1330.
Proof. vm_refl. Qed.
Lemma D_b1330 : decode_any W_b1330 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1334 : bv 32 := 0x00008067.
Lemma F_b1334 : fetch_word Plain.M.loaded_segments (0xb1380 : word) = Some W_b1334.
Proof. vm_refl. Qed.
Lemma D_b1334 : decode_any W_b1334 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1344 : bv 32 := 0xff010113.
Lemma F_b1344 : fetch_word Plain.M.loaded_segments (0xb1390 : word) = Some W_b1344.
Proof. vm_refl. Qed.
Lemma D_b1344 : decode_any W_b1344 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1348 : bv 32 := 0x00113423.
Lemma F_b1348 : fetch_word Plain.M.loaded_segments (0xb1394 : word) = Some W_b1348.
Proof. vm_refl. Qed.
Lemma D_b1348 : decode_any W_b1348 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b134c : bv 32 := 0x00060693.
Lemma F_b134c : fetch_word Plain.M.loaded_segments (0xb1398 : word) = Some W_b134c.
Proof. vm_refl. Qed.
Lemma D_b134c : decode_any W_b134c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1350 : bv 32 := 0x00058613.
Lemma F_b1350 : fetch_word Plain.M.loaded_segments (0xb139c : word) = Some W_b1350.
Proof. vm_refl. Qed.
Lemma D_b1350 : decode_any W_b1350 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1354 : bv 32 := 0x00050593.
Lemma F_b1354 : fetch_word Plain.M.loaded_segments (0xb13a0 : word) = Some W_b1354.
Proof. vm_refl. Qed.
Lemma D_b1354 : decode_any W_b1354 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1358 : bv 32 := 0x03f00513.
Lemma F_b1358 : fetch_word Plain.M.loaded_segments (0xb13a4 : word) = Some W_b1358.
Proof. vm_refl. Qed.
Lemma D_b1358 : decode_any W_b1358 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_b135c : bv 32 := 0x00000713.
Lemma F_b135c : fetch_word Plain.M.loaded_segments (0xb13a8 : word) = Some W_b135c.
Proof. vm_refl. Qed.
Lemma D_b135c : decode_any W_b135c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1360 : bv 32 := 0x00000793.
Lemma F_b1360 : fetch_word Plain.M.loaded_segments (0xb13ac : word) = Some W_b1360.
Proof. vm_refl. Qed.
Lemma D_b1360 : decode_any W_b1360 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1364 : bv 32 := 0x00000813.
Lemma F_b1364 : fetch_word Plain.M.loaded_segments (0xb13b0 : word) = Some W_b1364.
Proof. vm_refl. Qed.
Lemma D_b1364 : decode_any W_b1364 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1368 : bv 32 := 0x888fc0ef.
Lemma F_b1368 : fetch_word Plain.M.loaded_segments (0xb13b4 : word) = Some W_b1368.
Proof. vm_refl. Qed.
Lemma D_b1368 : decode_any W_b1368 = Some (Jal 1 2080904, 4%Z).
Proof. vm_refl. Qed.

Definition W_b136c : bv 32 := 0x00813083.
Lemma F_b136c : fetch_word Plain.M.loaded_segments (0xb13b8 : word) = Some W_b136c.
Proof. vm_refl. Qed.
Lemma D_b136c : decode_any W_b136c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1370 : bv 32 := 0x01010113.
Lemma F_b1370 : fetch_word Plain.M.loaded_segments (0xb13bc : word) = Some W_b1370.
Proof. vm_refl. Qed.
Lemma D_b1370 : decode_any W_b1370 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b1374 : bv 32 := 0xbf9ea06f.
Lemma F_b1374 : fetch_word Plain.M.loaded_segments (0xb13c0 : word) = Some W_b1374.
Proof. vm_refl. Qed.
Lemma D_b1374 : decode_any W_b1374 = Some (Jal 0 2010104, 4%Z).
Proof. vm_refl. Qed.

Definition W_b13bc : bv 32 := 0x00008067.
Lemma F_b13bc : fetch_word Plain.M.loaded_segments (0xb1408 : word) = Some W_b13bc.
Proof. vm_refl. Qed.
Lemma D_b13bc : decode_any W_b13bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
