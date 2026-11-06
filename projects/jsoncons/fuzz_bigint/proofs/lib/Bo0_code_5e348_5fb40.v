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

Definition W_5e348 : bv 32 := 0x2590006f.
Lemma F_5e348 : fetch_word AsanUbsan.M.loaded_segments (0x5e348 : word) = Some W_5e348.
Proof. vm_refl. Qed.
Lemma D_5e348 : decode_any W_5e348 = Some (Jal 0 2648, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e34c : bv 32 := 0x5450006f.
Lemma F_5e34c : fetch_word AsanUbsan.M.loaded_segments (0x5e34c : word) = Some W_5e34c.
Proof. vm_refl. Qed.
Lemma D_5e34c : decode_any W_5e34c = Some (Jal 0 3396, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e350 : bv 32 := 0x2000106f.
Lemma F_5e350 : fetch_word AsanUbsan.M.loaded_segments (0x5e350 : word) = Some W_5e350.
Proof. vm_refl. Qed.
Lemma D_5e350 : decode_any W_5e350 = Some (Jal 0 4608, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e354 : bv 32 := 0x81010113.
Lemma F_5e354 : fetch_word AsanUbsan.M.loaded_segments (0x5e354 : word) = Some W_5e354.
Proof. vm_refl. Qed.
Lemma D_5e354 : decode_any W_5e354 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e358 : bv 32 := 0x7e113423.
Lemma F_5e358 : fetch_word AsanUbsan.M.loaded_segments (0x5e358 : word) = Some W_5e358.
Proof. vm_refl. Qed.
Lemma D_5e358 : decode_any W_5e358 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e35c : bv 32 := 0x7e813023.
Lemma F_5e35c : fetch_word AsanUbsan.M.loaded_segments (0x5e35c : word) = Some W_5e35c.
Proof. vm_refl. Qed.
Lemma D_5e35c : decode_any W_5e35c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e360 : bv 32 := 0x7c913c23.
Lemma F_5e360 : fetch_word AsanUbsan.M.loaded_segments (0x5e360 : word) = Some W_5e360.
Proof. vm_refl. Qed.
Lemma D_5e360 : decode_any W_5e360 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e364 : bv 32 := 0x7d213823.
Lemma F_5e364 : fetch_word AsanUbsan.M.loaded_segments (0x5e364 : word) = Some W_5e364.
Proof. vm_refl. Qed.
Lemma D_5e364 : decode_any W_5e364 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e368 : bv 32 := 0x7d313423.
Lemma F_5e368 : fetch_word AsanUbsan.M.loaded_segments (0x5e368 : word) = Some W_5e368.
Proof. vm_refl. Qed.
Lemma D_5e368 : decode_any W_5e368 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e36c : bv 32 := 0x7d413023.
Lemma F_5e36c : fetch_word AsanUbsan.M.loaded_segments (0x5e36c : word) = Some W_5e36c.
Proof. vm_refl. Qed.
Lemma D_5e36c : decode_any W_5e36c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e370 : bv 32 := 0x7b513c23.
Lemma F_5e370 : fetch_word AsanUbsan.M.loaded_segments (0x5e370 : word) = Some W_5e370.
Proof. vm_refl. Qed.
Lemma D_5e370 : decode_any W_5e370 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e374 : bv 32 := 0x7b613823.
Lemma F_5e374 : fetch_word AsanUbsan.M.loaded_segments (0x5e374 : word) = Some W_5e374.
Proof. vm_refl. Qed.
Lemma D_5e374 : decode_any W_5e374 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e378 : bv 32 := 0x7b713423.
Lemma F_5e378 : fetch_word AsanUbsan.M.loaded_segments (0x5e378 : word) = Some W_5e378.
Proof. vm_refl. Qed.
Lemma D_5e378 : decode_any W_5e378 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e37c : bv 32 := 0x7f010413.
Lemma F_5e37c : fetch_word AsanUbsan.M.loaded_segments (0x5e37c : word) = Some W_5e37c.
Proof. vm_refl. Qed.
Lemma D_5e37c : decode_any W_5e37c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e380 : bv 32 := 0xf9010113.
Lemma F_5e380 : fetch_word AsanUbsan.M.loaded_segments (0x5e380 : word) = Some W_5e380.
Proof. vm_refl. Qed.
Lemma D_5e380 : decode_any W_5e380 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e384 : bv 32 := 0x00079697.
Lemma F_5e384 : fetch_word AsanUbsan.M.loaded_segments (0x5e384 : word) = Some W_5e384.
Proof. vm_refl. Qed.
Lemma D_5e384 : decode_any W_5e384 = Some (Auipc 13 121, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e388 : bv 32 := 0xcac6b683.
Lemma F_5e388 : fetch_word AsanUbsan.M.loaded_segments (0x5e388 : word) = Some W_5e388.
Proof. vm_refl. Qed.
Lemma D_5e388 : decode_any W_5e388 = Some (Load SZ8 true 13 13 3244, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e38c : bv 32 := 0x0006c683.
Lemma F_5e38c : fetch_word AsanUbsan.M.loaded_segments (0x5e38c : word) = Some W_5e38c.
Proof. vm_refl. Qed.
Lemma D_5e38c : decode_any W_5e38c = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e390 : bv 32 := 0x0e068863.
Lemma F_5e390 : fetch_word AsanUbsan.M.loaded_segments (0x5e390 : word) = Some W_5e390.
Proof. vm_refl. Qed.
Lemma D_5e390 : decode_any W_5e390 = Some (Branch BC_EQ 13 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e394 : bv 32 := 0x80040a13.
Lemma F_5e394 : fetch_word AsanUbsan.M.loaded_segments (0x5e394 : word) = Some W_5e394.
Proof. vm_refl. Qed.
Lemma D_5e394 : decode_any W_5e394 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e398 : bv 32 := 0xfa0a0a13.
Lemma F_5e398 : fetch_word AsanUbsan.M.loaded_segments (0x5e398 : word) = Some W_5e398.
Proof. vm_refl. Qed.
Lemma D_5e398 : decode_any W_5e398 = Some (OpImm ALU_ADD 20 20 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e39c : bv 32 := 0x00c58ab3.
Lemma F_5e39c : fetch_word AsanUbsan.M.loaded_segments (0x5e39c : word) = Some W_5e39c.
Proof. vm_refl. Qed.
Lemma D_5e39c : decode_any W_5e39c = Some (Op ALU_ADD 21 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3a0 : bv 32 := 0x00c509b3.
Lemma F_5e3a0 : fetch_word AsanUbsan.M.loaded_segments (0x5e3a0 : word) = Some W_5e3a0.
Proof. vm_refl. Qed.
Lemma D_5e3a0 : decode_any W_5e3a0 = Some (Op ALU_ADD 19 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3a4 : bv 32 := 0x00b50663.
Lemma F_5e3a4 : fetch_word AsanUbsan.M.loaded_segments (0x5e3a4 : word) = Some W_5e3a4.
Proof. vm_refl. Qed.
Lemma D_5e3a4 : decode_any W_5e3a4 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3a8 : bv 32 := 0x0135f463.
Lemma F_5e3a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e3a8 : word) = Some W_5e3a8.
Proof. vm_refl. Qed.
Lemma D_5e3a8 : decode_any W_5e3a8 = Some (Branch BC_GEU 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3ac : bv 32 := 0x1b556a63.
Lemma F_5e3ac : fetch_word AsanUbsan.M.loaded_segments (0x5e3ac : word) = Some W_5e3ac.
Proof. vm_refl. Qed.
Lemma D_5e3ac : decode_any W_5e3ac = Some (Branch BC_LTU 10 21 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3b0 : bv 32 := 0xfff5c693.
Lemma F_5e3b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e3b0 : word) = Some W_5e3b0.
Proof. vm_refl. Qed.
Lemma D_5e3b0 : decode_any W_5e3b0 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3b4 : bv 32 := 0x26c6e463.
Lemma F_5e3b4 : fetch_word AsanUbsan.M.loaded_segments (0x5e3b4 : word) = Some W_5e3b4.
Proof. vm_refl. Qed.
Lemma D_5e3b4 : decode_any W_5e3b4 = Some (Branch BC_LTU 13 12 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3b8 : bv 32 := 0xfbf60b13.
Lemma F_5e3b8 : fetch_word AsanUbsan.M.loaded_segments (0x5e3b8 : word) = Some W_5e3b8.
Proof. vm_refl. Qed.
Lemma D_5e3b8 : decode_any W_5e3b8 = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3bc : bv 32 := 0xfbf00693.
Lemma F_5e3bc : fetch_word AsanUbsan.M.loaded_segments (0x5e3bc : word) = Some W_5e3bc.
Proof. vm_refl. Qed.
Lemma D_5e3bc : decode_any W_5e3bc = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3c0 : bv 32 := 0x2f66f263.
Lemma F_5e3c0 : fetch_word AsanUbsan.M.loaded_segments (0x5e3c0 : word) = Some W_5e3c0.
Proof. vm_refl. Qed.
Lemma D_5e3c0 : decode_any W_5e3c0 = Some (Branch BC_GEU 13 22 740, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3c4 : bv 32 := 0x00078697.
Lemma F_5e3c4 : fetch_word AsanUbsan.M.loaded_segments (0x5e3c4 : word) = Some W_5e3c4.
Proof. vm_refl. Qed.
Lemma D_5e3c4 : decode_any W_5e3c4 = Some (Auipc 13 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3c8 : bv 32 := 0x1046b683.
Lemma F_5e3c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e3c8 : word) = Some W_5e3c8.
Proof. vm_refl. Qed.
Lemma D_5e3c8 : decode_any W_5e3c8 = Some (Load SZ8 true 13 13 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3cc : bv 32 := 0x0006b703.
Lemma F_5e3cc : fetch_word AsanUbsan.M.loaded_segments (0x5e3cc : word) = Some W_5e3cc.
Proof. vm_refl. Qed.
Lemma D_5e3cc : decode_any W_5e3cc = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3d0 : bv 32 := 0xfffa8a93.
Lemma F_5e3d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e3d0 : word) = Some W_5e3d0.
Proof. vm_refl. Qed.
Lemma D_5e3d0 : decode_any W_5e3d0 = Some (OpImm ALU_ADD 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3d4 : bv 32 := 0x0035d693.
Lemma F_5e3d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e3d4 : word) = Some W_5e3d4.
Proof. vm_refl. Qed.
Lemma D_5e3d4 : decode_any W_5e3d4 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3d8 : bv 32 := 0x003ad793.
Lemma F_5e3d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e3d8 : word) = Some W_5e3d8.
Proof. vm_refl. Qed.
Lemma D_5e3d8 : decode_any W_5e3d8 = Some (ShiftImm ALU_SRL 15 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3dc : bv 32 := 0x00d706b3.
Lemma F_5e3dc : fetch_word AsanUbsan.M.loaded_segments (0x5e3dc : word) = Some W_5e3dc.
Proof. vm_refl. Qed.
Lemma D_5e3dc : decode_any W_5e3dc = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3e0 : bv 32 := 0x00f70733.
Lemma F_5e3e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e3e0 : word) = Some W_5e3e0.
Proof. vm_refl. Qed.
Lemma D_5e3e0 : decode_any W_5e3e0 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3e4 : bv 32 := 0xff86f793.
Lemma F_5e3e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e3e4 : word) = Some W_5e3e4.
Proof. vm_refl. Qed.
Lemma D_5e3e4 : decode_any W_5e3e4 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3e8 : bv 32 := 0xff877813.
Lemma F_5e3e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e3e8 : word) = Some W_5e3e8.
Proof. vm_refl. Qed.
Lemma D_5e3e8 : decode_any W_5e3e8 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3ec : bv 32 := 0x0007b783.
Lemma F_5e3ec : fetch_word AsanUbsan.M.loaded_segments (0x5e3ec : word) = Some W_5e3ec.
Proof. vm_refl. Qed.
Lemma D_5e3ec : decode_any W_5e3ec = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3f0 : bv 32 := 0x00083803.
Lemma F_5e3f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e3f0 : word) = Some W_5e3f0.
Proof. vm_refl. Qed.
Lemma D_5e3f0 : decode_any W_5e3f0 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3f4 : bv 32 := 0x00f867b3.
Lemma F_5e3f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e3f4 : word) = Some W_5e3f4.
Proof. vm_refl. Qed.
Lemma D_5e3f4 : decode_any W_5e3f4 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3f8 : bv 32 := 0x2a079a63.
Lemma F_5e3f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e3f8 : word) = Some W_5e3f8.
Proof. vm_refl. Qed.
Lemma D_5e3f8 : decode_any W_5e3f8 = Some (Branch BC_NE 15 0 692, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3fc : bv 32 := 0xfff54693.
Lemma F_5e3fc : fetch_word AsanUbsan.M.loaded_segments (0x5e3fc : word) = Some W_5e3fc.
Proof. vm_refl. Qed.
Lemma D_5e3fc : decode_any W_5e3fc = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e400 : bv 32 := 0x0cc6ea63.
Lemma F_5e400 : fetch_word AsanUbsan.M.loaded_segments (0x5e400 : word) = Some W_5e400.
Proof. vm_refl. Qed.
Lemma D_5e400 : decode_any W_5e400 = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e404 : bv 32 := 0xfbf00693.
Lemma F_5e404 : fetch_word AsanUbsan.M.loaded_segments (0x5e404 : word) = Some W_5e404.
Proof. vm_refl. Qed.
Lemma D_5e404 : decode_any W_5e404 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e408 : bv 32 := 0x1566f863.
Lemma F_5e408 : fetch_word AsanUbsan.M.loaded_segments (0x5e408 : word) = Some W_5e408.
Proof. vm_refl. Qed.
Lemma D_5e408 : decode_any W_5e408 = Some (Branch BC_GEU 13 22 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e40c : bv 32 := 0x00078697.
Lemma F_5e40c : fetch_word AsanUbsan.M.loaded_segments (0x5e40c : word) = Some W_5e40c.
Proof. vm_refl. Qed.
Lemma D_5e40c : decode_any W_5e40c = Some (Auipc 13 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e410 : bv 32 := 0x0bc6b683.
Lemma F_5e410 : fetch_word AsanUbsan.M.loaded_segments (0x5e410 : word) = Some W_5e410.
Proof. vm_refl. Qed.
Lemma D_5e410 : decode_any W_5e410 = Some (Load SZ8 true 13 13 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e414 : bv 32 := 0x0006b703.
Lemma F_5e414 : fetch_word AsanUbsan.M.loaded_segments (0x5e414 : word) = Some W_5e414.
Proof. vm_refl. Qed.
Lemma D_5e414 : decode_any W_5e414 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e418 : bv 32 := 0xfff98993.
Lemma F_5e418 : fetch_word AsanUbsan.M.loaded_segments (0x5e418 : word) = Some W_5e418.
Proof. vm_refl. Qed.
Lemma D_5e418 : decode_any W_5e418 = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e41c : bv 32 := 0x00355693.
Lemma F_5e41c : fetch_word AsanUbsan.M.loaded_segments (0x5e41c : word) = Some W_5e41c.
Proof. vm_refl. Qed.
Lemma D_5e41c : decode_any W_5e41c = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e420 : bv 32 := 0x0039d793.
Lemma F_5e420 : fetch_word AsanUbsan.M.loaded_segments (0x5e420 : word) = Some W_5e420.
Proof. vm_refl. Qed.
Lemma D_5e420 : decode_any W_5e420 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e424 : bv 32 := 0x00d706b3.
Lemma F_5e424 : fetch_word AsanUbsan.M.loaded_segments (0x5e424 : word) = Some W_5e424.
Proof. vm_refl. Qed.
Lemma D_5e424 : decode_any W_5e424 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e428 : bv 32 := 0x00f70733.
Lemma F_5e428 : fetch_word AsanUbsan.M.loaded_segments (0x5e428 : word) = Some W_5e428.
Proof. vm_refl. Qed.
Lemma D_5e428 : decode_any W_5e428 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e42c : bv 32 := 0xff86f793.
Lemma F_5e42c : fetch_word AsanUbsan.M.loaded_segments (0x5e42c : word) = Some W_5e42c.
Proof. vm_refl. Qed.
Lemma D_5e42c : decode_any W_5e42c = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e430 : bv 32 := 0xff877813.
Lemma F_5e430 : fetch_word AsanUbsan.M.loaded_segments (0x5e430 : word) = Some W_5e430.
Proof. vm_refl. Qed.
Lemma D_5e430 : decode_any W_5e430 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e434 : bv 32 := 0x0007b783.
Lemma F_5e434 : fetch_word AsanUbsan.M.loaded_segments (0x5e434 : word) = Some W_5e434.
Proof. vm_refl. Qed.
Lemma D_5e434 : decode_any W_5e434 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e438 : bv 32 := 0x00083803.
Lemma F_5e438 : fetch_word AsanUbsan.M.loaded_segments (0x5e438 : word) = Some W_5e438.
Proof. vm_refl. Qed.
Lemma D_5e438 : decode_any W_5e438 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e43c : bv 32 := 0x00f867b3.
Lemma F_5e43c : fetch_word AsanUbsan.M.loaded_segments (0x5e43c : word) = Some W_5e43c.
Proof. vm_refl. Qed.
Lemma D_5e43c : decode_any W_5e43c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e440 : bv 32 := 0x30079863.
Lemma F_5e440 : fetch_word AsanUbsan.M.loaded_segments (0x5e440 : word) = Some W_5e440.
Proof. vm_refl. Qed.
Lemma D_5e440 : decode_any W_5e440 = Some (Branch BC_NE 15 0 784, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e444 : bv 32 := 0x0007a697.
Lemma F_5e444 : fetch_word AsanUbsan.M.loaded_segments (0x5e444 : word) = Some W_5e444.
Proof. vm_refl. Qed.
Lemma D_5e444 : decode_any W_5e444 = Some (Auipc 13 122, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e448 : bv 32 := 0xfdc6b683.
Lemma F_5e448 : fetch_word AsanUbsan.M.loaded_segments (0x5e448 : word) = Some W_5e448.
Proof. vm_refl. Qed.
Lemma D_5e448 : decode_any W_5e448 = Some (Load SZ8 true 13 13 4060, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e44c : bv 32 := 0x000680e7.
Lemma F_5e44c : fetch_word AsanUbsan.M.loaded_segments (0x5e44c : word) = Some W_5e44c.
Proof. vm_refl. Qed.
Lemma D_5e44c : decode_any W_5e44c = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e450 : bv 32 := 0x07010113.
Lemma F_5e450 : fetch_word AsanUbsan.M.loaded_segments (0x5e450 : word) = Some W_5e450.
Proof. vm_refl. Qed.
Lemma D_5e450 : decode_any W_5e450 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e454 : bv 32 := 0x7e813083.
Lemma F_5e454 : fetch_word AsanUbsan.M.loaded_segments (0x5e454 : word) = Some W_5e454.
Proof. vm_refl. Qed.
Lemma D_5e454 : decode_any W_5e454 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e458 : bv 32 := 0x7e013403.
Lemma F_5e458 : fetch_word AsanUbsan.M.loaded_segments (0x5e458 : word) = Some W_5e458.
Proof. vm_refl. Qed.
Lemma D_5e458 : decode_any W_5e458 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e45c : bv 32 := 0x7d813483.
Lemma F_5e45c : fetch_word AsanUbsan.M.loaded_segments (0x5e45c : word) = Some W_5e45c.
Proof. vm_refl. Qed.
Lemma D_5e45c : decode_any W_5e45c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e460 : bv 32 := 0x7d013903.
Lemma F_5e460 : fetch_word AsanUbsan.M.loaded_segments (0x5e460 : word) = Some W_5e460.
Proof. vm_refl. Qed.
Lemma D_5e460 : decode_any W_5e460 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e464 : bv 32 := 0x7c813983.
Lemma F_5e464 : fetch_word AsanUbsan.M.loaded_segments (0x5e464 : word) = Some W_5e464.
Proof. vm_refl. Qed.
Lemma D_5e464 : decode_any W_5e464 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e468 : bv 32 := 0x7c013a03.
Lemma F_5e468 : fetch_word AsanUbsan.M.loaded_segments (0x5e468 : word) = Some W_5e468.
Proof. vm_refl. Qed.
Lemma D_5e468 : decode_any W_5e468 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e46c : bv 32 := 0x7b813a83.
Lemma F_5e46c : fetch_word AsanUbsan.M.loaded_segments (0x5e46c : word) = Some W_5e46c.
Proof. vm_refl. Qed.
Lemma D_5e46c : decode_any W_5e46c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e470 : bv 32 := 0x7b013b03.
Lemma F_5e470 : fetch_word AsanUbsan.M.loaded_segments (0x5e470 : word) = Some W_5e470.
Proof. vm_refl. Qed.
Lemma D_5e470 : decode_any W_5e470 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e474 : bv 32 := 0x7a813b83.
Lemma F_5e474 : fetch_word AsanUbsan.M.loaded_segments (0x5e474 : word) = Some W_5e474.
Proof. vm_refl. Qed.
Lemma D_5e474 : decode_any W_5e474 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e478 : bv 32 := 0x7f010113.
Lemma F_5e478 : fetch_word AsanUbsan.M.loaded_segments (0x5e478 : word) = Some W_5e478.
Proof. vm_refl. Qed.
Lemma D_5e478 : decode_any W_5e478 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e47c : bv 32 := 0x00008067.
Lemma F_5e47c : fetch_word AsanUbsan.M.loaded_segments (0x5e47c : word) = Some W_5e47c.
Proof. vm_refl. Qed.
Lemma D_5e47c : decode_any W_5e47c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e480 : bv 32 := 0x00060913.
Lemma F_5e480 : fetch_word AsanUbsan.M.loaded_segments (0x5e480 : word) = Some W_5e480.
Proof. vm_refl. Qed.
Lemma D_5e480 : decode_any W_5e480 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e484 : bv 32 := 0x00058993.
Lemma F_5e484 : fetch_word AsanUbsan.M.loaded_segments (0x5e484 : word) = Some W_5e484.
Proof. vm_refl. Qed.
Lemma D_5e484 : decode_any W_5e484 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e488 : bv 32 := 0x00050493.
Lemma F_5e488 : fetch_word AsanUbsan.M.loaded_segments (0x5e488 : word) = Some W_5e488.
Proof. vm_refl. Qed.
Lemma D_5e488 : decode_any W_5e488 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e48c : bv 32 := 0x6c9070ef.
Lemma F_5e48c : fetch_word AsanUbsan.M.loaded_segments (0x5e48c : word) = Some W_5e48c.
Proof. vm_refl. Qed.
Lemma D_5e48c : decode_any W_5e48c = Some (Jal 1 32456, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e490 : bv 32 := 0x00098593.
Lemma F_5e490 : fetch_word AsanUbsan.M.loaded_segments (0x5e490 : word) = Some W_5e490.
Proof. vm_refl. Qed.
Lemma D_5e490 : decode_any W_5e490 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e494 : bv 32 := 0x00090613.
Lemma F_5e494 : fetch_word AsanUbsan.M.loaded_segments (0x5e494 : word) = Some W_5e494.
Proof. vm_refl. Qed.
Lemma D_5e494 : decode_any W_5e494 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e498 : bv 32 := 0x00050693.
Lemma F_5e498 : fetch_word AsanUbsan.M.loaded_segments (0x5e498 : word) = Some W_5e498.
Proof. vm_refl. Qed.
Lemma D_5e498 : decode_any W_5e498 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e49c : bv 32 := 0x00048513.
Lemma F_5e49c : fetch_word AsanUbsan.M.loaded_segments (0x5e49c : word) = Some W_5e49c.
Proof. vm_refl. Qed.
Lemma D_5e49c : decode_any W_5e49c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4a0 : bv 32 := 0xfa0692e3.
Lemma F_5e4a0 : fetch_word AsanUbsan.M.loaded_segments (0x5e4a0 : word) = Some W_5e4a0.
Proof. vm_refl. Qed.
Lemma D_5e4a0 : decode_any W_5e4a0 = Some (Branch BC_NE 13 0 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4a4 : bv 32 := 0x07010113.
Lemma F_5e4a4 : fetch_word AsanUbsan.M.loaded_segments (0x5e4a4 : word) = Some W_5e4a4.
Proof. vm_refl. Qed.
Lemma D_5e4a4 : decode_any W_5e4a4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4a8 : bv 32 := 0x7e813083.
Lemma F_5e4a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e4a8 : word) = Some W_5e4a8.
Proof. vm_refl. Qed.
Lemma D_5e4a8 : decode_any W_5e4a8 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4ac : bv 32 := 0x7e013403.
Lemma F_5e4ac : fetch_word AsanUbsan.M.loaded_segments (0x5e4ac : word) = Some W_5e4ac.
Proof. vm_refl. Qed.
Lemma D_5e4ac : decode_any W_5e4ac = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4b0 : bv 32 := 0x7d813483.
Lemma F_5e4b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e4b0 : word) = Some W_5e4b0.
Proof. vm_refl. Qed.
Lemma D_5e4b0 : decode_any W_5e4b0 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4b4 : bv 32 := 0x7d013903.
Lemma F_5e4b4 : fetch_word AsanUbsan.M.loaded_segments (0x5e4b4 : word) = Some W_5e4b4.
Proof. vm_refl. Qed.
Lemma D_5e4b4 : decode_any W_5e4b4 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4b8 : bv 32 := 0x7c813983.
Lemma F_5e4b8 : fetch_word AsanUbsan.M.loaded_segments (0x5e4b8 : word) = Some W_5e4b8.
Proof. vm_refl. Qed.
Lemma D_5e4b8 : decode_any W_5e4b8 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4bc : bv 32 := 0x7c013a03.
Lemma F_5e4bc : fetch_word AsanUbsan.M.loaded_segments (0x5e4bc : word) = Some W_5e4bc.
Proof. vm_refl. Qed.
Lemma D_5e4bc : decode_any W_5e4bc = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4c0 : bv 32 := 0x7b813a83.
Lemma F_5e4c0 : fetch_word AsanUbsan.M.loaded_segments (0x5e4c0 : word) = Some W_5e4c0.
Proof. vm_refl. Qed.
Lemma D_5e4c0 : decode_any W_5e4c0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4c4 : bv 32 := 0x7b013b03.
Lemma F_5e4c4 : fetch_word AsanUbsan.M.loaded_segments (0x5e4c4 : word) = Some W_5e4c4.
Proof. vm_refl. Qed.
Lemma D_5e4c4 : decode_any W_5e4c4 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4c8 : bv 32 := 0x7a813b83.
Lemma F_5e4c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e4c8 : word) = Some W_5e4c8.
Proof. vm_refl. Qed.
Lemma D_5e4c8 : decode_any W_5e4c8 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4cc : bv 32 := 0x7f010113.
Lemma F_5e4cc : fetch_word AsanUbsan.M.loaded_segments (0x5e4cc : word) = Some W_5e4cc.
Proof. vm_refl. Qed.
Lemma D_5e4cc : decode_any W_5e4cc = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4d0 : bv 32 := 0x0941306f.
Lemma F_5e4d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e4d0 : word) = Some W_5e4d0.
Proof. vm_refl. Qed.
Lemma D_5e4d0 : decode_any W_5e4d0 = Some (Jal 0 77972, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4d4 : bv 32 := 0x80040693.
Lemma F_5e4d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e4d4 : word) = Some W_5e4d4.
Proof. vm_refl. Qed.
Lemma D_5e4d4 : decode_any W_5e4d4 = Some (OpImm ALU_ADD 13 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4d8 : bv 32 := 0xfb068693.
Lemma F_5e4d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e4d8 : word) = Some W_5e4d8.
Proof. vm_refl. Qed.
Lemma D_5e4d8 : decode_any W_5e4d8 = Some (OpImm ALU_ADD 13 13 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4dc : bv 32 := 0x80040713.
Lemma F_5e4dc : fetch_word AsanUbsan.M.loaded_segments (0x5e4dc : word) = Some W_5e4dc.
Proof. vm_refl. Qed.
Lemma D_5e4dc : decode_any W_5e4dc = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4e0 : bv 32 := 0xfa070713.
Lemma F_5e4e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e4e0 : word) = Some W_5e4e0.
Proof. vm_refl. Qed.
Lemma D_5e4e0 : decode_any W_5e4e0 = Some (OpImm ALU_ADD 14 14 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4e4 : bv 32 := 0x7ff70b93.
Lemma F_5e4e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e4e4 : word) = Some W_5e4e4.
Proof. vm_refl. Qed.
Lemma D_5e4e4 : decode_any W_5e4e4 = Some (OpImm ALU_ADD 23 14 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4e8 : bv 32 := 0x000bb4a3.
Lemma F_5e4e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e4e8 : word) = Some W_5e4e8.
Proof. vm_refl. Qed.
Lemma D_5e4e8 : decode_any W_5e4e8 = Some (Store SZ8 23 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4ec : bv 32 := 0x00da3023.
Lemma F_5e4ec : fetch_word AsanUbsan.M.loaded_segments (0x5e4ec : word) = Some W_5e4ec.
Proof. vm_refl. Qed.
Lemma D_5e4ec : decode_any W_5e4ec = Some (Store SZ8 20 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4f0 : bv 32 := 0x000a3423.
Lemma F_5e4f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e4f0 : word) = Some W_5e4f0.
Proof. vm_refl. Qed.
Lemma D_5e4f0 : decode_any W_5e4f0 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4f4 : bv 32 := 0x00060493.
Lemma F_5e4f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e4f4 : word) = Some W_5e4f4.
Proof. vm_refl. Qed.
Lemma D_5e4f4 : decode_any W_5e4f4 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4f8 : bv 32 := 0x00058a93.
Lemma F_5e4f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e4f8 : word) = Some W_5e4f8.
Proof. vm_refl. Qed.
Lemma D_5e4f8 : decode_any W_5e4f8 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4fc : bv 32 := 0x00050913.
Lemma F_5e4fc : fetch_word AsanUbsan.M.loaded_segments (0x5e4fc : word) = Some W_5e4fc.
Proof. vm_refl. Qed.
Lemma D_5e4fc : decode_any W_5e4fc = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e500 : bv 32 := 0x5ac220ef.
Lemma F_5e500 : fetch_word AsanUbsan.M.loaded_segments (0x5e500 : word) = Some W_5e500.
Proof. vm_refl. Qed.
Lemma D_5e500 : decode_any W_5e500 = Some (Jal 1 140716, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e504 : bv 32 := 0x00050593.
Lemma F_5e504 : fetch_word AsanUbsan.M.loaded_segments (0x5e504 : word) = Some W_5e504.
Proof. vm_refl. Qed.
Lemma D_5e504 : decode_any W_5e504 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e508 : bv 32 := 0x00078517.
Lemma F_5e508 : fetch_word AsanUbsan.M.loaded_segments (0x5e508 : word) = Some W_5e508.
Proof. vm_refl. Qed.
Lemma D_5e508 : decode_any W_5e508 = Some (Auipc 10 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e50c : bv 32 := 0xfb053503.
Lemma F_5e50c : fetch_word AsanUbsan.M.loaded_segments (0x5e50c : word) = Some W_5e50c.
Proof. vm_refl. Qed.
Lemma D_5e50c : decode_any W_5e50c = Some (Load SZ8 true 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e510 : bv 32 := 0x02154703.
Lemma F_5e510 : fetch_word AsanUbsan.M.loaded_segments (0x5e510 : word) = Some W_5e510.
Proof. vm_refl. Qed.
Lemma D_5e510 : decode_any W_5e510 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e514 : bv 32 := 0x008bb4a3.
Lemma F_5e514 : fetch_word AsanUbsan.M.loaded_segments (0x5e514 : word) = Some W_5e514.
Proof. vm_refl. Qed.
Lemma D_5e514 : decode_any W_5e514 = Some (Store SZ8 23 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e518 : bv 32 := 0x80040513.
Lemma F_5e518 : fetch_word AsanUbsan.M.loaded_segments (0x5e518 : word) = Some W_5e518.
Proof. vm_refl. Qed.
Lemma D_5e518 : decode_any W_5e518 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e51c : bv 32 := 0xfa050513.
Lemma F_5e51c : fetch_word AsanUbsan.M.loaded_segments (0x5e51c : word) = Some W_5e51c.
Proof. vm_refl. Qed.
Lemma D_5e51c : decode_any W_5e51c = Some (OpImm ALU_ADD 10 10 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e520 : bv 32 := 0x0ff00793.
Lemma F_5e520 : fetch_word AsanUbsan.M.loaded_segments (0x5e520 : word) = Some W_5e520.
Proof. vm_refl. Qed.
Lemma D_5e520 : decode_any W_5e520 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e524 : bv 32 := 0x00040613.
Lemma F_5e524 : fetch_word AsanUbsan.M.loaded_segments (0x5e524 : word) = Some W_5e524.
Proof. vm_refl. Qed.
Lemma D_5e524 : decode_any W_5e524 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e528 : bv 32 := 0x00000693.
Lemma F_5e528 : fetch_word AsanUbsan.M.loaded_segments (0x5e528 : word) = Some W_5e528.
Proof. vm_refl. Qed.
Lemma D_5e528 : decode_any W_5e528 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e52c : bv 32 := 0x2d1090ef.
Lemma F_5e52c : fetch_word AsanUbsan.M.loaded_segments (0x5e52c : word) = Some W_5e52c.
Proof. vm_refl. Qed.
Lemma D_5e52c : decode_any W_5e52c = Some (Jal 1 39632, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e530 : bv 32 := 0x80040613.
Lemma F_5e530 : fetch_word AsanUbsan.M.loaded_segments (0x5e530 : word) = Some W_5e530.
Proof. vm_refl. Qed.
Lemma D_5e530 : decode_any W_5e530 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e534 : bv 32 := 0xfa060613.
Lemma F_5e534 : fetch_word AsanUbsan.M.loaded_segments (0x5e534 : word) = Some W_5e534.
Proof. vm_refl. Qed.
Lemma D_5e534 : decode_any W_5e534 = Some (OpImm ALU_ADD 12 12 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e538 : bv 32 := 0x00090513.
Lemma F_5e538 : fetch_word AsanUbsan.M.loaded_segments (0x5e538 : word) = Some W_5e538.
Proof. vm_refl. Qed.
Lemma D_5e538 : decode_any W_5e538 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e53c : bv 32 := 0x00048593.
Lemma F_5e53c : fetch_word AsanUbsan.M.loaded_segments (0x5e53c : word) = Some W_5e53c.
Proof. vm_refl. Qed.
Lemma D_5e53c : decode_any W_5e53c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e540 : bv 32 := 0x075060ef.
Lemma F_5e540 : fetch_word AsanUbsan.M.loaded_segments (0x5e540 : word) = Some W_5e540.
Proof. vm_refl. Qed.
Lemma D_5e540 : decode_any W_5e540 = Some (Jal 1 26740, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e544 : bv 32 := 0x00090513.
Lemma F_5e544 : fetch_word AsanUbsan.M.loaded_segments (0x5e544 : word) = Some W_5e544.
Proof. vm_refl. Qed.
Lemma D_5e544 : decode_any W_5e544 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e548 : bv 32 := 0x000a8593.
Lemma F_5e548 : fetch_word AsanUbsan.M.loaded_segments (0x5e548 : word) = Some W_5e548.
Proof. vm_refl. Qed.
Lemma D_5e548 : decode_any W_5e548 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e54c : bv 32 := 0x00048613.
Lemma F_5e54c : fetch_word AsanUbsan.M.loaded_segments (0x5e54c : word) = Some W_5e54c.
Proof. vm_refl. Qed.
Lemma D_5e54c : decode_any W_5e54c = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e550 : bv 32 := 0xfbf00693.
Lemma F_5e550 : fetch_word AsanUbsan.M.loaded_segments (0x5e550 : word) = Some W_5e550.
Proof. vm_refl. Qed.
Lemma D_5e550 : decode_any W_5e550 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e554 : bv 32 := 0xeb66ece3.
Lemma F_5e554 : fetch_word AsanUbsan.M.loaded_segments (0x5e554 : word) = Some W_5e554.
Proof. vm_refl. Qed.
Lemma D_5e554 : decode_any W_5e554 = Some (Branch BC_LTU 13 22 7864, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e558 : bv 32 := 0x22061663.
Lemma F_5e558 : fetch_word AsanUbsan.M.loaded_segments (0x5e558 : word) = Some W_5e558.
Proof. vm_refl. Qed.
Lemma D_5e558 : decode_any W_5e558 = Some (Branch BC_NE 12 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e55c : bv 32 := 0xee9ff06f.
Lemma F_5e55c : fetch_word AsanUbsan.M.loaded_segments (0x5e55c : word) = Some W_5e55c.
Proof. vm_refl. Qed.
Lemma D_5e55c : decode_any W_5e55c = Some (Jal 0 2096872, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e560 : bv 32 := 0x00050493.
Lemma F_5e560 : fetch_word AsanUbsan.M.loaded_segments (0x5e560 : word) = Some W_5e560.
Proof. vm_refl. Qed.
Lemma D_5e560 : decode_any W_5e560 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e564 : bv 32 := 0x00058913.
Lemma F_5e564 : fetch_word AsanUbsan.M.loaded_segments (0x5e564 : word) = Some W_5e564.
Proof. vm_refl. Qed.
Lemma D_5e564 : decode_any W_5e564 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e568 : bv 32 := 0x00060b13.
Lemma F_5e568 : fetch_word AsanUbsan.M.loaded_segments (0x5e568 : word) = Some W_5e568.
Proof. vm_refl. Qed.
Lemma D_5e568 : decode_any W_5e568 = Some (OpImm ALU_ADD 22 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e56c : bv 32 := 0x80040513.
Lemma F_5e56c : fetch_word AsanUbsan.M.loaded_segments (0x5e56c : word) = Some W_5e56c.
Proof. vm_refl. Qed.
Lemma D_5e56c : decode_any W_5e56c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e570 : bv 32 := 0xfb050513.
Lemma F_5e570 : fetch_word AsanUbsan.M.loaded_segments (0x5e570 : word) = Some W_5e570.
Proof. vm_refl. Qed.
Lemma D_5e570 : decode_any W_5e570 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e574 : bv 32 := 0x80040593.
Lemma F_5e574 : fetch_word AsanUbsan.M.loaded_segments (0x5e574 : word) = Some W_5e574.
Proof. vm_refl. Qed.
Lemma D_5e574 : decode_any W_5e574 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e578 : bv 32 := 0xfa058593.
Lemma F_5e578 : fetch_word AsanUbsan.M.loaded_segments (0x5e578 : word) = Some W_5e578.
Proof. vm_refl. Qed.
Lemma D_5e578 : decode_any W_5e578 = Some (OpImm ALU_ADD 11 11 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e57c : bv 32 := 0x7ff58b93.
Lemma F_5e57c : fetch_word AsanUbsan.M.loaded_segments (0x5e57c : word) = Some W_5e57c.
Proof. vm_refl. Qed.
Lemma D_5e57c : decode_any W_5e57c = Some (OpImm ALU_ADD 23 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e580 : bv 32 := 0x000bb4a3.
Lemma F_5e580 : fetch_word AsanUbsan.M.loaded_segments (0x5e580 : word) = Some W_5e580.
Proof. vm_refl. Qed.
Lemma D_5e580 : decode_any W_5e580 = Some (Store SZ8 23 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e584 : bv 32 := 0x00aa3023.
Lemma F_5e584 : fetch_word AsanUbsan.M.loaded_segments (0x5e584 : word) = Some W_5e584.
Proof. vm_refl. Qed.
Lemma D_5e584 : decode_any W_5e584 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e588 : bv 32 := 0x000a3423.
Lemma F_5e588 : fetch_word AsanUbsan.M.loaded_segments (0x5e588 : word) = Some W_5e588.
Proof. vm_refl. Qed.
Lemma D_5e588 : decode_any W_5e588 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e58c : bv 32 := 0x520220ef.
Lemma F_5e58c : fetch_word AsanUbsan.M.loaded_segments (0x5e58c : word) = Some W_5e58c.
Proof. vm_refl. Qed.
Lemma D_5e58c : decode_any W_5e58c = Some (Jal 1 140576, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e590 : bv 32 := 0x00050593.
Lemma F_5e590 : fetch_word AsanUbsan.M.loaded_segments (0x5e590 : word) = Some W_5e590.
Proof. vm_refl. Qed.
Lemma D_5e590 : decode_any W_5e590 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e594 : bv 32 := 0x00078517.
Lemma F_5e594 : fetch_word AsanUbsan.M.loaded_segments (0x5e594 : word) = Some W_5e594.
Proof. vm_refl. Qed.
Lemma D_5e594 : decode_any W_5e594 = Some (Auipc 10 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e598 : bv 32 := 0xf2453503.
Lemma F_5e598 : fetch_word AsanUbsan.M.loaded_segments (0x5e598 : word) = Some W_5e598.
Proof. vm_refl. Qed.
Lemma D_5e598 : decode_any W_5e598 = Some (Load SZ8 true 10 10 3876, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e59c : bv 32 := 0x02154703.
Lemma F_5e59c : fetch_word AsanUbsan.M.loaded_segments (0x5e59c : word) = Some W_5e59c.
Proof. vm_refl. Qed.
Lemma D_5e59c : decode_any W_5e59c = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5a0 : bv 32 := 0x008bb4a3.
Lemma F_5e5a0 : fetch_word AsanUbsan.M.loaded_segments (0x5e5a0 : word) = Some W_5e5a0.
Proof. vm_refl. Qed.
Lemma D_5e5a0 : decode_any W_5e5a0 = Some (Store SZ8 23 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5a4 : bv 32 := 0x80040513.
Lemma F_5e5a4 : fetch_word AsanUbsan.M.loaded_segments (0x5e5a4 : word) = Some W_5e5a4.
Proof. vm_refl. Qed.
Lemma D_5e5a4 : decode_any W_5e5a4 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5a8 : bv 32 := 0xfa050513.
Lemma F_5e5a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e5a8 : word) = Some W_5e5a8.
Proof. vm_refl. Qed.
Lemma D_5e5a8 : decode_any W_5e5a8 = Some (OpImm ALU_ADD 10 10 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5ac : bv 32 := 0x0ff00793.
Lemma F_5e5ac : fetch_word AsanUbsan.M.loaded_segments (0x5e5ac : word) = Some W_5e5ac.
Proof. vm_refl. Qed.
Lemma D_5e5ac : decode_any W_5e5ac = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5b0 : bv 32 := 0x00040613.
Lemma F_5e5b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e5b0 : word) = Some W_5e5b0.
Proof. vm_refl. Qed.
Lemma D_5e5b0 : decode_any W_5e5b0 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5b4 : bv 32 := 0x00000693.
Lemma F_5e5b4 : fetch_word AsanUbsan.M.loaded_segments (0x5e5b4 : word) = Some W_5e5b4.
Proof. vm_refl. Qed.
Lemma D_5e5b4 : decode_any W_5e5b4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5b8 : bv 32 := 0x245090ef.
Lemma F_5e5b8 : fetch_word AsanUbsan.M.loaded_segments (0x5e5b8 : word) = Some W_5e5b8.
Proof. vm_refl. Qed.
Lemma D_5e5b8 : decode_any W_5e5b8 = Some (Jal 1 39492, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5bc : bv 32 := 0xfffb7517.
Lemma F_5e5bc : fetch_word AsanUbsan.M.loaded_segments (0x5e5bc : word) = Some W_5e5bc.
Proof. vm_refl. Qed.
Lemma D_5e5bc : decode_any W_5e5bc = Some (Auipc 10 1048503, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5c0 : bv 32 := 0xac850513.
Lemma F_5e5c0 : fetch_word AsanUbsan.M.loaded_segments (0x5e5c0 : word) = Some W_5e5c0.
Proof. vm_refl. Qed.
Lemma D_5e5c0 : decode_any W_5e5c0 = Some (OpImm ALU_ADD 10 10 2760, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5c4 : bv 32 := 0x1e50a0ef.
Lemma F_5e5c4 : fetch_word AsanUbsan.M.loaded_segments (0x5e5c4 : word) = Some W_5e5c4.
Proof. vm_refl. Qed.
Lemma D_5e5c4 : decode_any W_5e5c4 = Some (Jal 1 43492, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5c8 : bv 32 := 0x04051063.
Lemma F_5e5c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e5c8 : word) = Some W_5e5c8.
Proof. vm_refl. Qed.
Lemma D_5e5c8 : decode_any W_5e5c8 = Some (Branch BC_NE 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5cc : bv 32 := 0x2450a0ef.
Lemma F_5e5cc : fetch_word AsanUbsan.M.loaded_segments (0x5e5cc : word) = Some W_5e5cc.
Proof. vm_refl. Qed.
Lemma D_5e5cc : decode_any W_5e5cc = Some (Jal 1 43588, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5d0 : bv 32 := 0x00050a63.
Lemma F_5e5d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e5d0 : word) = Some W_5e5d0.
Proof. vm_refl. Qed.
Lemma D_5e5d0 : decode_any W_5e5d0 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5d4 : bv 32 := 0x80040513.
Lemma F_5e5d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e5d4 : word) = Some W_5e5d4.
Proof. vm_refl. Qed.
Lemma D_5e5d4 : decode_any W_5e5d4 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5d8 : bv 32 := 0xfa050513.
Lemma F_5e5d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e5d8 : word) = Some W_5e5d8.
Proof. vm_refl. Qed.
Lemma D_5e5d8 : decode_any W_5e5d8 = Some (OpImm ALU_ADD 10 10 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5dc : bv 32 := 0x53d0a0ef.
Lemma F_5e5dc : fetch_word AsanUbsan.M.loaded_segments (0x5e5dc : word) = Some W_5e5dc.
Proof. vm_refl. Qed.
Lemma D_5e5dc : decode_any W_5e5dc = Some (Jal 1 44348, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5e0 : bv 32 := 0x02051463.
Lemma F_5e5e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e5e0 : word) = Some W_5e5e0.
Proof. vm_refl. Qed.
Lemma D_5e5e0 : decode_any W_5e5e0 = Some (Branch BC_NE 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5e4 : bv 32 := 0xfffb7517.
Lemma F_5e5e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e5e4 : word) = Some W_5e5e4.
Proof. vm_refl. Qed.
Lemma D_5e5e4 : decode_any W_5e5e4 = Some (Auipc 10 1048503, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5e8 : bv 32 := 0xaa050513.
Lemma F_5e5e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e5e8 : word) = Some W_5e5e8.
Proof. vm_refl. Qed.
Lemma D_5e5e8 : decode_any W_5e5e8 = Some (OpImm ALU_ADD 10 10 2720, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5ec : bv 32 := 0x80040793.
Lemma F_5e5ec : fetch_word AsanUbsan.M.loaded_segments (0x5e5ec : word) = Some W_5e5ec.
Proof. vm_refl. Qed.
Lemma D_5e5ec : decode_any W_5e5ec = Some (OpImm ALU_ADD 15 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5f0 : bv 32 := 0xfa078793.
Lemma F_5e5f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e5f0 : word) = Some W_5e5f0.
Proof. vm_refl. Qed.
Lemma D_5e5f0 : decode_any W_5e5f0 = Some (OpImm ALU_ADD 15 15 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5f4 : bv 32 := 0x00048593.
Lemma F_5e5f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e5f4 : word) = Some W_5e5f4.
Proof. vm_refl. Qed.
Lemma D_5e5f4 : decode_any W_5e5f4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5f8 : bv 32 := 0x000b0613.
Lemma F_5e5f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e5f8 : word) = Some W_5e5f8.
Proof. vm_refl. Qed.
Lemma D_5e5f8 : decode_any W_5e5f8 = Some (OpImm ALU_ADD 12 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5fc : bv 32 := 0x00090693.
Lemma F_5e5fc : fetch_word AsanUbsan.M.loaded_segments (0x5e5fc : word) = Some W_5e5fc.
Proof. vm_refl. Qed.
Lemma D_5e5fc : decode_any W_5e5fc = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e600 : bv 32 := 0x000b0713.
Lemma F_5e600 : fetch_word AsanUbsan.M.loaded_segments (0x5e600 : word) = Some W_5e600.
Proof. vm_refl. Qed.
Lemma D_5e600 : decode_any W_5e600 = Some (OpImm ALU_ADD 14 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e604 : bv 32 := 0x4dc060ef.
Lemma F_5e604 : fetch_word AsanUbsan.M.loaded_segments (0x5e604 : word) = Some W_5e604.
Proof. vm_refl. Qed.
Lemma D_5e604 : decode_any W_5e604 = Some (Jal 1 25820, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e608 : bv 32 := 0x000b0613.
Lemma F_5e608 : fetch_word AsanUbsan.M.loaded_segments (0x5e608 : word) = Some W_5e608.
Proof. vm_refl. Qed.
Lemma D_5e608 : decode_any W_5e608 = Some (OpImm ALU_ADD 12 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e60c : bv 32 := 0x00090593.
Lemma F_5e60c : fetch_word AsanUbsan.M.loaded_segments (0x5e60c : word) = Some W_5e60c.
Proof. vm_refl. Qed.
Lemma D_5e60c : decode_any W_5e60c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e610 : bv 32 := 0x00048513.
Lemma F_5e610 : fetch_word AsanUbsan.M.loaded_segments (0x5e610 : word) = Some W_5e610.
Proof. vm_refl. Qed.
Lemma D_5e610 : decode_any W_5e610 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e614 : bv 32 := 0xfff94693.
Lemma F_5e614 : fetch_word AsanUbsan.M.loaded_segments (0x5e614 : word) = Some W_5e614.
Proof. vm_refl. Qed.
Lemma D_5e614 : decode_any W_5e614 = Some (OpImm ALU_XOR 13 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e618 : bv 32 := 0xdb66f0e3.
Lemma F_5e618 : fetch_word AsanUbsan.M.loaded_segments (0x5e618 : word) = Some W_5e618.
Proof. vm_refl. Qed.
Lemma D_5e618 : decode_any W_5e618 = Some (Branch BC_GEU 13 22 7584, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e61c : bv 32 := 0x80040693.
Lemma F_5e61c : fetch_word AsanUbsan.M.loaded_segments (0x5e61c : word) = Some W_5e61c.
Proof. vm_refl. Qed.
Lemma D_5e61c : decode_any W_5e61c = Some (OpImm ALU_ADD 13 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e620 : bv 32 := 0xfb068693.
Lemma F_5e620 : fetch_word AsanUbsan.M.loaded_segments (0x5e620 : word) = Some W_5e620.
Proof. vm_refl. Qed.
Lemma D_5e620 : decode_any W_5e620 = Some (OpImm ALU_ADD 13 13 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e624 : bv 32 := 0x80040713.
Lemma F_5e624 : fetch_word AsanUbsan.M.loaded_segments (0x5e624 : word) = Some W_5e624.
Proof. vm_refl. Qed.
Lemma D_5e624 : decode_any W_5e624 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e628 : bv 32 := 0xfa070713.
Lemma F_5e628 : fetch_word AsanUbsan.M.loaded_segments (0x5e628 : word) = Some W_5e628.
Proof. vm_refl. Qed.
Lemma D_5e628 : decode_any W_5e628 = Some (OpImm ALU_ADD 14 14 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e62c : bv 32 := 0x7ff70b93.
Lemma F_5e62c : fetch_word AsanUbsan.M.loaded_segments (0x5e62c : word) = Some W_5e62c.
Proof. vm_refl. Qed.
Lemma D_5e62c : decode_any W_5e62c = Some (OpImm ALU_ADD 23 14 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e630 : bv 32 := 0x000bb4a3.
Lemma F_5e630 : fetch_word AsanUbsan.M.loaded_segments (0x5e630 : word) = Some W_5e630.
Proof. vm_refl. Qed.
Lemma D_5e630 : decode_any W_5e630 = Some (Store SZ8 23 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e634 : bv 32 := 0x00da3023.
Lemma F_5e634 : fetch_word AsanUbsan.M.loaded_segments (0x5e634 : word) = Some W_5e634.
Proof. vm_refl. Qed.
Lemma D_5e634 : decode_any W_5e634 = Some (Store SZ8 20 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e638 : bv 32 := 0x000a3423.
Lemma F_5e638 : fetch_word AsanUbsan.M.loaded_segments (0x5e638 : word) = Some W_5e638.
Proof. vm_refl. Qed.
Lemma D_5e638 : decode_any W_5e638 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e63c : bv 32 := 0x00060493.
Lemma F_5e63c : fetch_word AsanUbsan.M.loaded_segments (0x5e63c : word) = Some W_5e63c.
Proof. vm_refl. Qed.
Lemma D_5e63c : decode_any W_5e63c = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e640 : bv 32 := 0x00058913.
Lemma F_5e640 : fetch_word AsanUbsan.M.loaded_segments (0x5e640 : word) = Some W_5e640.
Proof. vm_refl. Qed.
Lemma D_5e640 : decode_any W_5e640 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e644 : bv 32 := 0x00050b13.
Lemma F_5e644 : fetch_word AsanUbsan.M.loaded_segments (0x5e644 : word) = Some W_5e644.
Proof. vm_refl. Qed.
Lemma D_5e644 : decode_any W_5e644 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e648 : bv 32 := 0x464220ef.
Lemma F_5e648 : fetch_word AsanUbsan.M.loaded_segments (0x5e648 : word) = Some W_5e648.
Proof. vm_refl. Qed.
Lemma D_5e648 : decode_any W_5e648 = Some (Jal 1 140388, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e64c : bv 32 := 0x00050593.
Lemma F_5e64c : fetch_word AsanUbsan.M.loaded_segments (0x5e64c : word) = Some W_5e64c.
Proof. vm_refl. Qed.
Lemma D_5e64c : decode_any W_5e64c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e650 : bv 32 := 0x00078517.
Lemma F_5e650 : fetch_word AsanUbsan.M.loaded_segments (0x5e650 : word) = Some W_5e650.
Proof. vm_refl. Qed.
Lemma D_5e650 : decode_any W_5e650 = Some (Auipc 10 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e654 : bv 32 := 0xe6853503.
Lemma F_5e654 : fetch_word AsanUbsan.M.loaded_segments (0x5e654 : word) = Some W_5e654.
Proof. vm_refl. Qed.
Lemma D_5e654 : decode_any W_5e654 = Some (Load SZ8 true 10 10 3688, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e658 : bv 32 := 0x02154703.
Lemma F_5e658 : fetch_word AsanUbsan.M.loaded_segments (0x5e658 : word) = Some W_5e658.
Proof. vm_refl. Qed.
Lemma D_5e658 : decode_any W_5e658 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e65c : bv 32 := 0x008bb4a3.
Lemma F_5e65c : fetch_word AsanUbsan.M.loaded_segments (0x5e65c : word) = Some W_5e65c.
Proof. vm_refl. Qed.
Lemma D_5e65c : decode_any W_5e65c = Some (Store SZ8 23 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e660 : bv 32 := 0x80040513.
Lemma F_5e660 : fetch_word AsanUbsan.M.loaded_segments (0x5e660 : word) = Some W_5e660.
Proof. vm_refl. Qed.
Lemma D_5e660 : decode_any W_5e660 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e664 : bv 32 := 0xfa050513.
Lemma F_5e664 : fetch_word AsanUbsan.M.loaded_segments (0x5e664 : word) = Some W_5e664.
Proof. vm_refl. Qed.
Lemma D_5e664 : decode_any W_5e664 = Some (OpImm ALU_ADD 10 10 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e668 : bv 32 := 0x0ff00793.
Lemma F_5e668 : fetch_word AsanUbsan.M.loaded_segments (0x5e668 : word) = Some W_5e668.
Proof. vm_refl. Qed.
Lemma D_5e668 : decode_any W_5e668 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e66c : bv 32 := 0x00040613.
Lemma F_5e66c : fetch_word AsanUbsan.M.loaded_segments (0x5e66c : word) = Some W_5e66c.
Proof. vm_refl. Qed.
Lemma D_5e66c : decode_any W_5e66c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e670 : bv 32 := 0x00000693.
Lemma F_5e670 : fetch_word AsanUbsan.M.loaded_segments (0x5e670 : word) = Some W_5e670.
Proof. vm_refl. Qed.
Lemma D_5e670 : decode_any W_5e670 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e674 : bv 32 := 0x189090ef.
Lemma F_5e674 : fetch_word AsanUbsan.M.loaded_segments (0x5e674 : word) = Some W_5e674.
Proof. vm_refl. Qed.
Lemma D_5e674 : decode_any W_5e674 = Some (Jal 1 39304, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e678 : bv 32 := 0x80040613.
Lemma F_5e678 : fetch_word AsanUbsan.M.loaded_segments (0x5e678 : word) = Some W_5e678.
Proof. vm_refl. Qed.
Lemma D_5e678 : decode_any W_5e678 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e67c : bv 32 := 0xfa060613.
Lemma F_5e67c : fetch_word AsanUbsan.M.loaded_segments (0x5e67c : word) = Some W_5e67c.
Proof. vm_refl. Qed.
Lemma D_5e67c : decode_any W_5e67c = Some (OpImm ALU_ADD 12 12 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e680 : bv 32 := 0x00090513.
Lemma F_5e680 : fetch_word AsanUbsan.M.loaded_segments (0x5e680 : word) = Some W_5e680.
Proof. vm_refl. Qed.
Lemma D_5e680 : decode_any W_5e680 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e684 : bv 32 := 0x00048593.
Lemma F_5e684 : fetch_word AsanUbsan.M.loaded_segments (0x5e684 : word) = Some W_5e684.
Proof. vm_refl. Qed.
Lemma D_5e684 : decode_any W_5e684 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e688 : bv 32 := 0x72c060ef.
Lemma F_5e688 : fetch_word AsanUbsan.M.loaded_segments (0x5e688 : word) = Some W_5e688.
Proof. vm_refl. Qed.
Lemma D_5e688 : decode_any W_5e688 = Some (Jal 1 26412, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e68c : bv 32 := 0x000b0513.
Lemma F_5e68c : fetch_word AsanUbsan.M.loaded_segments (0x5e68c : word) = Some W_5e68c.
Proof. vm_refl. Qed.
Lemma D_5e68c : decode_any W_5e68c = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e690 : bv 32 := 0x00090593.
Lemma F_5e690 : fetch_word AsanUbsan.M.loaded_segments (0x5e690 : word) = Some W_5e690.
Proof. vm_refl. Qed.
Lemma D_5e690 : decode_any W_5e690 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e694 : bv 32 := 0x00048613.
Lemma F_5e694 : fetch_word AsanUbsan.M.loaded_segments (0x5e694 : word) = Some W_5e694.
Proof. vm_refl. Qed.
Lemma D_5e694 : decode_any W_5e694 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e698 : bv 32 := 0xfbf48b13.
Lemma F_5e698 : fetch_word AsanUbsan.M.loaded_segments (0x5e698 : word) = Some W_5e698.
Proof. vm_refl. Qed.
Lemma D_5e698 : decode_any W_5e698 = Some (OpImm ALU_ADD 22 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e69c : bv 32 := 0xfbf00693.
Lemma F_5e69c : fetch_word AsanUbsan.M.loaded_segments (0x5e69c : word) = Some W_5e69c.
Proof. vm_refl. Qed.
Lemma D_5e69c : decode_any W_5e69c = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6a0 : bv 32 := 0xd366e2e3.
Lemma F_5e6a0 : fetch_word AsanUbsan.M.loaded_segments (0x5e6a0 : word) = Some W_5e6a0.
Proof. vm_refl. Qed.
Lemma D_5e6a0 : decode_any W_5e6a0 = Some (Branch BC_LTU 13 22 7460, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6a4 : bv 32 := 0x02061e63.
Lemma F_5e6a4 : fetch_word AsanUbsan.M.loaded_segments (0x5e6a4 : word) = Some W_5e6a4.
Proof. vm_refl. Qed.
Lemma D_5e6a4 : decode_any W_5e6a4 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6a8 : bv 32 := 0xd55ff06f.
Lemma F_5e6a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e6a8 : word) = Some W_5e6a8.
Proof. vm_refl. Qed.
Lemma D_5e6a8 : decode_any W_5e6a8 = Some (Jal 0 2096468, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6ac : bv 32 := 0x00070783.
Lemma F_5e6ac : fetch_word AsanUbsan.M.loaded_segments (0x5e6ac : word) = Some W_5e6ac.
Proof. vm_refl. Qed.
Lemma D_5e6ac : decode_any W_5e6ac = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6b0 : bv 32 := 0x007af813.
Lemma F_5e6b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e6b0 : word) = Some W_5e6b0.
Proof. vm_refl. Qed.
Lemma D_5e6b0 : decode_any W_5e6b0 = Some (OpImm ALU_AND 16 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6b4 : bv 32 := 0x00f038b3.
Lemma F_5e6b4 : fetch_word AsanUbsan.M.loaded_segments (0x5e6b4 : word) = Some W_5e6b4.
Proof. vm_refl. Qed.
Lemma D_5e6b4 : decode_any W_5e6b4 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6b8 : bv 32 := 0x00f827b3.
Lemma F_5e6b8 : fetch_word AsanUbsan.M.loaded_segments (0x5e6b8 : word) = Some W_5e6b8.
Proof. vm_refl. Qed.
Lemma D_5e6b8 : decode_any W_5e6b8 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6bc : bv 32 := 0x0017c793.
Lemma F_5e6bc : fetch_word AsanUbsan.M.loaded_segments (0x5e6bc : word) = Some W_5e6bc.
Proof. vm_refl. Qed.
Lemma D_5e6bc : decode_any W_5e6bc = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6c0 : bv 32 := 0x00f8f7b3.
Lemma F_5e6c0 : fetch_word AsanUbsan.M.loaded_segments (0x5e6c0 : word) = Some W_5e6c0.
Proof. vm_refl. Qed.
Lemma D_5e6c0 : decode_any W_5e6c0 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6c4 : bv 32 := 0x00e6fa63.
Lemma F_5e6c4 : fetch_word AsanUbsan.M.loaded_segments (0x5e6c4 : word) = Some W_5e6c4.
Proof. vm_refl. Qed.
Lemma D_5e6c4 : decode_any W_5e6c4 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6c8 : bv 32 := 0x0006c803.
Lemma F_5e6c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e6c8 : word) = Some W_5e6c8.
Proof. vm_refl. Qed.
Lemma D_5e6c8 : decode_any W_5e6c8 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6cc : bv 32 := 0x00168693.
Lemma F_5e6cc : fetch_word AsanUbsan.M.loaded_segments (0x5e6cc : word) = Some W_5e6cc.
Proof. vm_refl. Qed.
Lemma D_5e6cc : decode_any W_5e6cc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6d0 : bv 32 := 0x00f867b3.
Lemma F_5e6d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e6d0 : word) = Some W_5e6d0.
Proof. vm_refl. Qed.
Lemma D_5e6d0 : decode_any W_5e6d0 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6d4 : bv 32 := 0xfee69ae3.
Lemma F_5e6d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e6d4 : word) = Some W_5e6d4.
Proof. vm_refl. Qed.
Lemma D_5e6d4 : decode_any W_5e6d4 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6d8 : bv 32 := 0x0ff7f693.
Lemma F_5e6d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e6d8 : word) = Some W_5e6d8.
Proof. vm_refl. Qed.
Lemma D_5e6d8 : decode_any W_5e6d8 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6dc : bv 32 := 0xd20680e3.
Lemma F_5e6dc : fetch_word AsanUbsan.M.loaded_segments (0x5e6dc : word) = Some W_5e6dc.
Proof. vm_refl. Qed.
Lemma D_5e6dc : decode_any W_5e6dc = Some (Branch BC_EQ 13 0 7456, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6e0 : bv 32 := 0x00050a93.
Lemma F_5e6e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e6e0 : word) = Some W_5e6e0.
Proof. vm_refl. Qed.
Lemma D_5e6e0 : decode_any W_5e6e0 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6e4 : bv 32 := 0x00058513.
Lemma F_5e6e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e6e4 : word) = Some W_5e6e4.
Proof. vm_refl. Qed.
Lemma D_5e6e4 : decode_any W_5e6e4 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6e8 : bv 32 := 0x00058b93.
Lemma F_5e6e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e6e8 : word) = Some W_5e6e8.
Proof. vm_refl. Qed.
Lemma D_5e6e8 : decode_any W_5e6e8 = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6ec : bv 32 := 0x00060593.
Lemma F_5e6ec : fetch_word AsanUbsan.M.loaded_segments (0x5e6ec : word) = Some W_5e6ec.
Proof. vm_refl. Qed.
Lemma D_5e6ec : decode_any W_5e6ec = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6f0 : bv 32 := 0x00060493.
Lemma F_5e6f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e6f0 : word) = Some W_5e6f0.
Proof. vm_refl. Qed.
Lemma D_5e6f0 : decode_any W_5e6f0 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6f4 : bv 32 := 0x48c030ef.
Lemma F_5e6f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e6f4 : word) = Some W_5e6f4.
Proof. vm_refl. Qed.
Lemma D_5e6f4 : decode_any W_5e6f4 = Some (Jal 1 13452, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6f8 : bv 32 := 0x000b8593.
Lemma F_5e6f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e6f8 : word) = Some W_5e6f8.
Proof. vm_refl. Qed.
Lemma D_5e6f8 : decode_any W_5e6f8 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6fc : bv 32 := 0x00048613.
Lemma F_5e6fc : fetch_word AsanUbsan.M.loaded_segments (0x5e6fc : word) = Some W_5e6fc.
Proof. vm_refl. Qed.
Lemma D_5e6fc : decode_any W_5e6fc = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e700 : bv 32 := 0x00050913.
Lemma F_5e700 : fetch_word AsanUbsan.M.loaded_segments (0x5e700 : word) = Some W_5e700.
Proof. vm_refl. Qed.
Lemma D_5e700 : decode_any W_5e700 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e704 : bv 32 := 0x000a8513.
Lemma F_5e704 : fetch_word AsanUbsan.M.loaded_segments (0x5e704 : word) = Some W_5e704.
Proof. vm_refl. Qed.
Lemma D_5e704 : decode_any W_5e704 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e708 : bv 32 := 0xce090ae3.
Lemma F_5e708 : fetch_word AsanUbsan.M.loaded_segments (0x5e708 : word) = Some W_5e708.
Proof. vm_refl. Qed.
Lemma D_5e708 : decode_any W_5e708 = Some (Branch BC_EQ 18 0 7412, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e70c : bv 32 := 0x3a0220ef.
Lemma F_5e70c : fetch_word AsanUbsan.M.loaded_segments (0x5e70c : word) = Some W_5e70c.
Proof. vm_refl. Qed.
Lemma D_5e70c : decode_any W_5e70c = Some (Jal 1 140192, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e710 : bv 32 := 0xfffb2597.
Lemma F_5e710 : fetch_word AsanUbsan.M.loaded_segments (0x5e710 : word) = Some W_5e710.
Proof. vm_refl. Qed.
Lemma D_5e710 : decode_any W_5e710 = Some (Auipc 11 1048498, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e714 : bv 32 := 0xcf85b583.
Lemma F_5e714 : fetch_word AsanUbsan.M.loaded_segments (0x5e714 : word) = Some W_5e714.
Proof. vm_refl. Qed.
Lemma D_5e714 : decode_any W_5e714 = Some (Load SZ8 true 11 11 3320, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e718 : bv 32 := 0x00ba3023.
Lemma F_5e718 : fetch_word AsanUbsan.M.loaded_segments (0x5e718 : word) = Some W_5e718.
Proof. vm_refl. Qed.
Lemma D_5e718 : decode_any W_5e718 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e71c : bv 32 := 0x80040613.
Lemma F_5e71c : fetch_word AsanUbsan.M.loaded_segments (0x5e71c : word) = Some W_5e71c.
Proof. vm_refl. Qed.
Lemma D_5e71c : decode_any W_5e71c = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e720 : bv 32 := 0xfa060613.
Lemma F_5e720 : fetch_word AsanUbsan.M.loaded_segments (0x5e720 : word) = Some W_5e720.
Proof. vm_refl. Qed.
Lemma D_5e720 : decode_any W_5e720 = Some (OpImm ALU_ADD 12 12 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e724 : bv 32 := 0x00040593.
Lemma F_5e724 : fetch_word AsanUbsan.M.loaded_segments (0x5e724 : word) = Some W_5e724.
Proof. vm_refl. Qed.
Lemma D_5e724 : decode_any W_5e724 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e728 : bv 32 := 0x00090693.
Lemma F_5e728 : fetch_word AsanUbsan.M.loaded_segments (0x5e728 : word) = Some W_5e728.
Proof. vm_refl. Qed.
Lemma D_5e728 : decode_any W_5e728 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e72c : bv 32 := 0x00000713.
Lemma F_5e72c : fetch_word AsanUbsan.M.loaded_segments (0x5e72c : word) = Some W_5e72c.
Proof. vm_refl. Qed.
Lemma D_5e72c : decode_any W_5e72c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e730 : bv 32 := 0x00048793.
Lemma F_5e730 : fetch_word AsanUbsan.M.loaded_segments (0x5e730 : word) = Some W_5e730.
Proof. vm_refl. Qed.
Lemma D_5e730 : decode_any W_5e730 = Some (OpImm ALU_ADD 15 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e734 : bv 32 := 0x00000813.
Lemma F_5e734 : fetch_word AsanUbsan.M.loaded_segments (0x5e734 : word) = Some W_5e734.
Proof. vm_refl. Qed.
Lemma D_5e734 : decode_any W_5e734 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e738 : bv 32 := 0x00000893.
Lemma F_5e738 : fetch_word AsanUbsan.M.loaded_segments (0x5e738 : word) = Some W_5e738.
Proof. vm_refl. Qed.
Lemma D_5e738 : decode_any W_5e738 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e73c : bv 32 := 0x3d1060ef.
Lemma F_5e73c : fetch_word AsanUbsan.M.loaded_segments (0x5e73c : word) = Some W_5e73c.
Proof. vm_refl. Qed.
Lemma D_5e73c : decode_any W_5e73c = Some (Jal 1 27600, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e740 : bv 32 := 0x000a8513.
Lemma F_5e740 : fetch_word AsanUbsan.M.loaded_segments (0x5e740 : word) = Some W_5e740.
Proof. vm_refl. Qed.
Lemma D_5e740 : decode_any W_5e740 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e744 : bv 32 := 0x000b8593.
Lemma F_5e744 : fetch_word AsanUbsan.M.loaded_segments (0x5e744 : word) = Some W_5e744.
Proof. vm_refl. Qed.
Lemma D_5e744 : decode_any W_5e744 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e748 : bv 32 := 0x00048613.
Lemma F_5e748 : fetch_word AsanUbsan.M.loaded_segments (0x5e748 : word) = Some W_5e748.
Proof. vm_refl. Qed.
Lemma D_5e748 : decode_any W_5e748 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e74c : bv 32 := 0xcb1ff06f.
Lemma F_5e74c : fetch_word AsanUbsan.M.loaded_segments (0x5e74c : word) = Some W_5e74c.
Proof. vm_refl. Qed.
Lemma D_5e74c : decode_any W_5e74c = Some (Jal 0 2096304, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e750 : bv 32 := 0x00070783.
Lemma F_5e750 : fetch_word AsanUbsan.M.loaded_segments (0x5e750 : word) = Some W_5e750.
Proof. vm_refl. Qed.
Lemma D_5e750 : decode_any W_5e750 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e754 : bv 32 := 0x0079f813.
Lemma F_5e754 : fetch_word AsanUbsan.M.loaded_segments (0x5e754 : word) = Some W_5e754.
Proof. vm_refl. Qed.
Lemma D_5e754 : decode_any W_5e754 = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e758 : bv 32 := 0x00f038b3.
Lemma F_5e758 : fetch_word AsanUbsan.M.loaded_segments (0x5e758 : word) = Some W_5e758.
Proof. vm_refl. Qed.
Lemma D_5e758 : decode_any W_5e758 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e75c : bv 32 := 0x00f827b3.
Lemma F_5e75c : fetch_word AsanUbsan.M.loaded_segments (0x5e75c : word) = Some W_5e75c.
Proof. vm_refl. Qed.
Lemma D_5e75c : decode_any W_5e75c = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e760 : bv 32 := 0x0017c793.
Lemma F_5e760 : fetch_word AsanUbsan.M.loaded_segments (0x5e760 : word) = Some W_5e760.
Proof. vm_refl. Qed.
Lemma D_5e760 : decode_any W_5e760 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e764 : bv 32 := 0x00f8f7b3.
Lemma F_5e764 : fetch_word AsanUbsan.M.loaded_segments (0x5e764 : word) = Some W_5e764.
Proof. vm_refl. Qed.
Lemma D_5e764 : decode_any W_5e764 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e768 : bv 32 := 0x00e6fa63.
Lemma F_5e768 : fetch_word AsanUbsan.M.loaded_segments (0x5e768 : word) = Some W_5e768.
Proof. vm_refl. Qed.
Lemma D_5e768 : decode_any W_5e768 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e76c : bv 32 := 0x0006c803.
Lemma F_5e76c : fetch_word AsanUbsan.M.loaded_segments (0x5e76c : word) = Some W_5e76c.
Proof. vm_refl. Qed.
Lemma D_5e76c : decode_any W_5e76c = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e770 : bv 32 := 0x00168693.
Lemma F_5e770 : fetch_word AsanUbsan.M.loaded_segments (0x5e770 : word) = Some W_5e770.
Proof. vm_refl. Qed.
Lemma D_5e770 : decode_any W_5e770 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e774 : bv 32 := 0x00f867b3.
Lemma F_5e774 : fetch_word AsanUbsan.M.loaded_segments (0x5e774 : word) = Some W_5e774.
Proof. vm_refl. Qed.
Lemma D_5e774 : decode_any W_5e774 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e778 : bv 32 := 0xfee69ae3.
Lemma F_5e778 : fetch_word AsanUbsan.M.loaded_segments (0x5e778 : word) = Some W_5e778.
Proof. vm_refl. Qed.
Lemma D_5e778 : decode_any W_5e778 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e77c : bv 32 := 0x0ff7f693.
Lemma F_5e77c : fetch_word AsanUbsan.M.loaded_segments (0x5e77c : word) = Some W_5e77c.
Proof. vm_refl. Qed.
Lemma D_5e77c : decode_any W_5e77c = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e780 : bv 32 := 0xcc0682e3.
Lemma F_5e780 : fetch_word AsanUbsan.M.loaded_segments (0x5e780 : word) = Some W_5e780.
Proof. vm_refl. Qed.
Lemma D_5e780 : decode_any W_5e780 = Some (Branch BC_EQ 13 0 7364, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e784 : bv 32 := 0x00050493.
Lemma F_5e784 : fetch_word AsanUbsan.M.loaded_segments (0x5e784 : word) = Some W_5e784.
Proof. vm_refl. Qed.
Lemma D_5e784 : decode_any W_5e784 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e788 : bv 32 := 0x00058a93.
Lemma F_5e788 : fetch_word AsanUbsan.M.loaded_segments (0x5e788 : word) = Some W_5e788.
Proof. vm_refl. Qed.
Lemma D_5e788 : decode_any W_5e788 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e78c : bv 32 := 0x00060593.
Lemma F_5e78c : fetch_word AsanUbsan.M.loaded_segments (0x5e78c : word) = Some W_5e78c.
Proof. vm_refl. Qed.
Lemma D_5e78c : decode_any W_5e78c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e790 : bv 32 := 0x00060913.
Lemma F_5e790 : fetch_word AsanUbsan.M.loaded_segments (0x5e790 : word) = Some W_5e790.
Proof. vm_refl. Qed.
Lemma D_5e790 : decode_any W_5e790 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e794 : bv 32 := 0x3ec030ef.
Lemma F_5e794 : fetch_word AsanUbsan.M.loaded_segments (0x5e794 : word) = Some W_5e794.
Proof. vm_refl. Qed.
Lemma D_5e794 : decode_any W_5e794 = Some (Jal 1 13292, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e798 : bv 32 := 0x000a8593.
Lemma F_5e798 : fetch_word AsanUbsan.M.loaded_segments (0x5e798 : word) = Some W_5e798.
Proof. vm_refl. Qed.
Lemma D_5e798 : decode_any W_5e798 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e79c : bv 32 := 0x00090613.
Lemma F_5e79c : fetch_word AsanUbsan.M.loaded_segments (0x5e79c : word) = Some W_5e79c.
Proof. vm_refl. Qed.
Lemma D_5e79c : decode_any W_5e79c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7a0 : bv 32 := 0x00050993.
Lemma F_5e7a0 : fetch_word AsanUbsan.M.loaded_segments (0x5e7a0 : word) = Some W_5e7a0.
Proof. vm_refl. Qed.
Lemma D_5e7a0 : decode_any W_5e7a0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7a4 : bv 32 := 0x00048513.
Lemma F_5e7a4 : fetch_word AsanUbsan.M.loaded_segments (0x5e7a4 : word) = Some W_5e7a4.
Proof. vm_refl. Qed.
Lemma D_5e7a4 : decode_any W_5e7a4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7a8 : bv 32 := 0xc8098ee3.
Lemma F_5e7a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e7a8 : word) = Some W_5e7a8.
Proof. vm_refl. Qed.
Lemma D_5e7a8 : decode_any W_5e7a8 = Some (Branch BC_EQ 19 0 7324, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7ac : bv 32 := 0x300220ef.
Lemma F_5e7ac : fetch_word AsanUbsan.M.loaded_segments (0x5e7ac : word) = Some W_5e7ac.
Proof. vm_refl. Qed.
Lemma D_5e7ac : decode_any W_5e7ac = Some (Jal 1 140032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7b0 : bv 32 := 0xfffb2597.
Lemma F_5e7b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e7b0 : word) = Some W_5e7b0.
Proof. vm_refl. Qed.
Lemma D_5e7b0 : decode_any W_5e7b0 = Some (Auipc 11 1048498, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7b4 : bv 32 := 0xc585b583.
Lemma F_5e7b4 : fetch_word AsanUbsan.M.loaded_segments (0x5e7b4 : word) = Some W_5e7b4.
Proof. vm_refl. Qed.
Lemma D_5e7b4 : decode_any W_5e7b4 = Some (Load SZ8 true 11 11 3160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7b8 : bv 32 := 0x00ba3023.
Lemma F_5e7b8 : fetch_word AsanUbsan.M.loaded_segments (0x5e7b8 : word) = Some W_5e7b8.
Proof. vm_refl. Qed.
Lemma D_5e7b8 : decode_any W_5e7b8 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7bc : bv 32 := 0x80040613.
Lemma F_5e7bc : fetch_word AsanUbsan.M.loaded_segments (0x5e7bc : word) = Some W_5e7bc.
Proof. vm_refl. Qed.
Lemma D_5e7bc : decode_any W_5e7bc = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7c0 : bv 32 := 0xfa060613.
Lemma F_5e7c0 : fetch_word AsanUbsan.M.loaded_segments (0x5e7c0 : word) = Some W_5e7c0.
Proof. vm_refl. Qed.
Lemma D_5e7c0 : decode_any W_5e7c0 = Some (OpImm ALU_ADD 12 12 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7c4 : bv 32 := 0x00100713.
Lemma F_5e7c4 : fetch_word AsanUbsan.M.loaded_segments (0x5e7c4 : word) = Some W_5e7c4.
Proof. vm_refl. Qed.
Lemma D_5e7c4 : decode_any W_5e7c4 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7c8 : bv 32 := 0x00040593.
Lemma F_5e7c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e7c8 : word) = Some W_5e7c8.
Proof. vm_refl. Qed.
Lemma D_5e7c8 : decode_any W_5e7c8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7cc : bv 32 := 0x00098693.
Lemma F_5e7cc : fetch_word AsanUbsan.M.loaded_segments (0x5e7cc : word) = Some W_5e7cc.
Proof. vm_refl. Qed.
Lemma D_5e7cc : decode_any W_5e7cc = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d0 : bv 32 := 0x00090793.
Lemma F_5e7d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e7d0 : word) = Some W_5e7d0.
Proof. vm_refl. Qed.
Lemma D_5e7d0 : decode_any W_5e7d0 = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d4 : bv 32 := 0x00000813.
Lemma F_5e7d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e7d4 : word) = Some W_5e7d4.
Proof. vm_refl. Qed.
Lemma D_5e7d4 : decode_any W_5e7d4 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d8 : bv 32 := 0x00000893.
Lemma F_5e7d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e7d8 : word) = Some W_5e7d8.
Proof. vm_refl. Qed.
Lemma D_5e7d8 : decode_any W_5e7d8 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7dc : bv 32 := 0x331060ef.
Lemma F_5e7dc : fetch_word AsanUbsan.M.loaded_segments (0x5e7dc : word) = Some W_5e7dc.
Proof. vm_refl. Qed.
Lemma D_5e7dc : decode_any W_5e7dc = Some (Jal 1 27440, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e0 : bv 32 := 0x00048513.
Lemma F_5e7e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e7e0 : word) = Some W_5e7e0.
Proof. vm_refl. Qed.
Lemma D_5e7e0 : decode_any W_5e7e0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e4 : bv 32 := 0x000a8593.
Lemma F_5e7e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e7e4 : word) = Some W_5e7e4.
Proof. vm_refl. Qed.
Lemma D_5e7e4 : decode_any W_5e7e4 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e8 : bv 32 := 0x00090613.
Lemma F_5e7e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e7e8 : word) = Some W_5e7e8.
Proof. vm_refl. Qed.
Lemma D_5e7e8 : decode_any W_5e7e8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7ec : bv 32 := 0xc59ff06f.
Lemma F_5e7ec : fetch_word AsanUbsan.M.loaded_segments (0x5e7ec : word) = Some W_5e7ec.
Proof. vm_refl. Qed.
Lemma D_5e7ec : decode_any W_5e7ec = Some (Jal 0 2096216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7f0 : bv 32 := 0x81010113.
Lemma F_5e7f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e7f0 : word) = Some W_5e7f0.
Proof. vm_refl. Qed.
Lemma D_5e7f0 : decode_any W_5e7f0 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7f4 : bv 32 := 0x7e113423.
Lemma F_5e7f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e7f4 : word) = Some W_5e7f4.
Proof. vm_refl. Qed.
Lemma D_5e7f4 : decode_any W_5e7f4 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7f8 : bv 32 := 0x7e813023.
Lemma F_5e7f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e7f8 : word) = Some W_5e7f8.
Proof. vm_refl. Qed.
Lemma D_5e7f8 : decode_any W_5e7f8 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7fc : bv 32 := 0x7c913c23.
Lemma F_5e7fc : fetch_word AsanUbsan.M.loaded_segments (0x5e7fc : word) = Some W_5e7fc.
Proof. vm_refl. Qed.
Lemma D_5e7fc : decode_any W_5e7fc = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e800 : bv 32 := 0x7d213823.
Lemma F_5e800 : fetch_word AsanUbsan.M.loaded_segments (0x5e800 : word) = Some W_5e800.
Proof. vm_refl. Qed.
Lemma D_5e800 : decode_any W_5e800 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e804 : bv 32 := 0x7d313423.
Lemma F_5e804 : fetch_word AsanUbsan.M.loaded_segments (0x5e804 : word) = Some W_5e804.
Proof. vm_refl. Qed.
Lemma D_5e804 : decode_any W_5e804 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e808 : bv 32 := 0x7d413023.
Lemma F_5e808 : fetch_word AsanUbsan.M.loaded_segments (0x5e808 : word) = Some W_5e808.
Proof. vm_refl. Qed.
Lemma D_5e808 : decode_any W_5e808 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e80c : bv 32 := 0x7b513c23.
Lemma F_5e80c : fetch_word AsanUbsan.M.loaded_segments (0x5e80c : word) = Some W_5e80c.
Proof. vm_refl. Qed.
Lemma D_5e80c : decode_any W_5e80c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e810 : bv 32 := 0x7f010413.
Lemma F_5e810 : fetch_word AsanUbsan.M.loaded_segments (0x5e810 : word) = Some W_5e810.
Proof. vm_refl. Qed.
Lemma D_5e810 : decode_any W_5e810 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e814 : bv 32 := 0xfa010113.
Lemma F_5e814 : fetch_word AsanUbsan.M.loaded_segments (0x5e814 : word) = Some W_5e814.
Proof. vm_refl. Qed.
Lemma D_5e814 : decode_any W_5e814 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e818 : bv 32 := 0x00079697.
Lemma F_5e818 : fetch_word AsanUbsan.M.loaded_segments (0x5e818 : word) = Some W_5e818.
Proof. vm_refl. Qed.
Lemma D_5e818 : decode_any W_5e818 = Some (Auipc 13 121, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e81c : bv 32 := 0x8186b683.
Lemma F_5e81c : fetch_word AsanUbsan.M.loaded_segments (0x5e81c : word) = Some W_5e81c.
Proof. vm_refl. Qed.
Lemma D_5e81c : decode_any W_5e81c = Some (Load SZ8 true 13 13 2072, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e820 : bv 32 := 0x0006c683.
Lemma F_5e820 : fetch_word AsanUbsan.M.loaded_segments (0x5e820 : word) = Some W_5e820.
Proof. vm_refl. Qed.
Lemma D_5e820 : decode_any W_5e820 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e824 : bv 32 := 0x08068863.
Lemma F_5e824 : fetch_word AsanUbsan.M.loaded_segments (0x5e824 : word) = Some W_5e824.
Proof. vm_refl. Qed.
Lemma D_5e824 : decode_any W_5e824 = Some (Branch BC_EQ 13 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e828 : bv 32 := 0xfff54693.
Lemma F_5e828 : fetch_word AsanUbsan.M.loaded_segments (0x5e828 : word) = Some W_5e828.
Proof. vm_refl. Qed.
Lemma D_5e828 : decode_any W_5e828 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e82c : bv 32 := 0x80040a13.
Lemma F_5e82c : fetch_word AsanUbsan.M.loaded_segments (0x5e82c : word) = Some W_5e82c.
Proof. vm_refl. Qed.
Lemma D_5e82c : decode_any W_5e82c = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e830 : bv 32 := 0xfb0a0a13.
Lemma F_5e830 : fetch_word AsanUbsan.M.loaded_segments (0x5e830 : word) = Some W_5e830.
Proof. vm_refl. Qed.
Lemma D_5e830 : decode_any W_5e830 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e834 : bv 32 := 0x0cc6e663.
Lemma F_5e834 : fetch_word AsanUbsan.M.loaded_segments (0x5e834 : word) = Some W_5e834.
Proof. vm_refl. Qed.
Lemma D_5e834 : decode_any W_5e834 = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e838 : bv 32 := 0xfbf60693.
Lemma F_5e838 : fetch_word AsanUbsan.M.loaded_segments (0x5e838 : word) = Some W_5e838.
Proof. vm_refl. Qed.
Lemma D_5e838 : decode_any W_5e838 = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e83c : bv 32 := 0xfbf00713.
Lemma F_5e83c : fetch_word AsanUbsan.M.loaded_segments (0x5e83c : word) = Some W_5e83c.
Proof. vm_refl. Qed.
Lemma D_5e83c : decode_any W_5e83c = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e840 : bv 32 := 0x14d77463.
Lemma F_5e840 : fetch_word AsanUbsan.M.loaded_segments (0x5e840 : word) = Some W_5e840.
Proof. vm_refl. Qed.
Lemma D_5e840 : decode_any W_5e840 = Some (Branch BC_GEU 14 13 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e844 : bv 32 := 0x00078697.
Lemma F_5e844 : fetch_word AsanUbsan.M.loaded_segments (0x5e844 : word) = Some W_5e844.
Proof. vm_refl. Qed.
Lemma D_5e844 : decode_any W_5e844 = Some (Auipc 13 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e848 : bv 32 := 0xc846b683.
Lemma F_5e848 : fetch_word AsanUbsan.M.loaded_segments (0x5e848 : word) = Some W_5e848.
Proof. vm_refl. Qed.
Lemma D_5e848 : decode_any W_5e848 = Some (Load SZ8 true 13 13 3204, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e84c : bv 32 := 0x00c507b3.
Lemma F_5e84c : fetch_word AsanUbsan.M.loaded_segments (0x5e84c : word) = Some W_5e84c.
Proof. vm_refl. Qed.
Lemma D_5e84c : decode_any W_5e84c = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e850 : bv 32 := 0x0006b703.
Lemma F_5e850 : fetch_word AsanUbsan.M.loaded_segments (0x5e850 : word) = Some W_5e850.
Proof. vm_refl. Qed.
Lemma D_5e850 : decode_any W_5e850 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e854 : bv 32 := 0x00355693.
Lemma F_5e854 : fetch_word AsanUbsan.M.loaded_segments (0x5e854 : word) = Some W_5e854.
Proof. vm_refl. Qed.
Lemma D_5e854 : decode_any W_5e854 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e858 : bv 32 := 0xfff78793.
Lemma F_5e858 : fetch_word AsanUbsan.M.loaded_segments (0x5e858 : word) = Some W_5e858.
Proof. vm_refl. Qed.
Lemma D_5e858 : decode_any W_5e858 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e85c : bv 32 := 0x0037d813.
Lemma F_5e85c : fetch_word AsanUbsan.M.loaded_segments (0x5e85c : word) = Some W_5e85c.
Proof. vm_refl. Qed.
Lemma D_5e85c : decode_any W_5e85c = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e860 : bv 32 := 0x00d706b3.
Lemma F_5e860 : fetch_word AsanUbsan.M.loaded_segments (0x5e860 : word) = Some W_5e860.
Proof. vm_refl. Qed.
Lemma D_5e860 : decode_any W_5e860 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e864 : bv 32 := 0x01070733.
Lemma F_5e864 : fetch_word AsanUbsan.M.loaded_segments (0x5e864 : word) = Some W_5e864.
Proof. vm_refl. Qed.
Lemma D_5e864 : decode_any W_5e864 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e868 : bv 32 := 0xff86f813.
Lemma F_5e868 : fetch_word AsanUbsan.M.loaded_segments (0x5e868 : word) = Some W_5e868.
Proof. vm_refl. Qed.
Lemma D_5e868 : decode_any W_5e868 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e86c : bv 32 := 0xff877893.
Lemma F_5e86c : fetch_word AsanUbsan.M.loaded_segments (0x5e86c : word) = Some W_5e86c.
Proof. vm_refl. Qed.
Lemma D_5e86c : decode_any W_5e86c = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e870 : bv 32 := 0x00083803.
Lemma F_5e870 : fetch_word AsanUbsan.M.loaded_segments (0x5e870 : word) = Some W_5e870.
Proof. vm_refl. Qed.
Lemma D_5e870 : decode_any W_5e870 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e874 : bv 32 := 0x0008b883.
Lemma F_5e874 : fetch_word AsanUbsan.M.loaded_segments (0x5e874 : word) = Some W_5e874.
Proof. vm_refl. Qed.
Lemma D_5e874 : decode_any W_5e874 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e878 : bv 32 := 0x0108e833.
Lemma F_5e878 : fetch_word AsanUbsan.M.loaded_segments (0x5e878 : word) = Some W_5e878.
Proof. vm_refl. Qed.
Lemma D_5e878 : decode_any W_5e878 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e87c : bv 32 := 0x10081a63.
Lemma F_5e87c : fetch_word AsanUbsan.M.loaded_segments (0x5e87c : word) = Some W_5e87c.
Proof. vm_refl. Qed.
Lemma D_5e87c : decode_any W_5e87c = Some (Branch BC_NE 16 0 276, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e880 : bv 32 := 0x0007a697.
Lemma F_5e880 : fetch_word AsanUbsan.M.loaded_segments (0x5e880 : word) = Some W_5e880.
Proof. vm_refl. Qed.
Lemma D_5e880 : decode_any W_5e880 = Some (Auipc 13 122, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e884 : bv 32 := 0xba86b683.
Lemma F_5e884 : fetch_word AsanUbsan.M.loaded_segments (0x5e884 : word) = Some W_5e884.
Proof. vm_refl. Qed.
Lemma D_5e884 : decode_any W_5e884 = Some (Load SZ8 true 13 13 2984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e888 : bv 32 := 0x000680e7.
Lemma F_5e888 : fetch_word AsanUbsan.M.loaded_segments (0x5e888 : word) = Some W_5e888.
Proof. vm_refl. Qed.
Lemma D_5e888 : decode_any W_5e888 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e88c : bv 32 := 0x06010113.
Lemma F_5e88c : fetch_word AsanUbsan.M.loaded_segments (0x5e88c : word) = Some W_5e88c.
Proof. vm_refl. Qed.
Lemma D_5e88c : decode_any W_5e88c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e890 : bv 32 := 0x7e813083.
Lemma F_5e890 : fetch_word AsanUbsan.M.loaded_segments (0x5e890 : word) = Some W_5e890.
Proof. vm_refl. Qed.
Lemma D_5e890 : decode_any W_5e890 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e894 : bv 32 := 0x7e013403.
Lemma F_5e894 : fetch_word AsanUbsan.M.loaded_segments (0x5e894 : word) = Some W_5e894.
Proof. vm_refl. Qed.
Lemma D_5e894 : decode_any W_5e894 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e898 : bv 32 := 0x7d813483.
Lemma F_5e898 : fetch_word AsanUbsan.M.loaded_segments (0x5e898 : word) = Some W_5e898.
Proof. vm_refl. Qed.
Lemma D_5e898 : decode_any W_5e898 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e89c : bv 32 := 0x7d013903.
Lemma F_5e89c : fetch_word AsanUbsan.M.loaded_segments (0x5e89c : word) = Some W_5e89c.
Proof. vm_refl. Qed.
Lemma D_5e89c : decode_any W_5e89c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8a0 : bv 32 := 0x7c813983.
Lemma F_5e8a0 : fetch_word AsanUbsan.M.loaded_segments (0x5e8a0 : word) = Some W_5e8a0.
Proof. vm_refl. Qed.
Lemma D_5e8a0 : decode_any W_5e8a0 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8a4 : bv 32 := 0x7c013a03.
Lemma F_5e8a4 : fetch_word AsanUbsan.M.loaded_segments (0x5e8a4 : word) = Some W_5e8a4.
Proof. vm_refl. Qed.
Lemma D_5e8a4 : decode_any W_5e8a4 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8a8 : bv 32 := 0x7b813a83.
Lemma F_5e8a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e8a8 : word) = Some W_5e8a8.
Proof. vm_refl. Qed.
Lemma D_5e8a8 : decode_any W_5e8a8 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8ac : bv 32 := 0x7f010113.
Lemma F_5e8ac : fetch_word AsanUbsan.M.loaded_segments (0x5e8ac : word) = Some W_5e8ac.
Proof. vm_refl. Qed.
Lemma D_5e8ac : decode_any W_5e8ac = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8b0 : bv 32 := 0x00008067.
Lemma F_5e8b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e8b0 : word) = Some W_5e8b0.
Proof. vm_refl. Qed.
Lemma D_5e8b0 : decode_any W_5e8b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8b4 : bv 32 := 0x00060913.
Lemma F_5e8b4 : fetch_word AsanUbsan.M.loaded_segments (0x5e8b4 : word) = Some W_5e8b4.
Proof. vm_refl. Qed.
Lemma D_5e8b4 : decode_any W_5e8b4 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8b8 : bv 32 := 0x00058993.
Lemma F_5e8b8 : fetch_word AsanUbsan.M.loaded_segments (0x5e8b8 : word) = Some W_5e8b8.
Proof. vm_refl. Qed.
Lemma D_5e8b8 : decode_any W_5e8b8 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8bc : bv 32 := 0x00050493.
Lemma F_5e8bc : fetch_word AsanUbsan.M.loaded_segments (0x5e8bc : word) = Some W_5e8bc.
Proof. vm_refl. Qed.
Lemma D_5e8bc : decode_any W_5e8bc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8c0 : bv 32 := 0x295070ef.
Lemma F_5e8c0 : fetch_word AsanUbsan.M.loaded_segments (0x5e8c0 : word) = Some W_5e8c0.
Proof. vm_refl. Qed.
Lemma D_5e8c0 : decode_any W_5e8c0 = Some (Jal 1 31380, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8c4 : bv 32 := 0x00098593.
Lemma F_5e8c4 : fetch_word AsanUbsan.M.loaded_segments (0x5e8c4 : word) = Some W_5e8c4.
Proof. vm_refl. Qed.
Lemma D_5e8c4 : decode_any W_5e8c4 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8c8 : bv 32 := 0x00090613.
Lemma F_5e8c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e8c8 : word) = Some W_5e8c8.
Proof. vm_refl. Qed.
Lemma D_5e8c8 : decode_any W_5e8c8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8cc : bv 32 := 0x00050693.
Lemma F_5e8cc : fetch_word AsanUbsan.M.loaded_segments (0x5e8cc : word) = Some W_5e8cc.
Proof. vm_refl. Qed.
Lemma D_5e8cc : decode_any W_5e8cc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8d0 : bv 32 := 0x00048513.
Lemma F_5e8d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e8d0 : word) = Some W_5e8d0.
Proof. vm_refl. Qed.
Lemma D_5e8d0 : decode_any W_5e8d0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8d4 : bv 32 := 0xfa0696e3.
Lemma F_5e8d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e8d4 : word) = Some W_5e8d4.
Proof. vm_refl. Qed.
Lemma D_5e8d4 : decode_any W_5e8d4 = Some (Branch BC_NE 13 0 8108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8d8 : bv 32 := 0x06010113.
Lemma F_5e8d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e8d8 : word) = Some W_5e8d8.
Proof. vm_refl. Qed.
Lemma D_5e8d8 : decode_any W_5e8d8 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8dc : bv 32 := 0x7e813083.
Lemma F_5e8dc : fetch_word AsanUbsan.M.loaded_segments (0x5e8dc : word) = Some W_5e8dc.
Proof. vm_refl. Qed.
Lemma D_5e8dc : decode_any W_5e8dc = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8e0 : bv 32 := 0x7e013403.
Lemma F_5e8e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e8e0 : word) = Some W_5e8e0.
Proof. vm_refl. Qed.
Lemma D_5e8e0 : decode_any W_5e8e0 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8e4 : bv 32 := 0x7d813483.
Lemma F_5e8e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e8e4 : word) = Some W_5e8e4.
Proof. vm_refl. Qed.
Lemma D_5e8e4 : decode_any W_5e8e4 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8e8 : bv 32 := 0x7d013903.
Lemma F_5e8e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e8e8 : word) = Some W_5e8e8.
Proof. vm_refl. Qed.
Lemma D_5e8e8 : decode_any W_5e8e8 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8ec : bv 32 := 0x7c813983.
Lemma F_5e8ec : fetch_word AsanUbsan.M.loaded_segments (0x5e8ec : word) = Some W_5e8ec.
Proof. vm_refl. Qed.
Lemma D_5e8ec : decode_any W_5e8ec = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8f0 : bv 32 := 0x7c013a03.
Lemma F_5e8f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e8f0 : word) = Some W_5e8f0.
Proof. vm_refl. Qed.
Lemma D_5e8f0 : decode_any W_5e8f0 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8f4 : bv 32 := 0x7b813a83.
Lemma F_5e8f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e8f4 : word) = Some W_5e8f4.
Proof. vm_refl. Qed.
Lemma D_5e8f4 : decode_any W_5e8f4 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8f8 : bv 32 := 0x7f010113.
Lemma F_5e8f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e8f8 : word) = Some W_5e8f8.
Proof. vm_refl. Qed.
Lemma D_5e8f8 : decode_any W_5e8f8 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8fc : bv 32 := 0x4e51206f.
Lemma F_5e8fc : fetch_word AsanUbsan.M.loaded_segments (0x5e8fc : word) = Some W_5e8fc.
Proof. vm_refl. Qed.
Lemma D_5e8fc : decode_any W_5e8fc = Some (Jal 0 77028, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e900 : bv 32 := 0x80040693.
Lemma F_5e900 : fetch_word AsanUbsan.M.loaded_segments (0x5e900 : word) = Some W_5e900.
Proof. vm_refl. Qed.
Lemma D_5e900 : decode_any W_5e900 = Some (OpImm ALU_ADD 13 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e904 : bv 32 := 0xfc068693.
Lemma F_5e904 : fetch_word AsanUbsan.M.loaded_segments (0x5e904 : word) = Some W_5e904.
Proof. vm_refl. Qed.
Lemma D_5e904 : decode_any W_5e904 = Some (OpImm ALU_ADD 13 13 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e908 : bv 32 := 0x80040713.
Lemma F_5e908 : fetch_word AsanUbsan.M.loaded_segments (0x5e908 : word) = Some W_5e908.
Proof. vm_refl. Qed.
Lemma D_5e908 : decode_any W_5e908 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e90c : bv 32 := 0xfb070713.
Lemma F_5e90c : fetch_word AsanUbsan.M.loaded_segments (0x5e90c : word) = Some W_5e90c.
Proof. vm_refl. Qed.
Lemma D_5e90c : decode_any W_5e90c = Some (OpImm ALU_ADD 14 14 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e910 : bv 32 := 0x7ff70a93.
Lemma F_5e910 : fetch_word AsanUbsan.M.loaded_segments (0x5e910 : word) = Some W_5e910.
Proof. vm_refl. Qed.
Lemma D_5e910 : decode_any W_5e910 = Some (OpImm ALU_ADD 21 14 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e914 : bv 32 := 0x000ab4a3.
Lemma F_5e914 : fetch_word AsanUbsan.M.loaded_segments (0x5e914 : word) = Some W_5e914.
Proof. vm_refl. Qed.
Lemma D_5e914 : decode_any W_5e914 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e918 : bv 32 := 0x00da3023.
Lemma F_5e918 : fetch_word AsanUbsan.M.loaded_segments (0x5e918 : word) = Some W_5e918.
Proof. vm_refl. Qed.
Lemma D_5e918 : decode_any W_5e918 = Some (Store SZ8 20 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e91c : bv 32 := 0x000a3423.
Lemma F_5e91c : fetch_word AsanUbsan.M.loaded_segments (0x5e91c : word) = Some W_5e91c.
Proof. vm_refl. Qed.
Lemma D_5e91c : decode_any W_5e91c = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e920 : bv 32 := 0x00060493.
Lemma F_5e920 : fetch_word AsanUbsan.M.loaded_segments (0x5e920 : word) = Some W_5e920.
Proof. vm_refl. Qed.
Lemma D_5e920 : decode_any W_5e920 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e924 : bv 32 := 0x00058993.
Lemma F_5e924 : fetch_word AsanUbsan.M.loaded_segments (0x5e924 : word) = Some W_5e924.
Proof. vm_refl. Qed.
Lemma D_5e924 : decode_any W_5e924 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e928 : bv 32 := 0x00050913.
Lemma F_5e928 : fetch_word AsanUbsan.M.loaded_segments (0x5e928 : word) = Some W_5e928.
Proof. vm_refl. Qed.
Lemma D_5e928 : decode_any W_5e928 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e92c : bv 32 := 0x180220ef.
Lemma F_5e92c : fetch_word AsanUbsan.M.loaded_segments (0x5e92c : word) = Some W_5e92c.
Proof. vm_refl. Qed.
Lemma D_5e92c : decode_any W_5e92c = Some (Jal 1 139648, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e930 : bv 32 := 0x00050593.
Lemma F_5e930 : fetch_word AsanUbsan.M.loaded_segments (0x5e930 : word) = Some W_5e930.
Proof. vm_refl. Qed.
Lemma D_5e930 : decode_any W_5e930 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e934 : bv 32 := 0x00078517.
Lemma F_5e934 : fetch_word AsanUbsan.M.loaded_segments (0x5e934 : word) = Some W_5e934.
Proof. vm_refl. Qed.
Lemma D_5e934 : decode_any W_5e934 = Some (Auipc 10 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e938 : bv 32 := 0xb8453503.
Lemma F_5e938 : fetch_word AsanUbsan.M.loaded_segments (0x5e938 : word) = Some W_5e938.
Proof. vm_refl. Qed.
Lemma D_5e938 : decode_any W_5e938 = Some (Load SZ8 true 10 10 2948, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e93c : bv 32 := 0x02154703.
Lemma F_5e93c : fetch_word AsanUbsan.M.loaded_segments (0x5e93c : word) = Some W_5e93c.
Proof. vm_refl. Qed.
Lemma D_5e93c : decode_any W_5e93c = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e940 : bv 32 := 0x008ab4a3.
Lemma F_5e940 : fetch_word AsanUbsan.M.loaded_segments (0x5e940 : word) = Some W_5e940.
Proof. vm_refl. Qed.
Lemma D_5e940 : decode_any W_5e940 = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e944 : bv 32 := 0x80040513.
Lemma F_5e944 : fetch_word AsanUbsan.M.loaded_segments (0x5e944 : word) = Some W_5e944.
Proof. vm_refl. Qed.
Lemma D_5e944 : decode_any W_5e944 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e948 : bv 32 := 0xfb050513.
Lemma F_5e948 : fetch_word AsanUbsan.M.loaded_segments (0x5e948 : word) = Some W_5e948.
Proof. vm_refl. Qed.
Lemma D_5e948 : decode_any W_5e948 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e94c : bv 32 := 0x0ff00793.
Lemma F_5e94c : fetch_word AsanUbsan.M.loaded_segments (0x5e94c : word) = Some W_5e94c.
Proof. vm_refl. Qed.
Lemma D_5e94c : decode_any W_5e94c = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e950 : bv 32 := 0x00040613.
Lemma F_5e950 : fetch_word AsanUbsan.M.loaded_segments (0x5e950 : word) = Some W_5e950.
Proof. vm_refl. Qed.
Lemma D_5e950 : decode_any W_5e950 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e954 : bv 32 := 0x00000693.
Lemma F_5e954 : fetch_word AsanUbsan.M.loaded_segments (0x5e954 : word) = Some W_5e954.
Proof. vm_refl. Qed.
Lemma D_5e954 : decode_any W_5e954 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e958 : bv 32 := 0x6a4090ef.
Lemma F_5e958 : fetch_word AsanUbsan.M.loaded_segments (0x5e958 : word) = Some W_5e958.
Proof. vm_refl. Qed.
Lemma D_5e958 : decode_any W_5e958 = Some (Jal 1 38564, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e95c : bv 32 := 0x80040613.
Lemma F_5e95c : fetch_word AsanUbsan.M.loaded_segments (0x5e95c : word) = Some W_5e95c.
Proof. vm_refl. Qed.
Lemma D_5e95c : decode_any W_5e95c = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e960 : bv 32 := 0xfb060613.
Lemma F_5e960 : fetch_word AsanUbsan.M.loaded_segments (0x5e960 : word) = Some W_5e960.
Proof. vm_refl. Qed.
Lemma D_5e960 : decode_any W_5e960 = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e964 : bv 32 := 0x00090513.
Lemma F_5e964 : fetch_word AsanUbsan.M.loaded_segments (0x5e964 : word) = Some W_5e964.
Proof. vm_refl. Qed.
Lemma D_5e964 : decode_any W_5e964 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e968 : bv 32 := 0x00048593.
Lemma F_5e968 : fetch_word AsanUbsan.M.loaded_segments (0x5e968 : word) = Some W_5e968.
Proof. vm_refl. Qed.
Lemma D_5e968 : decode_any W_5e968 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e96c : bv 32 := 0x448060ef.
Lemma F_5e96c : fetch_word AsanUbsan.M.loaded_segments (0x5e96c : word) = Some W_5e96c.
Proof. vm_refl. Qed.
Lemma D_5e96c : decode_any W_5e96c = Some (Jal 1 25672, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e970 : bv 32 := 0x00090513.
Lemma F_5e970 : fetch_word AsanUbsan.M.loaded_segments (0x5e970 : word) = Some W_5e970.
Proof. vm_refl. Qed.
Lemma D_5e970 : decode_any W_5e970 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e974 : bv 32 := 0x00098593.
Lemma F_5e974 : fetch_word AsanUbsan.M.loaded_segments (0x5e974 : word) = Some W_5e974.
Proof. vm_refl. Qed.
Lemma D_5e974 : decode_any W_5e974 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e978 : bv 32 := 0x00048613.
Lemma F_5e978 : fetch_word AsanUbsan.M.loaded_segments (0x5e978 : word) = Some W_5e978.
Proof. vm_refl. Qed.
Lemma D_5e978 : decode_any W_5e978 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e97c : bv 32 := 0xfbf48693.
Lemma F_5e97c : fetch_word AsanUbsan.M.loaded_segments (0x5e97c : word) = Some W_5e97c.
Proof. vm_refl. Qed.
Lemma D_5e97c : decode_any W_5e97c = Some (OpImm ALU_ADD 13 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e980 : bv 32 := 0xfbf00713.
Lemma F_5e980 : fetch_word AsanUbsan.M.loaded_segments (0x5e980 : word) = Some W_5e980.
Proof. vm_refl. Qed.
Lemma D_5e980 : decode_any W_5e980 = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e984 : bv 32 := 0xecd760e3.
Lemma F_5e984 : fetch_word AsanUbsan.M.loaded_segments (0x5e984 : word) = Some W_5e984.
Proof. vm_refl. Qed.
Lemma D_5e984 : decode_any W_5e984 = Some (Branch BC_LTU 14 13 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e988 : bv 32 := 0x02061e63.
Lemma F_5e988 : fetch_word AsanUbsan.M.loaded_segments (0x5e988 : word) = Some W_5e988.
Proof. vm_refl. Qed.
Lemma D_5e988 : decode_any W_5e988 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e98c : bv 32 := 0xef5ff06f.
Lemma F_5e98c : fetch_word AsanUbsan.M.loaded_segments (0x5e98c : word) = Some W_5e98c.
Proof. vm_refl. Qed.
Lemma D_5e98c : decode_any W_5e98c = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e990 : bv 32 := 0x00070803.
Lemma F_5e990 : fetch_word AsanUbsan.M.loaded_segments (0x5e990 : word) = Some W_5e990.
Proof. vm_refl. Qed.
Lemma D_5e990 : decode_any W_5e990 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e994 : bv 32 := 0x0077f793.
Lemma F_5e994 : fetch_word AsanUbsan.M.loaded_segments (0x5e994 : word) = Some W_5e994.
Proof. vm_refl. Qed.
Lemma D_5e994 : decode_any W_5e994 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e998 : bv 32 := 0x010038b3.
Lemma F_5e998 : fetch_word AsanUbsan.M.loaded_segments (0x5e998 : word) = Some W_5e998.
Proof. vm_refl. Qed.
Lemma D_5e998 : decode_any W_5e998 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e99c : bv 32 := 0x0107a7b3.
Lemma F_5e99c : fetch_word AsanUbsan.M.loaded_segments (0x5e99c : word) = Some W_5e99c.
Proof. vm_refl. Qed.
Lemma D_5e99c : decode_any W_5e99c = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9a0 : bv 32 := 0x0017c793.
Lemma F_5e9a0 : fetch_word AsanUbsan.M.loaded_segments (0x5e9a0 : word) = Some W_5e9a0.
Proof. vm_refl. Qed.
Lemma D_5e9a0 : decode_any W_5e9a0 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9a4 : bv 32 := 0x00f8f7b3.
Lemma F_5e9a4 : fetch_word AsanUbsan.M.loaded_segments (0x5e9a4 : word) = Some W_5e9a4.
Proof. vm_refl. Qed.
Lemma D_5e9a4 : decode_any W_5e9a4 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9a8 : bv 32 := 0x00e6fa63.
Lemma F_5e9a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e9a8 : word) = Some W_5e9a8.
Proof. vm_refl. Qed.
Lemma D_5e9a8 : decode_any W_5e9a8 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9ac : bv 32 := 0x0006c803.
Lemma F_5e9ac : fetch_word AsanUbsan.M.loaded_segments (0x5e9ac : word) = Some W_5e9ac.
Proof. vm_refl. Qed.
Lemma D_5e9ac : decode_any W_5e9ac = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9b0 : bv 32 := 0x00168693.
Lemma F_5e9b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e9b0 : word) = Some W_5e9b0.
Proof. vm_refl. Qed.
Lemma D_5e9b0 : decode_any W_5e9b0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9b4 : bv 32 := 0x00f867b3.
Lemma F_5e9b4 : fetch_word AsanUbsan.M.loaded_segments (0x5e9b4 : word) = Some W_5e9b4.
Proof. vm_refl. Qed.
Lemma D_5e9b4 : decode_any W_5e9b4 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9b8 : bv 32 := 0xfee69ae3.
Lemma F_5e9b8 : fetch_word AsanUbsan.M.loaded_segments (0x5e9b8 : word) = Some W_5e9b8.
Proof. vm_refl. Qed.
Lemma D_5e9b8 : decode_any W_5e9b8 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9bc : bv 32 := 0x0ff7f693.
Lemma F_5e9bc : fetch_word AsanUbsan.M.loaded_segments (0x5e9bc : word) = Some W_5e9bc.
Proof. vm_refl. Qed.
Lemma D_5e9bc : decode_any W_5e9bc = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9c0 : bv 32 := 0xec0680e3.
Lemma F_5e9c0 : fetch_word AsanUbsan.M.loaded_segments (0x5e9c0 : word) = Some W_5e9c0.
Proof. vm_refl. Qed.
Lemma D_5e9c0 : decode_any W_5e9c0 = Some (Branch BC_EQ 13 0 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9c4 : bv 32 := 0x00050493.
Lemma F_5e9c4 : fetch_word AsanUbsan.M.loaded_segments (0x5e9c4 : word) = Some W_5e9c4.
Proof. vm_refl. Qed.
Lemma D_5e9c4 : decode_any W_5e9c4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9c8 : bv 32 := 0x00058a93.
Lemma F_5e9c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e9c8 : word) = Some W_5e9c8.
Proof. vm_refl. Qed.
Lemma D_5e9c8 : decode_any W_5e9c8 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9cc : bv 32 := 0x00060593.
Lemma F_5e9cc : fetch_word AsanUbsan.M.loaded_segments (0x5e9cc : word) = Some W_5e9cc.
Proof. vm_refl. Qed.
Lemma D_5e9cc : decode_any W_5e9cc = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9d0 : bv 32 := 0x00060913.
Lemma F_5e9d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e9d0 : word) = Some W_5e9d0.
Proof. vm_refl. Qed.
Lemma D_5e9d0 : decode_any W_5e9d0 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9d4 : bv 32 := 0x1ac030ef.
Lemma F_5e9d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e9d4 : word) = Some W_5e9d4.
Proof. vm_refl. Qed.
Lemma D_5e9d4 : decode_any W_5e9d4 = Some (Jal 1 12716, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9d8 : bv 32 := 0x000a8593.
Lemma F_5e9d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e9d8 : word) = Some W_5e9d8.
Proof. vm_refl. Qed.
Lemma D_5e9d8 : decode_any W_5e9d8 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9dc : bv 32 := 0x00090613.
Lemma F_5e9dc : fetch_word AsanUbsan.M.loaded_segments (0x5e9dc : word) = Some W_5e9dc.
Proof. vm_refl. Qed.
Lemma D_5e9dc : decode_any W_5e9dc = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9e0 : bv 32 := 0x00050993.
Lemma F_5e9e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e9e0 : word) = Some W_5e9e0.
Proof. vm_refl. Qed.
Lemma D_5e9e0 : decode_any W_5e9e0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9e4 : bv 32 := 0x00048513.
Lemma F_5e9e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e9e4 : word) = Some W_5e9e4.
Proof. vm_refl. Qed.
Lemma D_5e9e4 : decode_any W_5e9e4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9e8 : bv 32 := 0xe8098ce3.
Lemma F_5e9e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e9e8 : word) = Some W_5e9e8.
Proof. vm_refl. Qed.
Lemma D_5e9e8 : decode_any W_5e9e8 = Some (Branch BC_EQ 19 0 7832, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9ec : bv 32 := 0x0c0220ef.
Lemma F_5e9ec : fetch_word AsanUbsan.M.loaded_segments (0x5e9ec : word) = Some W_5e9ec.
Proof. vm_refl. Qed.
Lemma D_5e9ec : decode_any W_5e9ec = Some (Jal 1 139456, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9f0 : bv 32 := 0xfffb2597.
Lemma F_5e9f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e9f0 : word) = Some W_5e9f0.
Proof. vm_refl. Qed.
Lemma D_5e9f0 : decode_any W_5e9f0 = Some (Auipc 11 1048498, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9f4 : bv 32 := 0xa185b583.
Lemma F_5e9f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e9f4 : word) = Some W_5e9f4.
Proof. vm_refl. Qed.
Lemma D_5e9f4 : decode_any W_5e9f4 = Some (Load SZ8 true 11 11 2584, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9f8 : bv 32 := 0x00ba3023.
Lemma F_5e9f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e9f8 : word) = Some W_5e9f8.
Proof. vm_refl. Qed.
Lemma D_5e9f8 : decode_any W_5e9f8 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9fc : bv 32 := 0x80040613.
Lemma F_5e9fc : fetch_word AsanUbsan.M.loaded_segments (0x5e9fc : word) = Some W_5e9fc.
Proof. vm_refl. Qed.
Lemma D_5e9fc : decode_any W_5e9fc = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea00 : bv 32 := 0xfb060613.
Lemma F_5ea00 : fetch_word AsanUbsan.M.loaded_segments (0x5ea00 : word) = Some W_5ea00.
Proof. vm_refl. Qed.
Lemma D_5ea00 : decode_any W_5ea00 = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea04 : bv 32 := 0x00100713.
Lemma F_5ea04 : fetch_word AsanUbsan.M.loaded_segments (0x5ea04 : word) = Some W_5ea04.
Proof. vm_refl. Qed.
Lemma D_5ea04 : decode_any W_5ea04 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea08 : bv 32 := 0x00040593.
Lemma F_5ea08 : fetch_word AsanUbsan.M.loaded_segments (0x5ea08 : word) = Some W_5ea08.
Proof. vm_refl. Qed.
Lemma D_5ea08 : decode_any W_5ea08 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea0c : bv 32 := 0x00098693.
Lemma F_5ea0c : fetch_word AsanUbsan.M.loaded_segments (0x5ea0c : word) = Some W_5ea0c.
Proof. vm_refl. Qed.
Lemma D_5ea0c : decode_any W_5ea0c = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea10 : bv 32 := 0x00090793.
Lemma F_5ea10 : fetch_word AsanUbsan.M.loaded_segments (0x5ea10 : word) = Some W_5ea10.
Proof. vm_refl. Qed.
Lemma D_5ea10 : decode_any W_5ea10 = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea14 : bv 32 := 0x00000813.
Lemma F_5ea14 : fetch_word AsanUbsan.M.loaded_segments (0x5ea14 : word) = Some W_5ea14.
Proof. vm_refl. Qed.
Lemma D_5ea14 : decode_any W_5ea14 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea18 : bv 32 := 0x00000893.
Lemma F_5ea18 : fetch_word AsanUbsan.M.loaded_segments (0x5ea18 : word) = Some W_5ea18.
Proof. vm_refl. Qed.
Lemma D_5ea18 : decode_any W_5ea18 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea1c : bv 32 := 0x0f1060ef.
Lemma F_5ea1c : fetch_word AsanUbsan.M.loaded_segments (0x5ea1c : word) = Some W_5ea1c.
Proof. vm_refl. Qed.
Lemma D_5ea1c : decode_any W_5ea1c = Some (Jal 1 26864, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea20 : bv 32 := 0x00048513.
Lemma F_5ea20 : fetch_word AsanUbsan.M.loaded_segments (0x5ea20 : word) = Some W_5ea20.
Proof. vm_refl. Qed.
Lemma D_5ea20 : decode_any W_5ea20 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea24 : bv 32 := 0x000a8593.
Lemma F_5ea24 : fetch_word AsanUbsan.M.loaded_segments (0x5ea24 : word) = Some W_5ea24.
Proof. vm_refl. Qed.
Lemma D_5ea24 : decode_any W_5ea24 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea28 : bv 32 := 0x00090613.
Lemma F_5ea28 : fetch_word AsanUbsan.M.loaded_segments (0x5ea28 : word) = Some W_5ea28.
Proof. vm_refl. Qed.
Lemma D_5ea28 : decode_any W_5ea28 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea2c : bv 32 := 0xe55ff06f.
Lemma F_5ea2c : fetch_word AsanUbsan.M.loaded_segments (0x5ea2c : word) = Some W_5ea2c.
Proof. vm_refl. Qed.
Lemma D_5ea2c : decode_any W_5ea2c = Some (Jal 0 2096724, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea30 : bv 32 := 0x81010113.
Lemma F_5ea30 : fetch_word AsanUbsan.M.loaded_segments (0x5ea30 : word) = Some W_5ea30.
Proof. vm_refl. Qed.
Lemma D_5ea30 : decode_any W_5ea30 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea34 : bv 32 := 0x7e113423.
Lemma F_5ea34 : fetch_word AsanUbsan.M.loaded_segments (0x5ea34 : word) = Some W_5ea34.
Proof. vm_refl. Qed.
Lemma D_5ea34 : decode_any W_5ea34 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea38 : bv 32 := 0x7e813023.
Lemma F_5ea38 : fetch_word AsanUbsan.M.loaded_segments (0x5ea38 : word) = Some W_5ea38.
Proof. vm_refl. Qed.
Lemma D_5ea38 : decode_any W_5ea38 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea3c : bv 32 := 0x7c913c23.
Lemma F_5ea3c : fetch_word AsanUbsan.M.loaded_segments (0x5ea3c : word) = Some W_5ea3c.
Proof. vm_refl. Qed.
Lemma D_5ea3c : decode_any W_5ea3c = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea40 : bv 32 := 0x7d213823.
Lemma F_5ea40 : fetch_word AsanUbsan.M.loaded_segments (0x5ea40 : word) = Some W_5ea40.
Proof. vm_refl. Qed.
Lemma D_5ea40 : decode_any W_5ea40 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea44 : bv 32 := 0x7d313423.
Lemma F_5ea44 : fetch_word AsanUbsan.M.loaded_segments (0x5ea44 : word) = Some W_5ea44.
Proof. vm_refl. Qed.
Lemma D_5ea44 : decode_any W_5ea44 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea48 : bv 32 := 0x7d413023.
Lemma F_5ea48 : fetch_word AsanUbsan.M.loaded_segments (0x5ea48 : word) = Some W_5ea48.
Proof. vm_refl. Qed.
Lemma D_5ea48 : decode_any W_5ea48 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea4c : bv 32 := 0x7b513c23.
Lemma F_5ea4c : fetch_word AsanUbsan.M.loaded_segments (0x5ea4c : word) = Some W_5ea4c.
Proof. vm_refl. Qed.
Lemma D_5ea4c : decode_any W_5ea4c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea50 : bv 32 := 0x7b613823.
Lemma F_5ea50 : fetch_word AsanUbsan.M.loaded_segments (0x5ea50 : word) = Some W_5ea50.
Proof. vm_refl. Qed.
Lemma D_5ea50 : decode_any W_5ea50 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea54 : bv 32 := 0x7f010413.
Lemma F_5ea54 : fetch_word AsanUbsan.M.loaded_segments (0x5ea54 : word) = Some W_5ea54.
Proof. vm_refl. Qed.
Lemma D_5ea54 : decode_any W_5ea54 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea58 : bv 32 := 0xf9010113.
Lemma F_5ea58 : fetch_word AsanUbsan.M.loaded_segments (0x5ea58 : word) = Some W_5ea58.
Proof. vm_refl. Qed.
Lemma D_5ea58 : decode_any W_5ea58 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea5c : bv 32 := 0x00078697.
Lemma F_5ea5c : fetch_word AsanUbsan.M.loaded_segments (0x5ea5c : word) = Some W_5ea5c.
Proof. vm_refl. Qed.
Lemma D_5ea5c : decode_any W_5ea5c = Some (Auipc 13 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea60 : bv 32 := 0x5d46b683.
Lemma F_5ea60 : fetch_word AsanUbsan.M.loaded_segments (0x5ea60 : word) = Some W_5ea60.
Proof. vm_refl. Qed.
Lemma D_5ea60 : decode_any W_5ea60 = Some (Load SZ8 true 13 13 1492, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea64 : bv 32 := 0x0006c683.
Lemma F_5ea64 : fetch_word AsanUbsan.M.loaded_segments (0x5ea64 : word) = Some W_5ea64.
Proof. vm_refl. Qed.
Lemma D_5ea64 : decode_any W_5ea64 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea68 : bv 32 := 0x0a068463.
Lemma F_5ea68 : fetch_word AsanUbsan.M.loaded_segments (0x5ea68 : word) = Some W_5ea68.
Proof. vm_refl. Qed.
Lemma D_5ea68 : decode_any W_5ea68 = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea6c : bv 32 := 0xfff5c693.
Lemma F_5ea6c : fetch_word AsanUbsan.M.loaded_segments (0x5ea6c : word) = Some W_5ea6c.
Proof. vm_refl. Qed.
Lemma D_5ea6c : decode_any W_5ea6c = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea70 : bv 32 := 0x80040a13.
Lemma F_5ea70 : fetch_word AsanUbsan.M.loaded_segments (0x5ea70 : word) = Some W_5ea70.
Proof. vm_refl. Qed.
Lemma D_5ea70 : decode_any W_5ea70 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea74 : bv 32 := 0xfa8a0a13.
Lemma F_5ea74 : fetch_word AsanUbsan.M.loaded_segments (0x5ea74 : word) = Some W_5ea74.
Proof. vm_refl. Qed.
Lemma D_5ea74 : decode_any W_5ea74 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea78 : bv 32 := 0x0cc6e463.
Lemma F_5ea78 : fetch_word AsanUbsan.M.loaded_segments (0x5ea78 : word) = Some W_5ea78.
Proof. vm_refl. Qed.
Lemma D_5ea78 : decode_any W_5ea78 = Some (Branch BC_LTU 13 12 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea7c : bv 32 := 0xfbf60993.
Lemma F_5ea7c : fetch_word AsanUbsan.M.loaded_segments (0x5ea7c : word) = Some W_5ea7c.
Proof. vm_refl. Qed.
Lemma D_5ea7c : decode_any W_5ea7c = Some (OpImm ALU_ADD 19 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea80 : bv 32 := 0xfbf00693.
Lemma F_5ea80 : fetch_word AsanUbsan.M.loaded_segments (0x5ea80 : word) = Some W_5ea80.
Proof. vm_refl. Qed.
Lemma D_5ea80 : decode_any W_5ea80 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea84 : bv 32 := 0x1536f263.
Lemma F_5ea84 : fetch_word AsanUbsan.M.loaded_segments (0x5ea84 : word) = Some W_5ea84.
Proof. vm_refl. Qed.
Lemma D_5ea84 : decode_any W_5ea84 = Some (Branch BC_GEU 13 19 324, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea88 : bv 32 := 0x00078697.
Lemma F_5ea88 : fetch_word AsanUbsan.M.loaded_segments (0x5ea88 : word) = Some W_5ea88.
Proof. vm_refl. Qed.
Lemma D_5ea88 : decode_any W_5ea88 = Some (Auipc 13 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea8c : bv 32 := 0xa406b683.
Lemma F_5ea8c : fetch_word AsanUbsan.M.loaded_segments (0x5ea8c : word) = Some W_5ea8c.
Proof. vm_refl. Qed.
Lemma D_5ea8c : decode_any W_5ea8c = Some (Load SZ8 true 13 13 2624, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea90 : bv 32 := 0x00c587b3.
Lemma F_5ea90 : fetch_word AsanUbsan.M.loaded_segments (0x5ea90 : word) = Some W_5ea90.
Proof. vm_refl. Qed.
Lemma D_5ea90 : decode_any W_5ea90 = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea94 : bv 32 := 0x0006b703.
Lemma F_5ea94 : fetch_word AsanUbsan.M.loaded_segments (0x5ea94 : word) = Some W_5ea94.
Proof. vm_refl. Qed.
Lemma D_5ea94 : decode_any W_5ea94 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea98 : bv 32 := 0x0035d693.
Lemma F_5ea98 : fetch_word AsanUbsan.M.loaded_segments (0x5ea98 : word) = Some W_5ea98.
Proof. vm_refl. Qed.
Lemma D_5ea98 : decode_any W_5ea98 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea9c : bv 32 := 0xfff78793.
Lemma F_5ea9c : fetch_word AsanUbsan.M.loaded_segments (0x5ea9c : word) = Some W_5ea9c.
Proof. vm_refl. Qed.
Lemma D_5ea9c : decode_any W_5ea9c = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaa0 : bv 32 := 0x0037d813.
Lemma F_5eaa0 : fetch_word AsanUbsan.M.loaded_segments (0x5eaa0 : word) = Some W_5eaa0.
Proof. vm_refl. Qed.
Lemma D_5eaa0 : decode_any W_5eaa0 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaa4 : bv 32 := 0x00d706b3.
Lemma F_5eaa4 : fetch_word AsanUbsan.M.loaded_segments (0x5eaa4 : word) = Some W_5eaa4.
Proof. vm_refl. Qed.
Lemma D_5eaa4 : decode_any W_5eaa4 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaa8 : bv 32 := 0x01070733.
Lemma F_5eaa8 : fetch_word AsanUbsan.M.loaded_segments (0x5eaa8 : word) = Some W_5eaa8.
Proof. vm_refl. Qed.
Lemma D_5eaa8 : decode_any W_5eaa8 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaac : bv 32 := 0xff86f813.
Lemma F_5eaac : fetch_word AsanUbsan.M.loaded_segments (0x5eaac : word) = Some W_5eaac.
Proof. vm_refl. Qed.
Lemma D_5eaac : decode_any W_5eaac = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eab0 : bv 32 := 0xff877893.
Lemma F_5eab0 : fetch_word AsanUbsan.M.loaded_segments (0x5eab0 : word) = Some W_5eab0.
Proof. vm_refl. Qed.
Lemma D_5eab0 : decode_any W_5eab0 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eab4 : bv 32 := 0x00083803.
Lemma F_5eab4 : fetch_word AsanUbsan.M.loaded_segments (0x5eab4 : word) = Some W_5eab4.
Proof. vm_refl. Qed.
Lemma D_5eab4 : decode_any W_5eab4 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eab8 : bv 32 := 0x0008b883.
Lemma F_5eab8 : fetch_word AsanUbsan.M.loaded_segments (0x5eab8 : word) = Some W_5eab8.
Proof. vm_refl. Qed.
Lemma D_5eab8 : decode_any W_5eab8 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eabc : bv 32 := 0x0108e833.
Lemma F_5eabc : fetch_word AsanUbsan.M.loaded_segments (0x5eabc : word) = Some W_5eabc.
Proof. vm_refl. Qed.
Lemma D_5eabc : decode_any W_5eabc = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eac0 : bv 32 := 0x18081e63.
Lemma F_5eac0 : fetch_word AsanUbsan.M.loaded_segments (0x5eac0 : word) = Some W_5eac0.
Proof. vm_refl. Qed.
Lemma D_5eac0 : decode_any W_5eac0 = Some (Branch BC_NE 16 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eac4 : bv 32 := 0xfff54693.
Lemma F_5eac4 : fetch_word AsanUbsan.M.loaded_segments (0x5eac4 : word) = Some W_5eac4.
Proof. vm_refl. Qed.
Lemma D_5eac4 : decode_any W_5eac4 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eac8 : bv 32 := 0x10c6e463.
Lemma F_5eac8 : fetch_word AsanUbsan.M.loaded_segments (0x5eac8 : word) = Some W_5eac8.
Proof. vm_refl. Qed.
Lemma D_5eac8 : decode_any W_5eac8 = Some (Branch BC_LTU 13 12 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eacc : bv 32 := 0xfbf00693.
Lemma F_5eacc : fetch_word AsanUbsan.M.loaded_segments (0x5eacc : word) = Some W_5eacc.
Proof. vm_refl. Qed.
Lemma D_5eacc : decode_any W_5eacc = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ead0 : bv 32 := 0x1936f263.
Lemma F_5ead0 : fetch_word AsanUbsan.M.loaded_segments (0x5ead0 : word) = Some W_5ead0.
Proof. vm_refl. Qed.
Lemma D_5ead0 : decode_any W_5ead0 = Some (Branch BC_GEU 13 19 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ead4 : bv 32 := 0x00078697.
Lemma F_5ead4 : fetch_word AsanUbsan.M.loaded_segments (0x5ead4 : word) = Some W_5ead4.
Proof. vm_refl. Qed.
Lemma D_5ead4 : decode_any W_5ead4 = Some (Auipc 13 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ead8 : bv 32 := 0x9f46b683.
Lemma F_5ead8 : fetch_word AsanUbsan.M.loaded_segments (0x5ead8 : word) = Some W_5ead8.
Proof. vm_refl. Qed.
Lemma D_5ead8 : decode_any W_5ead8 = Some (Load SZ8 true 13 13 2548, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eadc : bv 32 := 0x00c507b3.
Lemma F_5eadc : fetch_word AsanUbsan.M.loaded_segments (0x5eadc : word) = Some W_5eadc.
Proof. vm_refl. Qed.
Lemma D_5eadc : decode_any W_5eadc = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eae0 : bv 32 := 0x0006b703.
Lemma F_5eae0 : fetch_word AsanUbsan.M.loaded_segments (0x5eae0 : word) = Some W_5eae0.
Proof. vm_refl. Qed.
Lemma D_5eae0 : decode_any W_5eae0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eae4 : bv 32 := 0x00355693.
Lemma F_5eae4 : fetch_word AsanUbsan.M.loaded_segments (0x5eae4 : word) = Some W_5eae4.
Proof. vm_refl. Qed.
Lemma D_5eae4 : decode_any W_5eae4 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eae8 : bv 32 := 0xfff78793.
Lemma F_5eae8 : fetch_word AsanUbsan.M.loaded_segments (0x5eae8 : word) = Some W_5eae8.
Proof. vm_refl. Qed.
Lemma D_5eae8 : decode_any W_5eae8 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaec : bv 32 := 0x0037d813.
Lemma F_5eaec : fetch_word AsanUbsan.M.loaded_segments (0x5eaec : word) = Some W_5eaec.
Proof. vm_refl. Qed.
Lemma D_5eaec : decode_any W_5eaec = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaf0 : bv 32 := 0x00d706b3.
Lemma F_5eaf0 : fetch_word AsanUbsan.M.loaded_segments (0x5eaf0 : word) = Some W_5eaf0.
Proof. vm_refl. Qed.
Lemma D_5eaf0 : decode_any W_5eaf0 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaf4 : bv 32 := 0x01070733.
Lemma F_5eaf4 : fetch_word AsanUbsan.M.loaded_segments (0x5eaf4 : word) = Some W_5eaf4.
Proof. vm_refl. Qed.
Lemma D_5eaf4 : decode_any W_5eaf4 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaf8 : bv 32 := 0xff86f813.
Lemma F_5eaf8 : fetch_word AsanUbsan.M.loaded_segments (0x5eaf8 : word) = Some W_5eaf8.
Proof. vm_refl. Qed.
Lemma D_5eaf8 : decode_any W_5eaf8 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eafc : bv 32 := 0xff877893.
Lemma F_5eafc : fetch_word AsanUbsan.M.loaded_segments (0x5eafc : word) = Some W_5eafc.
Proof. vm_refl. Qed.
Lemma D_5eafc : decode_any W_5eafc = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb00 : bv 32 := 0x00083803.
Lemma F_5eb00 : fetch_word AsanUbsan.M.loaded_segments (0x5eb00 : word) = Some W_5eb00.
Proof. vm_refl. Qed.
Lemma D_5eb00 : decode_any W_5eb00 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb04 : bv 32 := 0x0008b883.
Lemma F_5eb04 : fetch_word AsanUbsan.M.loaded_segments (0x5eb04 : word) = Some W_5eb04.
Proof. vm_refl. Qed.
Lemma D_5eb04 : decode_any W_5eb04 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb08 : bv 32 := 0x0108e833.
Lemma F_5eb08 : fetch_word AsanUbsan.M.loaded_segments (0x5eb08 : word) = Some W_5eb08.
Proof. vm_refl. Qed.
Lemma D_5eb08 : decode_any W_5eb08 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb0c : bv 32 := 0x1e081a63.
Lemma F_5eb0c : fetch_word AsanUbsan.M.loaded_segments (0x5eb0c : word) = Some W_5eb0c.
Proof. vm_refl. Qed.
Lemma D_5eb0c : decode_any W_5eb0c = Some (Branch BC_NE 16 0 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb10 : bv 32 := 0x279120ef.
Lemma F_5eb10 : fetch_word AsanUbsan.M.loaded_segments (0x5eb10 : word) = Some W_5eb10.
Proof. vm_refl. Qed.
Lemma D_5eb10 : decode_any W_5eb10 = Some (Jal 1 76408, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb14 : bv 32 := 0x07010113.
Lemma F_5eb14 : fetch_word AsanUbsan.M.loaded_segments (0x5eb14 : word) = Some W_5eb14.
Proof. vm_refl. Qed.
Lemma D_5eb14 : decode_any W_5eb14 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb18 : bv 32 := 0x7e813083.
Lemma F_5eb18 : fetch_word AsanUbsan.M.loaded_segments (0x5eb18 : word) = Some W_5eb18.
Proof. vm_refl. Qed.
Lemma D_5eb18 : decode_any W_5eb18 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb1c : bv 32 := 0x7e013403.
Lemma F_5eb1c : fetch_word AsanUbsan.M.loaded_segments (0x5eb1c : word) = Some W_5eb1c.
Proof. vm_refl. Qed.
Lemma D_5eb1c : decode_any W_5eb1c = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb20 : bv 32 := 0x7d813483.
Lemma F_5eb20 : fetch_word AsanUbsan.M.loaded_segments (0x5eb20 : word) = Some W_5eb20.
Proof. vm_refl. Qed.
Lemma D_5eb20 : decode_any W_5eb20 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb24 : bv 32 := 0x7d013903.
Lemma F_5eb24 : fetch_word AsanUbsan.M.loaded_segments (0x5eb24 : word) = Some W_5eb24.
Proof. vm_refl. Qed.
Lemma D_5eb24 : decode_any W_5eb24 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb28 : bv 32 := 0x7c813983.
Lemma F_5eb28 : fetch_word AsanUbsan.M.loaded_segments (0x5eb28 : word) = Some W_5eb28.
Proof. vm_refl. Qed.
Lemma D_5eb28 : decode_any W_5eb28 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb2c : bv 32 := 0x7c013a03.
Lemma F_5eb2c : fetch_word AsanUbsan.M.loaded_segments (0x5eb2c : word) = Some W_5eb2c.
Proof. vm_refl. Qed.
Lemma D_5eb2c : decode_any W_5eb2c = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb30 : bv 32 := 0x7b813a83.
Lemma F_5eb30 : fetch_word AsanUbsan.M.loaded_segments (0x5eb30 : word) = Some W_5eb30.
Proof. vm_refl. Qed.
Lemma D_5eb30 : decode_any W_5eb30 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb34 : bv 32 := 0x7b013b03.
Lemma F_5eb34 : fetch_word AsanUbsan.M.loaded_segments (0x5eb34 : word) = Some W_5eb34.
Proof. vm_refl. Qed.
Lemma D_5eb34 : decode_any W_5eb34 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb38 : bv 32 := 0x7f010113.
Lemma F_5eb38 : fetch_word AsanUbsan.M.loaded_segments (0x5eb38 : word) = Some W_5eb38.
Proof. vm_refl. Qed.
Lemma D_5eb38 : decode_any W_5eb38 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb3c : bv 32 := 0x00008067.
Lemma F_5eb3c : fetch_word AsanUbsan.M.loaded_segments (0x5eb3c : word) = Some W_5eb3c.
Proof. vm_refl. Qed.
Lemma D_5eb3c : decode_any W_5eb3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb40 : bv 32 := 0x80040693.
Lemma F_5eb40 : fetch_word AsanUbsan.M.loaded_segments (0x5eb40 : word) = Some W_5eb40.
Proof. vm_refl. Qed.
Lemma D_5eb40 : decode_any W_5eb40 = Some (OpImm ALU_ADD 13 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb44 : bv 32 := 0xfb868693.
Lemma F_5eb44 : fetch_word AsanUbsan.M.loaded_segments (0x5eb44 : word) = Some W_5eb44.
Proof. vm_refl. Qed.
Lemma D_5eb44 : decode_any W_5eb44 = Some (OpImm ALU_ADD 13 13 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb48 : bv 32 := 0x80040713.
Lemma F_5eb48 : fetch_word AsanUbsan.M.loaded_segments (0x5eb48 : word) = Some W_5eb48.
Proof. vm_refl. Qed.
Lemma D_5eb48 : decode_any W_5eb48 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb4c : bv 32 := 0xfa870713.
Lemma F_5eb4c : fetch_word AsanUbsan.M.loaded_segments (0x5eb4c : word) = Some W_5eb4c.
Proof. vm_refl. Qed.
Lemma D_5eb4c : decode_any W_5eb4c = Some (OpImm ALU_ADD 14 14 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb50 : bv 32 := 0x7ff70a93.
Lemma F_5eb50 : fetch_word AsanUbsan.M.loaded_segments (0x5eb50 : word) = Some W_5eb50.
Proof. vm_refl. Qed.
Lemma D_5eb50 : decode_any W_5eb50 = Some (OpImm ALU_ADD 21 14 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb54 : bv 32 := 0x000ab4a3.
Lemma F_5eb54 : fetch_word AsanUbsan.M.loaded_segments (0x5eb54 : word) = Some W_5eb54.
Proof. vm_refl. Qed.
Lemma D_5eb54 : decode_any W_5eb54 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb58 : bv 32 := 0x00da3023.
Lemma F_5eb58 : fetch_word AsanUbsan.M.loaded_segments (0x5eb58 : word) = Some W_5eb58.
Proof. vm_refl. Qed.
Lemma D_5eb58 : decode_any W_5eb58 = Some (Store SZ8 20 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb5c : bv 32 := 0x000a3423.
Lemma F_5eb5c : fetch_word AsanUbsan.M.loaded_segments (0x5eb5c : word) = Some W_5eb5c.
Proof. vm_refl. Qed.
Lemma D_5eb5c : decode_any W_5eb5c = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb60 : bv 32 := 0x00060493.
Lemma F_5eb60 : fetch_word AsanUbsan.M.loaded_segments (0x5eb60 : word) = Some W_5eb60.
Proof. vm_refl. Qed.
Lemma D_5eb60 : decode_any W_5eb60 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb64 : bv 32 := 0x00058913.
Lemma F_5eb64 : fetch_word AsanUbsan.M.loaded_segments (0x5eb64 : word) = Some W_5eb64.
Proof. vm_refl. Qed.
Lemma D_5eb64 : decode_any W_5eb64 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb68 : bv 32 := 0x00050993.
Lemma F_5eb68 : fetch_word AsanUbsan.M.loaded_segments (0x5eb68 : word) = Some W_5eb68.
Proof. vm_refl. Qed.
Lemma D_5eb68 : decode_any W_5eb68 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb6c : bv 32 := 0x741210ef.
Lemma F_5eb6c : fetch_word AsanUbsan.M.loaded_segments (0x5eb6c : word) = Some W_5eb6c.
Proof. vm_refl. Qed.
Lemma D_5eb6c : decode_any W_5eb6c = Some (Jal 1 139072, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb70 : bv 32 := 0x00050593.
Lemma F_5eb70 : fetch_word AsanUbsan.M.loaded_segments (0x5eb70 : word) = Some W_5eb70.
Proof. vm_refl. Qed.
Lemma D_5eb70 : decode_any W_5eb70 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb74 : bv 32 := 0x00078517.
Lemma F_5eb74 : fetch_word AsanUbsan.M.loaded_segments (0x5eb74 : word) = Some W_5eb74.
Proof. vm_refl. Qed.
Lemma D_5eb74 : decode_any W_5eb74 = Some (Auipc 10 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb78 : bv 32 := 0x94453503.
Lemma F_5eb78 : fetch_word AsanUbsan.M.loaded_segments (0x5eb78 : word) = Some W_5eb78.
Proof. vm_refl. Qed.
Lemma D_5eb78 : decode_any W_5eb78 = Some (Load SZ8 true 10 10 2372, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb7c : bv 32 := 0x02154703.
Lemma F_5eb7c : fetch_word AsanUbsan.M.loaded_segments (0x5eb7c : word) = Some W_5eb7c.
Proof. vm_refl. Qed.
Lemma D_5eb7c : decode_any W_5eb7c = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb80 : bv 32 := 0x008ab4a3.
Lemma F_5eb80 : fetch_word AsanUbsan.M.loaded_segments (0x5eb80 : word) = Some W_5eb80.
Proof. vm_refl. Qed.
Lemma D_5eb80 : decode_any W_5eb80 = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb84 : bv 32 := 0x80040513.
Lemma F_5eb84 : fetch_word AsanUbsan.M.loaded_segments (0x5eb84 : word) = Some W_5eb84.
Proof. vm_refl. Qed.
Lemma D_5eb84 : decode_any W_5eb84 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb88 : bv 32 := 0xfa850513.
Lemma F_5eb88 : fetch_word AsanUbsan.M.loaded_segments (0x5eb88 : word) = Some W_5eb88.
Proof. vm_refl. Qed.
Lemma D_5eb88 : decode_any W_5eb88 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb8c : bv 32 := 0x0ff00793.
Lemma F_5eb8c : fetch_word AsanUbsan.M.loaded_segments (0x5eb8c : word) = Some W_5eb8c.
Proof. vm_refl. Qed.
Lemma D_5eb8c : decode_any W_5eb8c = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb90 : bv 32 := 0x00040613.
Lemma F_5eb90 : fetch_word AsanUbsan.M.loaded_segments (0x5eb90 : word) = Some W_5eb90.
Proof. vm_refl. Qed.
Lemma D_5eb90 : decode_any W_5eb90 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb94 : bv 32 := 0x00000693.
Lemma F_5eb94 : fetch_word AsanUbsan.M.loaded_segments (0x5eb94 : word) = Some W_5eb94.
Proof. vm_refl. Qed.
Lemma D_5eb94 : decode_any W_5eb94 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb98 : bv 32 := 0x464090ef.
Lemma F_5eb98 : fetch_word AsanUbsan.M.loaded_segments (0x5eb98 : word) = Some W_5eb98.
Proof. vm_refl. Qed.
Lemma D_5eb98 : decode_any W_5eb98 = Some (Jal 1 37988, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb9c : bv 32 := 0x80040613.
Lemma F_5eb9c : fetch_word AsanUbsan.M.loaded_segments (0x5eb9c : word) = Some W_5eb9c.
Proof. vm_refl. Qed.
Lemma D_5eb9c : decode_any W_5eb9c = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eba0 : bv 32 := 0xfa860613.
Lemma F_5eba0 : fetch_word AsanUbsan.M.loaded_segments (0x5eba0 : word) = Some W_5eba0.
Proof. vm_refl. Qed.
Lemma D_5eba0 : decode_any W_5eba0 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eba4 : bv 32 := 0x00090513.
Lemma F_5eba4 : fetch_word AsanUbsan.M.loaded_segments (0x5eba4 : word) = Some W_5eba4.
Proof. vm_refl. Qed.
Lemma D_5eba4 : decode_any W_5eba4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eba8 : bv 32 := 0x00048593.
Lemma F_5eba8 : fetch_word AsanUbsan.M.loaded_segments (0x5eba8 : word) = Some W_5eba8.
Proof. vm_refl. Qed.
Lemma D_5eba8 : decode_any W_5eba8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebac : bv 32 := 0x208060ef.
Lemma F_5ebac : fetch_word AsanUbsan.M.loaded_segments (0x5ebac : word) = Some W_5ebac.
Proof. vm_refl. Qed.
Lemma D_5ebac : decode_any W_5ebac = Some (Jal 1 25096, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebb0 : bv 32 := 0x00098513.
Lemma F_5ebb0 : fetch_word AsanUbsan.M.loaded_segments (0x5ebb0 : word) = Some W_5ebb0.
Proof. vm_refl. Qed.
Lemma D_5ebb0 : decode_any W_5ebb0 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebb4 : bv 32 := 0x00090593.
Lemma F_5ebb4 : fetch_word AsanUbsan.M.loaded_segments (0x5ebb4 : word) = Some W_5ebb4.
Proof. vm_refl. Qed.
Lemma D_5ebb4 : decode_any W_5ebb4 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebb8 : bv 32 := 0x00048613.
Lemma F_5ebb8 : fetch_word AsanUbsan.M.loaded_segments (0x5ebb8 : word) = Some W_5ebb8.
Proof. vm_refl. Qed.
Lemma D_5ebb8 : decode_any W_5ebb8 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebbc : bv 32 := 0xfbf48993.
Lemma F_5ebbc : fetch_word AsanUbsan.M.loaded_segments (0x5ebbc : word) = Some W_5ebbc.
Proof. vm_refl. Qed.
Lemma D_5ebbc : decode_any W_5ebbc = Some (OpImm ALU_ADD 19 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebc0 : bv 32 := 0xfbf00693.
Lemma F_5ebc0 : fetch_word AsanUbsan.M.loaded_segments (0x5ebc0 : word) = Some W_5ebc0.
Proof. vm_refl. Qed.
Lemma D_5ebc0 : decode_any W_5ebc0 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebc4 : bv 32 := 0xed36e2e3.
Lemma F_5ebc4 : fetch_word AsanUbsan.M.loaded_segments (0x5ebc4 : word) = Some W_5ebc4.
Proof. vm_refl. Qed.
Lemma D_5ebc4 : decode_any W_5ebc4 = Some (Branch BC_LTU 13 19 7876, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebc8 : bv 32 := 0x0c061463.
Lemma F_5ebc8 : fetch_word AsanUbsan.M.loaded_segments (0x5ebc8 : word) = Some W_5ebc8.
Proof. vm_refl. Qed.
Lemma D_5ebc8 : decode_any W_5ebc8 = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebcc : bv 32 := 0xef9ff06f.
Lemma F_5ebcc : fetch_word AsanUbsan.M.loaded_segments (0x5ebcc : word) = Some W_5ebcc.
Proof. vm_refl. Qed.
Lemma D_5ebcc : decode_any W_5ebcc = Some (Jal 0 2096888, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebd0 : bv 32 := 0x80040693.
Lemma F_5ebd0 : fetch_word AsanUbsan.M.loaded_segments (0x5ebd0 : word) = Some W_5ebd0.
Proof. vm_refl. Qed.
Lemma D_5ebd0 : decode_any W_5ebd0 = Some (OpImm ALU_ADD 13 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebd4 : bv 32 := 0xfb868693.
Lemma F_5ebd4 : fetch_word AsanUbsan.M.loaded_segments (0x5ebd4 : word) = Some W_5ebd4.
Proof. vm_refl. Qed.
Lemma D_5ebd4 : decode_any W_5ebd4 = Some (OpImm ALU_ADD 13 13 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebd8 : bv 32 := 0x80040713.
Lemma F_5ebd8 : fetch_word AsanUbsan.M.loaded_segments (0x5ebd8 : word) = Some W_5ebd8.
Proof. vm_refl. Qed.
Lemma D_5ebd8 : decode_any W_5ebd8 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebdc : bv 32 := 0xfa870713.
Lemma F_5ebdc : fetch_word AsanUbsan.M.loaded_segments (0x5ebdc : word) = Some W_5ebdc.
Proof. vm_refl. Qed.
Lemma D_5ebdc : decode_any W_5ebdc = Some (OpImm ALU_ADD 14 14 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebe0 : bv 32 := 0x7ff70b13.
Lemma F_5ebe0 : fetch_word AsanUbsan.M.loaded_segments (0x5ebe0 : word) = Some W_5ebe0.
Proof. vm_refl. Qed.
Lemma D_5ebe0 : decode_any W_5ebe0 = Some (OpImm ALU_ADD 22 14 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebe4 : bv 32 := 0x000b34a3.
Lemma F_5ebe4 : fetch_word AsanUbsan.M.loaded_segments (0x5ebe4 : word) = Some W_5ebe4.
Proof. vm_refl. Qed.
Lemma D_5ebe4 : decode_any W_5ebe4 = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebe8 : bv 32 := 0x00da3023.
Lemma F_5ebe8 : fetch_word AsanUbsan.M.loaded_segments (0x5ebe8 : word) = Some W_5ebe8.
Proof. vm_refl. Qed.
Lemma D_5ebe8 : decode_any W_5ebe8 = Some (Store SZ8 20 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebec : bv 32 := 0x000a3423.
Lemma F_5ebec : fetch_word AsanUbsan.M.loaded_segments (0x5ebec : word) = Some W_5ebec.
Proof. vm_refl. Qed.
Lemma D_5ebec : decode_any W_5ebec = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebf0 : bv 32 := 0x00060493.
Lemma F_5ebf0 : fetch_word AsanUbsan.M.loaded_segments (0x5ebf0 : word) = Some W_5ebf0.
Proof. vm_refl. Qed.
Lemma D_5ebf0 : decode_any W_5ebf0 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebf4 : bv 32 := 0x00058a93.
Lemma F_5ebf4 : fetch_word AsanUbsan.M.loaded_segments (0x5ebf4 : word) = Some W_5ebf4.
Proof. vm_refl. Qed.
Lemma D_5ebf4 : decode_any W_5ebf4 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebf8 : bv 32 := 0x00050913.
Lemma F_5ebf8 : fetch_word AsanUbsan.M.loaded_segments (0x5ebf8 : word) = Some W_5ebf8.
Proof. vm_refl. Qed.
Lemma D_5ebf8 : decode_any W_5ebf8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebfc : bv 32 := 0x6b1210ef.
Lemma F_5ebfc : fetch_word AsanUbsan.M.loaded_segments (0x5ebfc : word) = Some W_5ebfc.
Proof. vm_refl. Qed.
Lemma D_5ebfc : decode_any W_5ebfc = Some (Jal 1 138928, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec00 : bv 32 := 0x00050593.
Lemma F_5ec00 : fetch_word AsanUbsan.M.loaded_segments (0x5ec00 : word) = Some W_5ec00.
Proof. vm_refl. Qed.
Lemma D_5ec00 : decode_any W_5ec00 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec04 : bv 32 := 0x00078517.
Lemma F_5ec04 : fetch_word AsanUbsan.M.loaded_segments (0x5ec04 : word) = Some W_5ec04.
Proof. vm_refl. Qed.
Lemma D_5ec04 : decode_any W_5ec04 = Some (Auipc 10 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec08 : bv 32 := 0x8b453503.
Lemma F_5ec08 : fetch_word AsanUbsan.M.loaded_segments (0x5ec08 : word) = Some W_5ec08.
Proof. vm_refl. Qed.
Lemma D_5ec08 : decode_any W_5ec08 = Some (Load SZ8 true 10 10 2228, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec0c : bv 32 := 0x02154703.
Lemma F_5ec0c : fetch_word AsanUbsan.M.loaded_segments (0x5ec0c : word) = Some W_5ec0c.
Proof. vm_refl. Qed.
Lemma D_5ec0c : decode_any W_5ec0c = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec10 : bv 32 := 0x008b34a3.
Lemma F_5ec10 : fetch_word AsanUbsan.M.loaded_segments (0x5ec10 : word) = Some W_5ec10.
Proof. vm_refl. Qed.
Lemma D_5ec10 : decode_any W_5ec10 = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec14 : bv 32 := 0x80040513.
Lemma F_5ec14 : fetch_word AsanUbsan.M.loaded_segments (0x5ec14 : word) = Some W_5ec14.
Proof. vm_refl. Qed.
Lemma D_5ec14 : decode_any W_5ec14 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec18 : bv 32 := 0xfa850513.
Lemma F_5ec18 : fetch_word AsanUbsan.M.loaded_segments (0x5ec18 : word) = Some W_5ec18.
Proof. vm_refl. Qed.
Lemma D_5ec18 : decode_any W_5ec18 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec1c : bv 32 := 0x0ff00793.
Lemma F_5ec1c : fetch_word AsanUbsan.M.loaded_segments (0x5ec1c : word) = Some W_5ec1c.
Proof. vm_refl. Qed.
Lemma D_5ec1c : decode_any W_5ec1c = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec20 : bv 32 := 0x00040613.
Lemma F_5ec20 : fetch_word AsanUbsan.M.loaded_segments (0x5ec20 : word) = Some W_5ec20.
Proof. vm_refl. Qed.
Lemma D_5ec20 : decode_any W_5ec20 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec24 : bv 32 := 0x00000693.
Lemma F_5ec24 : fetch_word AsanUbsan.M.loaded_segments (0x5ec24 : word) = Some W_5ec24.
Proof. vm_refl. Qed.
Lemma D_5ec24 : decode_any W_5ec24 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec28 : bv 32 := 0x3d4090ef.
Lemma F_5ec28 : fetch_word AsanUbsan.M.loaded_segments (0x5ec28 : word) = Some W_5ec28.
Proof. vm_refl. Qed.
Lemma D_5ec28 : decode_any W_5ec28 = Some (Jal 1 37844, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec2c : bv 32 := 0x80040613.
Lemma F_5ec2c : fetch_word AsanUbsan.M.loaded_segments (0x5ec2c : word) = Some W_5ec2c.
Proof. vm_refl. Qed.
Lemma D_5ec2c : decode_any W_5ec2c = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec30 : bv 32 := 0xfa860613.
Lemma F_5ec30 : fetch_word AsanUbsan.M.loaded_segments (0x5ec30 : word) = Some W_5ec30.
Proof. vm_refl. Qed.
Lemma D_5ec30 : decode_any W_5ec30 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec34 : bv 32 := 0x00090513.
Lemma F_5ec34 : fetch_word AsanUbsan.M.loaded_segments (0x5ec34 : word) = Some W_5ec34.
Proof. vm_refl. Qed.
Lemma D_5ec34 : decode_any W_5ec34 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec38 : bv 32 := 0x00048593.
Lemma F_5ec38 : fetch_word AsanUbsan.M.loaded_segments (0x5ec38 : word) = Some W_5ec38.
Proof. vm_refl. Qed.
Lemma D_5ec38 : decode_any W_5ec38 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec3c : bv 32 := 0x178060ef.
Lemma F_5ec3c : fetch_word AsanUbsan.M.loaded_segments (0x5ec3c : word) = Some W_5ec3c.
Proof. vm_refl. Qed.
Lemma D_5ec3c : decode_any W_5ec3c = Some (Jal 1 24952, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec40 : bv 32 := 0x00090513.
Lemma F_5ec40 : fetch_word AsanUbsan.M.loaded_segments (0x5ec40 : word) = Some W_5ec40.
Proof. vm_refl. Qed.
Lemma D_5ec40 : decode_any W_5ec40 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec44 : bv 32 := 0x000a8593.
Lemma F_5ec44 : fetch_word AsanUbsan.M.loaded_segments (0x5ec44 : word) = Some W_5ec44.
Proof. vm_refl. Qed.
Lemma D_5ec44 : decode_any W_5ec44 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec48 : bv 32 := 0x00048613.
Lemma F_5ec48 : fetch_word AsanUbsan.M.loaded_segments (0x5ec48 : word) = Some W_5ec48.
Proof. vm_refl. Qed.
Lemma D_5ec48 : decode_any W_5ec48 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec4c : bv 32 := 0xfbf00693.
Lemma F_5ec4c : fetch_word AsanUbsan.M.loaded_segments (0x5ec4c : word) = Some W_5ec4c.
Proof. vm_refl. Qed.
Lemma D_5ec4c : decode_any W_5ec4c = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec50 : bv 32 := 0xe936e2e3.
Lemma F_5ec50 : fetch_word AsanUbsan.M.loaded_segments (0x5ec50 : word) = Some W_5ec50.
Proof. vm_refl. Qed.
Lemma D_5ec50 : decode_any W_5ec50 = Some (Branch BC_LTU 13 19 7812, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec54 : bv 32 := 0x0e061063.
Lemma F_5ec54 : fetch_word AsanUbsan.M.loaded_segments (0x5ec54 : word) = Some W_5ec54.
Proof. vm_refl. Qed.
Lemma D_5ec54 : decode_any W_5ec54 = Some (Branch BC_NE 12 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec58 : bv 32 := 0xeb9ff06f.
Lemma F_5ec58 : fetch_word AsanUbsan.M.loaded_segments (0x5ec58 : word) = Some W_5ec58.
Proof. vm_refl. Qed.
Lemma D_5ec58 : decode_any W_5ec58 = Some (Jal 0 2096824, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec5c : bv 32 := 0x00070803.
Lemma F_5ec5c : fetch_word AsanUbsan.M.loaded_segments (0x5ec5c : word) = Some W_5ec5c.
Proof. vm_refl. Qed.
Lemma D_5ec5c : decode_any W_5ec5c = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec60 : bv 32 := 0x0077f793.
Lemma F_5ec60 : fetch_word AsanUbsan.M.loaded_segments (0x5ec60 : word) = Some W_5ec60.
Proof. vm_refl. Qed.
Lemma D_5ec60 : decode_any W_5ec60 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec64 : bv 32 := 0x010038b3.
Lemma F_5ec64 : fetch_word AsanUbsan.M.loaded_segments (0x5ec64 : word) = Some W_5ec64.
Proof. vm_refl. Qed.
Lemma D_5ec64 : decode_any W_5ec64 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec68 : bv 32 := 0x0107a7b3.
Lemma F_5ec68 : fetch_word AsanUbsan.M.loaded_segments (0x5ec68 : word) = Some W_5ec68.
Proof. vm_refl. Qed.
Lemma D_5ec68 : decode_any W_5ec68 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec6c : bv 32 := 0x0017c793.
Lemma F_5ec6c : fetch_word AsanUbsan.M.loaded_segments (0x5ec6c : word) = Some W_5ec6c.
Proof. vm_refl. Qed.
Lemma D_5ec6c : decode_any W_5ec6c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec70 : bv 32 := 0x00f8f7b3.
Lemma F_5ec70 : fetch_word AsanUbsan.M.loaded_segments (0x5ec70 : word) = Some W_5ec70.
Proof. vm_refl. Qed.
Lemma D_5ec70 : decode_any W_5ec70 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec74 : bv 32 := 0x00e6fa63.
Lemma F_5ec74 : fetch_word AsanUbsan.M.loaded_segments (0x5ec74 : word) = Some W_5ec74.
Proof. vm_refl. Qed.
Lemma D_5ec74 : decode_any W_5ec74 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec78 : bv 32 := 0x0006c803.
Lemma F_5ec78 : fetch_word AsanUbsan.M.loaded_segments (0x5ec78 : word) = Some W_5ec78.
Proof. vm_refl. Qed.
Lemma D_5ec78 : decode_any W_5ec78 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec7c : bv 32 := 0x00168693.
Lemma F_5ec7c : fetch_word AsanUbsan.M.loaded_segments (0x5ec7c : word) = Some W_5ec7c.
Proof. vm_refl. Qed.
Lemma D_5ec7c : decode_any W_5ec7c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec80 : bv 32 := 0x00f867b3.
Lemma F_5ec80 : fetch_word AsanUbsan.M.loaded_segments (0x5ec80 : word) = Some W_5ec80.
Proof. vm_refl. Qed.
Lemma D_5ec80 : decode_any W_5ec80 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec84 : bv 32 := 0xfee69ae3.
Lemma F_5ec84 : fetch_word AsanUbsan.M.loaded_segments (0x5ec84 : word) = Some W_5ec84.
Proof. vm_refl. Qed.
Lemma D_5ec84 : decode_any W_5ec84 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec88 : bv 32 := 0x0ff7f693.
Lemma F_5ec88 : fetch_word AsanUbsan.M.loaded_segments (0x5ec88 : word) = Some W_5ec88.
Proof. vm_refl. Qed.
Lemma D_5ec88 : decode_any W_5ec88 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec8c : bv 32 := 0xe2068ce3.
Lemma F_5ec8c : fetch_word AsanUbsan.M.loaded_segments (0x5ec8c : word) = Some W_5ec8c.
Proof. vm_refl. Qed.
Lemma D_5ec8c : decode_any W_5ec8c = Some (Branch BC_EQ 13 0 7736, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec90 : bv 32 := 0x00050a93.
Lemma F_5ec90 : fetch_word AsanUbsan.M.loaded_segments (0x5ec90 : word) = Some W_5ec90.
Proof. vm_refl. Qed.
Lemma D_5ec90 : decode_any W_5ec90 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec94 : bv 32 := 0x00058513.
Lemma F_5ec94 : fetch_word AsanUbsan.M.loaded_segments (0x5ec94 : word) = Some W_5ec94.
Proof. vm_refl. Qed.
Lemma D_5ec94 : decode_any W_5ec94 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec98 : bv 32 := 0x00058b13.
Lemma F_5ec98 : fetch_word AsanUbsan.M.loaded_segments (0x5ec98 : word) = Some W_5ec98.
Proof. vm_refl. Qed.
Lemma D_5ec98 : decode_any W_5ec98 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec9c : bv 32 := 0x00060593.
Lemma F_5ec9c : fetch_word AsanUbsan.M.loaded_segments (0x5ec9c : word) = Some W_5ec9c.
Proof. vm_refl. Qed.
Lemma D_5ec9c : decode_any W_5ec9c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eca0 : bv 32 := 0x00060493.
Lemma F_5eca0 : fetch_word AsanUbsan.M.loaded_segments (0x5eca0 : word) = Some W_5eca0.
Proof. vm_refl. Qed.
Lemma D_5eca0 : decode_any W_5eca0 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eca4 : bv 32 := 0x6dd020ef.
Lemma F_5eca4 : fetch_word AsanUbsan.M.loaded_segments (0x5eca4 : word) = Some W_5eca4.
Proof. vm_refl. Qed.
Lemma D_5eca4 : decode_any W_5eca4 = Some (Jal 1 11996, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eca8 : bv 32 := 0x000b0593.
Lemma F_5eca8 : fetch_word AsanUbsan.M.loaded_segments (0x5eca8 : word) = Some W_5eca8.
Proof. vm_refl. Qed.
Lemma D_5eca8 : decode_any W_5eca8 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecac : bv 32 := 0x00048613.
Lemma F_5ecac : fetch_word AsanUbsan.M.loaded_segments (0x5ecac : word) = Some W_5ecac.
Proof. vm_refl. Qed.
Lemma D_5ecac : decode_any W_5ecac = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecb0 : bv 32 := 0x00050913.
Lemma F_5ecb0 : fetch_word AsanUbsan.M.loaded_segments (0x5ecb0 : word) = Some W_5ecb0.
Proof. vm_refl. Qed.
Lemma D_5ecb0 : decode_any W_5ecb0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecb4 : bv 32 := 0x000a8513.
Lemma F_5ecb4 : fetch_word AsanUbsan.M.loaded_segments (0x5ecb4 : word) = Some W_5ecb4.
Proof. vm_refl. Qed.
Lemma D_5ecb4 : decode_any W_5ecb4 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecb8 : bv 32 := 0xe00906e3.
Lemma F_5ecb8 : fetch_word AsanUbsan.M.loaded_segments (0x5ecb8 : word) = Some W_5ecb8.
Proof. vm_refl. Qed.
Lemma D_5ecb8 : decode_any W_5ecb8 = Some (Branch BC_EQ 18 0 7692, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecbc : bv 32 := 0x5f1210ef.
Lemma F_5ecbc : fetch_word AsanUbsan.M.loaded_segments (0x5ecbc : word) = Some W_5ecbc.
Proof. vm_refl. Qed.
Lemma D_5ecbc : decode_any W_5ecbc = Some (Jal 1 138736, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecc0 : bv 32 := 0xfffb1597.
Lemma F_5ecc0 : fetch_word AsanUbsan.M.loaded_segments (0x5ecc0 : word) = Some W_5ecc0.
Proof. vm_refl. Qed.
Lemma D_5ecc0 : decode_any W_5ecc0 = Some (Auipc 11 1048497, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecc4 : bv 32 := 0x7485b583.
Lemma F_5ecc4 : fetch_word AsanUbsan.M.loaded_segments (0x5ecc4 : word) = Some W_5ecc4.
Proof. vm_refl. Qed.
Lemma D_5ecc4 : decode_any W_5ecc4 = Some (Load SZ8 true 11 11 1864, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecc8 : bv 32 := 0x00ba3023.
Lemma F_5ecc8 : fetch_word AsanUbsan.M.loaded_segments (0x5ecc8 : word) = Some W_5ecc8.
Proof. vm_refl. Qed.
Lemma D_5ecc8 : decode_any W_5ecc8 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eccc : bv 32 := 0x80040613.
Lemma F_5eccc : fetch_word AsanUbsan.M.loaded_segments (0x5eccc : word) = Some W_5eccc.
Proof. vm_refl. Qed.
Lemma D_5eccc : decode_any W_5eccc = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecd0 : bv 32 := 0xfa860613.
Lemma F_5ecd0 : fetch_word AsanUbsan.M.loaded_segments (0x5ecd0 : word) = Some W_5ecd0.
Proof. vm_refl. Qed.
Lemma D_5ecd0 : decode_any W_5ecd0 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecd4 : bv 32 := 0x00040593.
Lemma F_5ecd4 : fetch_word AsanUbsan.M.loaded_segments (0x5ecd4 : word) = Some W_5ecd4.
Proof. vm_refl. Qed.
Lemma D_5ecd4 : decode_any W_5ecd4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecd8 : bv 32 := 0x00090693.
Lemma F_5ecd8 : fetch_word AsanUbsan.M.loaded_segments (0x5ecd8 : word) = Some W_5ecd8.
Proof. vm_refl. Qed.
Lemma D_5ecd8 : decode_any W_5ecd8 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecdc : bv 32 := 0x00000713.
Lemma F_5ecdc : fetch_word AsanUbsan.M.loaded_segments (0x5ecdc : word) = Some W_5ecdc.
Proof. vm_refl. Qed.
Lemma D_5ecdc : decode_any W_5ecdc = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ece0 : bv 32 := 0x00048793.
Lemma F_5ece0 : fetch_word AsanUbsan.M.loaded_segments (0x5ece0 : word) = Some W_5ece0.
Proof. vm_refl. Qed.
Lemma D_5ece0 : decode_any W_5ece0 = Some (OpImm ALU_ADD 15 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ece4 : bv 32 := 0x00000813.
Lemma F_5ece4 : fetch_word AsanUbsan.M.loaded_segments (0x5ece4 : word) = Some W_5ece4.
Proof. vm_refl. Qed.
Lemma D_5ece4 : decode_any W_5ece4 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ece8 : bv 32 := 0x00000893.
Lemma F_5ece8 : fetch_word AsanUbsan.M.loaded_segments (0x5ece8 : word) = Some W_5ece8.
Proof. vm_refl. Qed.
Lemma D_5ece8 : decode_any W_5ece8 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecec : bv 32 := 0x620060ef.
Lemma F_5ecec : fetch_word AsanUbsan.M.loaded_segments (0x5ecec : word) = Some W_5ecec.
Proof. vm_refl. Qed.
Lemma D_5ecec : decode_any W_5ecec = Some (Jal 1 26144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecf0 : bv 32 := 0x000a8513.
Lemma F_5ecf0 : fetch_word AsanUbsan.M.loaded_segments (0x5ecf0 : word) = Some W_5ecf0.
Proof. vm_refl. Qed.
Lemma D_5ecf0 : decode_any W_5ecf0 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecf4 : bv 32 := 0x000b0593.
Lemma F_5ecf4 : fetch_word AsanUbsan.M.loaded_segments (0x5ecf4 : word) = Some W_5ecf4.
Proof. vm_refl. Qed.
Lemma D_5ecf4 : decode_any W_5ecf4 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecf8 : bv 32 := 0x00048613.
Lemma F_5ecf8 : fetch_word AsanUbsan.M.loaded_segments (0x5ecf8 : word) = Some W_5ecf8.
Proof. vm_refl. Qed.
Lemma D_5ecf8 : decode_any W_5ecf8 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecfc : bv 32 := 0xdc9ff06f.
Lemma F_5ecfc : fetch_word AsanUbsan.M.loaded_segments (0x5ecfc : word) = Some W_5ecfc.
Proof. vm_refl. Qed.
Lemma D_5ecfc : decode_any W_5ecfc = Some (Jal 0 2096584, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed00 : bv 32 := 0x00070803.
Lemma F_5ed00 : fetch_word AsanUbsan.M.loaded_segments (0x5ed00 : word) = Some W_5ed00.
Proof. vm_refl. Qed.
Lemma D_5ed00 : decode_any W_5ed00 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed04 : bv 32 := 0x0077f793.
Lemma F_5ed04 : fetch_word AsanUbsan.M.loaded_segments (0x5ed04 : word) = Some W_5ed04.
Proof. vm_refl. Qed.
Lemma D_5ed04 : decode_any W_5ed04 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed08 : bv 32 := 0x010038b3.
Lemma F_5ed08 : fetch_word AsanUbsan.M.loaded_segments (0x5ed08 : word) = Some W_5ed08.
Proof. vm_refl. Qed.
Lemma D_5ed08 : decode_any W_5ed08 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed0c : bv 32 := 0x0107a7b3.
Lemma F_5ed0c : fetch_word AsanUbsan.M.loaded_segments (0x5ed0c : word) = Some W_5ed0c.
Proof. vm_refl. Qed.
Lemma D_5ed0c : decode_any W_5ed0c = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed10 : bv 32 := 0x0017c793.
Lemma F_5ed10 : fetch_word AsanUbsan.M.loaded_segments (0x5ed10 : word) = Some W_5ed10.
Proof. vm_refl. Qed.
Lemma D_5ed10 : decode_any W_5ed10 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed14 : bv 32 := 0x00f8f7b3.
Lemma F_5ed14 : fetch_word AsanUbsan.M.loaded_segments (0x5ed14 : word) = Some W_5ed14.
Proof. vm_refl. Qed.
Lemma D_5ed14 : decode_any W_5ed14 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed18 : bv 32 := 0x00e6fa63.
Lemma F_5ed18 : fetch_word AsanUbsan.M.loaded_segments (0x5ed18 : word) = Some W_5ed18.
Proof. vm_refl. Qed.
Lemma D_5ed18 : decode_any W_5ed18 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed1c : bv 32 := 0x0006c803.
Lemma F_5ed1c : fetch_word AsanUbsan.M.loaded_segments (0x5ed1c : word) = Some W_5ed1c.
Proof. vm_refl. Qed.
Lemma D_5ed1c : decode_any W_5ed1c = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed20 : bv 32 := 0x00168693.
Lemma F_5ed20 : fetch_word AsanUbsan.M.loaded_segments (0x5ed20 : word) = Some W_5ed20.
Proof. vm_refl. Qed.
Lemma D_5ed20 : decode_any W_5ed20 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed24 : bv 32 := 0x00f867b3.
Lemma F_5ed24 : fetch_word AsanUbsan.M.loaded_segments (0x5ed24 : word) = Some W_5ed24.
Proof. vm_refl. Qed.
Lemma D_5ed24 : decode_any W_5ed24 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed28 : bv 32 := 0xfee69ae3.
Lemma F_5ed28 : fetch_word AsanUbsan.M.loaded_segments (0x5ed28 : word) = Some W_5ed28.
Proof. vm_refl. Qed.
Lemma D_5ed28 : decode_any W_5ed28 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed2c : bv 32 := 0x0ff7f693.
Lemma F_5ed2c : fetch_word AsanUbsan.M.loaded_segments (0x5ed2c : word) = Some W_5ed2c.
Proof. vm_refl. Qed.
Lemma D_5ed2c : decode_any W_5ed2c = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed30 : bv 32 := 0xde0680e3.
Lemma F_5ed30 : fetch_word AsanUbsan.M.loaded_segments (0x5ed30 : word) = Some W_5ed30.
Proof. vm_refl. Qed.
Lemma D_5ed30 : decode_any W_5ed30 = Some (Branch BC_EQ 13 0 7648, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed34 : bv 32 := 0x00050493.
Lemma F_5ed34 : fetch_word AsanUbsan.M.loaded_segments (0x5ed34 : word) = Some W_5ed34.
Proof. vm_refl. Qed.
Lemma D_5ed34 : decode_any W_5ed34 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed38 : bv 32 := 0x00058a93.
Lemma F_5ed38 : fetch_word AsanUbsan.M.loaded_segments (0x5ed38 : word) = Some W_5ed38.
Proof. vm_refl. Qed.
Lemma D_5ed38 : decode_any W_5ed38 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed3c : bv 32 := 0x00060593.
Lemma F_5ed3c : fetch_word AsanUbsan.M.loaded_segments (0x5ed3c : word) = Some W_5ed3c.
Proof. vm_refl. Qed.
Lemma D_5ed3c : decode_any W_5ed3c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed40 : bv 32 := 0x00060913.
Lemma F_5ed40 : fetch_word AsanUbsan.M.loaded_segments (0x5ed40 : word) = Some W_5ed40.
Proof. vm_refl. Qed.
Lemma D_5ed40 : decode_any W_5ed40 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed44 : bv 32 := 0x63d020ef.
Lemma F_5ed44 : fetch_word AsanUbsan.M.loaded_segments (0x5ed44 : word) = Some W_5ed44.
Proof. vm_refl. Qed.
Lemma D_5ed44 : decode_any W_5ed44 = Some (Jal 1 11836, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed48 : bv 32 := 0x000a8593.
Lemma F_5ed48 : fetch_word AsanUbsan.M.loaded_segments (0x5ed48 : word) = Some W_5ed48.
Proof. vm_refl. Qed.
Lemma D_5ed48 : decode_any W_5ed48 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed4c : bv 32 := 0x00090613.
Lemma F_5ed4c : fetch_word AsanUbsan.M.loaded_segments (0x5ed4c : word) = Some W_5ed4c.
Proof. vm_refl. Qed.
Lemma D_5ed4c : decode_any W_5ed4c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed50 : bv 32 := 0x00050993.
Lemma F_5ed50 : fetch_word AsanUbsan.M.loaded_segments (0x5ed50 : word) = Some W_5ed50.
Proof. vm_refl. Qed.
Lemma D_5ed50 : decode_any W_5ed50 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed54 : bv 32 := 0x00048513.
Lemma F_5ed54 : fetch_word AsanUbsan.M.loaded_segments (0x5ed54 : word) = Some W_5ed54.
Proof. vm_refl. Qed.
Lemma D_5ed54 : decode_any W_5ed54 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed58 : bv 32 := 0xda098ce3.
Lemma F_5ed58 : fetch_word AsanUbsan.M.loaded_segments (0x5ed58 : word) = Some W_5ed58.
Proof. vm_refl. Qed.
Lemma D_5ed58 : decode_any W_5ed58 = Some (Branch BC_EQ 19 0 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed5c : bv 32 := 0x551210ef.
Lemma F_5ed5c : fetch_word AsanUbsan.M.loaded_segments (0x5ed5c : word) = Some W_5ed5c.
Proof. vm_refl. Qed.
Lemma D_5ed5c : decode_any W_5ed5c = Some (Jal 1 138576, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed60 : bv 32 := 0xfffb1597.
Lemma F_5ed60 : fetch_word AsanUbsan.M.loaded_segments (0x5ed60 : word) = Some W_5ed60.
Proof. vm_refl. Qed.
Lemma D_5ed60 : decode_any W_5ed60 = Some (Auipc 11 1048497, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed64 : bv 32 := 0x6a85b583.
Lemma F_5ed64 : fetch_word AsanUbsan.M.loaded_segments (0x5ed64 : word) = Some W_5ed64.
Proof. vm_refl. Qed.
Lemma D_5ed64 : decode_any W_5ed64 = Some (Load SZ8 true 11 11 1704, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed68 : bv 32 := 0x00ba3023.
Lemma F_5ed68 : fetch_word AsanUbsan.M.loaded_segments (0x5ed68 : word) = Some W_5ed68.
Proof. vm_refl. Qed.
Lemma D_5ed68 : decode_any W_5ed68 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed6c : bv 32 := 0x80040613.
Lemma F_5ed6c : fetch_word AsanUbsan.M.loaded_segments (0x5ed6c : word) = Some W_5ed6c.
Proof. vm_refl. Qed.
Lemma D_5ed6c : decode_any W_5ed6c = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed70 : bv 32 := 0xfa860613.
Lemma F_5ed70 : fetch_word AsanUbsan.M.loaded_segments (0x5ed70 : word) = Some W_5ed70.
Proof. vm_refl. Qed.
Lemma D_5ed70 : decode_any W_5ed70 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed74 : bv 32 := 0x00100713.
Lemma F_5ed74 : fetch_word AsanUbsan.M.loaded_segments (0x5ed74 : word) = Some W_5ed74.
Proof. vm_refl. Qed.
Lemma D_5ed74 : decode_any W_5ed74 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed78 : bv 32 := 0x00040593.
Lemma F_5ed78 : fetch_word AsanUbsan.M.loaded_segments (0x5ed78 : word) = Some W_5ed78.
Proof. vm_refl. Qed.
Lemma D_5ed78 : decode_any W_5ed78 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed7c : bv 32 := 0x00098693.
Lemma F_5ed7c : fetch_word AsanUbsan.M.loaded_segments (0x5ed7c : word) = Some W_5ed7c.
Proof. vm_refl. Qed.
Lemma D_5ed7c : decode_any W_5ed7c = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed80 : bv 32 := 0x00090793.
Lemma F_5ed80 : fetch_word AsanUbsan.M.loaded_segments (0x5ed80 : word) = Some W_5ed80.
Proof. vm_refl. Qed.
Lemma D_5ed80 : decode_any W_5ed80 = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed84 : bv 32 := 0x00000813.
Lemma F_5ed84 : fetch_word AsanUbsan.M.loaded_segments (0x5ed84 : word) = Some W_5ed84.
Proof. vm_refl. Qed.
Lemma D_5ed84 : decode_any W_5ed84 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed88 : bv 32 := 0x00000893.
Lemma F_5ed88 : fetch_word AsanUbsan.M.loaded_segments (0x5ed88 : word) = Some W_5ed88.
Proof. vm_refl. Qed.
Lemma D_5ed88 : decode_any W_5ed88 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed8c : bv 32 := 0x580060ef.
Lemma F_5ed8c : fetch_word AsanUbsan.M.loaded_segments (0x5ed8c : word) = Some W_5ed8c.
Proof. vm_refl. Qed.
Lemma D_5ed8c : decode_any W_5ed8c = Some (Jal 1 25984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed90 : bv 32 := 0x00048513.
Lemma F_5ed90 : fetch_word AsanUbsan.M.loaded_segments (0x5ed90 : word) = Some W_5ed90.
Proof. vm_refl. Qed.
Lemma D_5ed90 : decode_any W_5ed90 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed94 : bv 32 := 0x000a8593.
Lemma F_5ed94 : fetch_word AsanUbsan.M.loaded_segments (0x5ed94 : word) = Some W_5ed94.
Proof. vm_refl. Qed.
Lemma D_5ed94 : decode_any W_5ed94 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed98 : bv 32 := 0x00090613.
Lemma F_5ed98 : fetch_word AsanUbsan.M.loaded_segments (0x5ed98 : word) = Some W_5ed98.
Proof. vm_refl. Qed.
Lemma D_5ed98 : decode_any W_5ed98 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed9c : bv 32 := 0xd75ff06f.
Lemma F_5ed9c : fetch_word AsanUbsan.M.loaded_segments (0x5ed9c : word) = Some W_5ed9c.
Proof. vm_refl. Qed.
Lemma D_5ed9c : decode_any W_5ed9c = Some (Jal 0 2096500, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eda0 : bv 32 := 0x81010113.
Lemma F_5eda0 : fetch_word AsanUbsan.M.loaded_segments (0x5eda0 : word) = Some W_5eda0.
Proof. vm_refl. Qed.
Lemma D_5eda0 : decode_any W_5eda0 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eda4 : bv 32 := 0x7e113423.
Lemma F_5eda4 : fetch_word AsanUbsan.M.loaded_segments (0x5eda4 : word) = Some W_5eda4.
Proof. vm_refl. Qed.
Lemma D_5eda4 : decode_any W_5eda4 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eda8 : bv 32 := 0x7e813023.
Lemma F_5eda8 : fetch_word AsanUbsan.M.loaded_segments (0x5eda8 : word) = Some W_5eda8.
Proof. vm_refl. Qed.
Lemma D_5eda8 : decode_any W_5eda8 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edac : bv 32 := 0x7c913c23.
Lemma F_5edac : fetch_word AsanUbsan.M.loaded_segments (0x5edac : word) = Some W_5edac.
Proof. vm_refl. Qed.
Lemma D_5edac : decode_any W_5edac = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edb0 : bv 32 := 0x7d213823.
Lemma F_5edb0 : fetch_word AsanUbsan.M.loaded_segments (0x5edb0 : word) = Some W_5edb0.
Proof. vm_refl. Qed.
Lemma D_5edb0 : decode_any W_5edb0 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edb4 : bv 32 := 0x7d313423.
Lemma F_5edb4 : fetch_word AsanUbsan.M.loaded_segments (0x5edb4 : word) = Some W_5edb4.
Proof. vm_refl. Qed.
Lemma D_5edb4 : decode_any W_5edb4 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edb8 : bv 32 := 0x7d413023.
Lemma F_5edb8 : fetch_word AsanUbsan.M.loaded_segments (0x5edb8 : word) = Some W_5edb8.
Proof. vm_refl. Qed.
Lemma D_5edb8 : decode_any W_5edb8 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edbc : bv 32 := 0x7b513c23.
Lemma F_5edbc : fetch_word AsanUbsan.M.loaded_segments (0x5edbc : word) = Some W_5edbc.
Proof. vm_refl. Qed.
Lemma D_5edbc : decode_any W_5edbc = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edc0 : bv 32 := 0x7b613823.
Lemma F_5edc0 : fetch_word AsanUbsan.M.loaded_segments (0x5edc0 : word) = Some W_5edc0.
Proof. vm_refl. Qed.
Lemma D_5edc0 : decode_any W_5edc0 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edc4 : bv 32 := 0x7f010413.
Lemma F_5edc4 : fetch_word AsanUbsan.M.loaded_segments (0x5edc4 : word) = Some W_5edc4.
Proof. vm_refl. Qed.
Lemma D_5edc4 : decode_any W_5edc4 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edc8 : bv 32 := 0xf9010113.
Lemma F_5edc8 : fetch_word AsanUbsan.M.loaded_segments (0x5edc8 : word) = Some W_5edc8.
Proof. vm_refl. Qed.
Lemma D_5edc8 : decode_any W_5edc8 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edcc : bv 32 := 0x00078697.
Lemma F_5edcc : fetch_word AsanUbsan.M.loaded_segments (0x5edcc : word) = Some W_5edcc.
Proof. vm_refl. Qed.
Lemma D_5edcc : decode_any W_5edcc = Some (Auipc 13 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edd0 : bv 32 := 0x2646b683.
Lemma F_5edd0 : fetch_word AsanUbsan.M.loaded_segments (0x5edd0 : word) = Some W_5edd0.
Proof. vm_refl. Qed.
Lemma D_5edd0 : decode_any W_5edd0 = Some (Load SZ8 true 13 13 612, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edd4 : bv 32 := 0x0006c683.
Lemma F_5edd4 : fetch_word AsanUbsan.M.loaded_segments (0x5edd4 : word) = Some W_5edd4.
Proof. vm_refl. Qed.
Lemma D_5edd4 : decode_any W_5edd4 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edd8 : bv 32 := 0x08068a63.
Lemma F_5edd8 : fetch_word AsanUbsan.M.loaded_segments (0x5edd8 : word) = Some W_5edd8.
Proof. vm_refl. Qed.
Lemma D_5edd8 : decode_any W_5edd8 = Some (Branch BC_EQ 13 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eddc : bv 32 := 0xfff54693.
Lemma F_5eddc : fetch_word AsanUbsan.M.loaded_segments (0x5eddc : word) = Some W_5eddc.
Proof. vm_refl. Qed.
Lemma D_5eddc : decode_any W_5eddc = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ede0 : bv 32 := 0x80040a93.
Lemma F_5ede0 : fetch_word AsanUbsan.M.loaded_segments (0x5ede0 : word) = Some W_5ede0.
Proof. vm_refl. Qed.
Lemma D_5ede0 : decode_any W_5ede0 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ede4 : bv 32 := 0xfa8a8a93.
Lemma F_5ede4 : fetch_word AsanUbsan.M.loaded_segments (0x5ede4 : word) = Some W_5ede4.
Proof. vm_refl. Qed.
Lemma D_5ede4 : decode_any W_5ede4 = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ede8 : bv 32 := 0x0cc6ea63.
Lemma F_5ede8 : fetch_word AsanUbsan.M.loaded_segments (0x5ede8 : word) = Some W_5ede8.
Proof. vm_refl. Qed.
Lemma D_5ede8 : decode_any W_5ede8 = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edec : bv 32 := 0xfbf60693.
Lemma F_5edec : fetch_word AsanUbsan.M.loaded_segments (0x5edec : word) = Some W_5edec.
Proof. vm_refl. Qed.
Lemma D_5edec : decode_any W_5edec = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edf0 : bv 32 := 0xfbf00713.
Lemma F_5edf0 : fetch_word AsanUbsan.M.loaded_segments (0x5edf0 : word) = Some W_5edf0.
Proof. vm_refl. Qed.
Lemma D_5edf0 : decode_any W_5edf0 = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edf4 : bv 32 := 0x14d77863.
Lemma F_5edf4 : fetch_word AsanUbsan.M.loaded_segments (0x5edf4 : word) = Some W_5edf4.
Proof. vm_refl. Qed.
Lemma D_5edf4 : decode_any W_5edf4 = Some (Branch BC_GEU 14 13 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edf8 : bv 32 := 0x00077697.
Lemma F_5edf8 : fetch_word AsanUbsan.M.loaded_segments (0x5edf8 : word) = Some W_5edf8.
Proof. vm_refl. Qed.
Lemma D_5edf8 : decode_any W_5edf8 = Some (Auipc 13 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edfc : bv 32 := 0x6d06b683.
Lemma F_5edfc : fetch_word AsanUbsan.M.loaded_segments (0x5edfc : word) = Some W_5edfc.
Proof. vm_refl. Qed.
Lemma D_5edfc : decode_any W_5edfc = Some (Load SZ8 true 13 13 1744, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee00 : bv 32 := 0x00c507b3.
Lemma F_5ee00 : fetch_word AsanUbsan.M.loaded_segments (0x5ee00 : word) = Some W_5ee00.
Proof. vm_refl. Qed.
Lemma D_5ee00 : decode_any W_5ee00 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee04 : bv 32 := 0x0006b703.
Lemma F_5ee04 : fetch_word AsanUbsan.M.loaded_segments (0x5ee04 : word) = Some W_5ee04.
Proof. vm_refl. Qed.
Lemma D_5ee04 : decode_any W_5ee04 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee08 : bv 32 := 0x00355693.
Lemma F_5ee08 : fetch_word AsanUbsan.M.loaded_segments (0x5ee08 : word) = Some W_5ee08.
Proof. vm_refl. Qed.
Lemma D_5ee08 : decode_any W_5ee08 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee0c : bv 32 := 0xfff78793.
Lemma F_5ee0c : fetch_word AsanUbsan.M.loaded_segments (0x5ee0c : word) = Some W_5ee0c.
Proof. vm_refl. Qed.
Lemma D_5ee0c : decode_any W_5ee0c = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee10 : bv 32 := 0x0037d813.
Lemma F_5ee10 : fetch_word AsanUbsan.M.loaded_segments (0x5ee10 : word) = Some W_5ee10.
Proof. vm_refl. Qed.
Lemma D_5ee10 : decode_any W_5ee10 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee14 : bv 32 := 0x00d706b3.
Lemma F_5ee14 : fetch_word AsanUbsan.M.loaded_segments (0x5ee14 : word) = Some W_5ee14.
Proof. vm_refl. Qed.
Lemma D_5ee14 : decode_any W_5ee14 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee18 : bv 32 := 0x01070733.
Lemma F_5ee18 : fetch_word AsanUbsan.M.loaded_segments (0x5ee18 : word) = Some W_5ee18.
Proof. vm_refl. Qed.
Lemma D_5ee18 : decode_any W_5ee18 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee1c : bv 32 := 0xff86f813.
Lemma F_5ee1c : fetch_word AsanUbsan.M.loaded_segments (0x5ee1c : word) = Some W_5ee1c.
Proof. vm_refl. Qed.
Lemma D_5ee1c : decode_any W_5ee1c = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee20 : bv 32 := 0xff877893.
Lemma F_5ee20 : fetch_word AsanUbsan.M.loaded_segments (0x5ee20 : word) = Some W_5ee20.
Proof. vm_refl. Qed.
Lemma D_5ee20 : decode_any W_5ee20 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee24 : bv 32 := 0x00083803.
Lemma F_5ee24 : fetch_word AsanUbsan.M.loaded_segments (0x5ee24 : word) = Some W_5ee24.
Proof. vm_refl. Qed.
Lemma D_5ee24 : decode_any W_5ee24 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee28 : bv 32 := 0x0008b883.
Lemma F_5ee28 : fetch_word AsanUbsan.M.loaded_segments (0x5ee28 : word) = Some W_5ee28.
Proof. vm_refl. Qed.
Lemma D_5ee28 : decode_any W_5ee28 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee2c : bv 32 := 0x0108e833.
Lemma F_5ee2c : fetch_word AsanUbsan.M.loaded_segments (0x5ee2c : word) = Some W_5ee2c.
Proof. vm_refl. Qed.
Lemma D_5ee2c : decode_any W_5ee2c = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee30 : bv 32 := 0x10081e63.
Lemma F_5ee30 : fetch_word AsanUbsan.M.loaded_segments (0x5ee30 : word) = Some W_5ee30.
Proof. vm_refl. Qed.
Lemma D_5ee30 : decode_any W_5ee30 = Some (Branch BC_NE 16 0 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee34 : bv 32 := 0x00079697.
Lemma F_5ee34 : fetch_word AsanUbsan.M.loaded_segments (0x5ee34 : word) = Some W_5ee34.
Proof. vm_refl. Qed.
Lemma D_5ee34 : decode_any W_5ee34 = Some (Auipc 13 121, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee38 : bv 32 := 0x5f46b683.
Lemma F_5ee38 : fetch_word AsanUbsan.M.loaded_segments (0x5ee38 : word) = Some W_5ee38.
Proof. vm_refl. Qed.
Lemma D_5ee38 : decode_any W_5ee38 = Some (Load SZ8 true 13 13 1524, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee3c : bv 32 := 0x000680e7.
Lemma F_5ee3c : fetch_word AsanUbsan.M.loaded_segments (0x5ee3c : word) = Some W_5ee3c.
Proof. vm_refl. Qed.
Lemma D_5ee3c : decode_any W_5ee3c = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee40 : bv 32 := 0x07010113.
Lemma F_5ee40 : fetch_word AsanUbsan.M.loaded_segments (0x5ee40 : word) = Some W_5ee40.
Proof. vm_refl. Qed.
Lemma D_5ee40 : decode_any W_5ee40 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee44 : bv 32 := 0x7e813083.
Lemma F_5ee44 : fetch_word AsanUbsan.M.loaded_segments (0x5ee44 : word) = Some W_5ee44.
Proof. vm_refl. Qed.
Lemma D_5ee44 : decode_any W_5ee44 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee48 : bv 32 := 0x7e013403.
Lemma F_5ee48 : fetch_word AsanUbsan.M.loaded_segments (0x5ee48 : word) = Some W_5ee48.
Proof. vm_refl. Qed.
Lemma D_5ee48 : decode_any W_5ee48 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee4c : bv 32 := 0x7d813483.
Lemma F_5ee4c : fetch_word AsanUbsan.M.loaded_segments (0x5ee4c : word) = Some W_5ee4c.
Proof. vm_refl. Qed.
Lemma D_5ee4c : decode_any W_5ee4c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee50 : bv 32 := 0x7d013903.
Lemma F_5ee50 : fetch_word AsanUbsan.M.loaded_segments (0x5ee50 : word) = Some W_5ee50.
Proof. vm_refl. Qed.
Lemma D_5ee50 : decode_any W_5ee50 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee54 : bv 32 := 0x7c813983.
Lemma F_5ee54 : fetch_word AsanUbsan.M.loaded_segments (0x5ee54 : word) = Some W_5ee54.
Proof. vm_refl. Qed.
Lemma D_5ee54 : decode_any W_5ee54 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee58 : bv 32 := 0x7c013a03.
Lemma F_5ee58 : fetch_word AsanUbsan.M.loaded_segments (0x5ee58 : word) = Some W_5ee58.
Proof. vm_refl. Qed.
Lemma D_5ee58 : decode_any W_5ee58 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee5c : bv 32 := 0x7b813a83.
Lemma F_5ee5c : fetch_word AsanUbsan.M.loaded_segments (0x5ee5c : word) = Some W_5ee5c.
Proof. vm_refl. Qed.
Lemma D_5ee5c : decode_any W_5ee5c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee60 : bv 32 := 0x7b013b03.
Lemma F_5ee60 : fetch_word AsanUbsan.M.loaded_segments (0x5ee60 : word) = Some W_5ee60.
Proof. vm_refl. Qed.
Lemma D_5ee60 : decode_any W_5ee60 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee64 : bv 32 := 0x7f010113.
Lemma F_5ee64 : fetch_word AsanUbsan.M.loaded_segments (0x5ee64 : word) = Some W_5ee64.
Proof. vm_refl. Qed.
Lemma D_5ee64 : decode_any W_5ee64 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee68 : bv 32 := 0x00008067.
Lemma F_5ee68 : fetch_word AsanUbsan.M.loaded_segments (0x5ee68 : word) = Some W_5ee68.
Proof. vm_refl. Qed.
Lemma D_5ee68 : decode_any W_5ee68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee6c : bv 32 := 0x00060913.
Lemma F_5ee6c : fetch_word AsanUbsan.M.loaded_segments (0x5ee6c : word) = Some W_5ee6c.
Proof. vm_refl. Qed.
Lemma D_5ee6c : decode_any W_5ee6c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee70 : bv 32 := 0x00058993.
Lemma F_5ee70 : fetch_word AsanUbsan.M.loaded_segments (0x5ee70 : word) = Some W_5ee70.
Proof. vm_refl. Qed.
Lemma D_5ee70 : decode_any W_5ee70 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee74 : bv 32 := 0x00050493.
Lemma F_5ee74 : fetch_word AsanUbsan.M.loaded_segments (0x5ee74 : word) = Some W_5ee74.
Proof. vm_refl. Qed.
Lemma D_5ee74 : decode_any W_5ee74 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee78 : bv 32 := 0x4dc070ef.
Lemma F_5ee78 : fetch_word AsanUbsan.M.loaded_segments (0x5ee78 : word) = Some W_5ee78.
Proof. vm_refl. Qed.
Lemma D_5ee78 : decode_any W_5ee78 = Some (Jal 1 29916, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee7c : bv 32 := 0x00098593.
Lemma F_5ee7c : fetch_word AsanUbsan.M.loaded_segments (0x5ee7c : word) = Some W_5ee7c.
Proof. vm_refl. Qed.
Lemma D_5ee7c : decode_any W_5ee7c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee80 : bv 32 := 0x00090613.
Lemma F_5ee80 : fetch_word AsanUbsan.M.loaded_segments (0x5ee80 : word) = Some W_5ee80.
Proof. vm_refl. Qed.
Lemma D_5ee80 : decode_any W_5ee80 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee84 : bv 32 := 0x00050693.
Lemma F_5ee84 : fetch_word AsanUbsan.M.loaded_segments (0x5ee84 : word) = Some W_5ee84.
Proof. vm_refl. Qed.
Lemma D_5ee84 : decode_any W_5ee84 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee88 : bv 32 := 0x00048513.
Lemma F_5ee88 : fetch_word AsanUbsan.M.loaded_segments (0x5ee88 : word) = Some W_5ee88.
Proof. vm_refl. Qed.
Lemma D_5ee88 : decode_any W_5ee88 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee8c : bv 32 := 0xfa0694e3.
Lemma F_5ee8c : fetch_word AsanUbsan.M.loaded_segments (0x5ee8c : word) = Some W_5ee8c.
Proof. vm_refl. Qed.
Lemma D_5ee8c : decode_any W_5ee8c = Some (Branch BC_NE 13 0 8104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee90 : bv 32 := 0x07010113.
Lemma F_5ee90 : fetch_word AsanUbsan.M.loaded_segments (0x5ee90 : word) = Some W_5ee90.
Proof. vm_refl. Qed.
Lemma D_5ee90 : decode_any W_5ee90 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee94 : bv 32 := 0x7e813083.
Lemma F_5ee94 : fetch_word AsanUbsan.M.loaded_segments (0x5ee94 : word) = Some W_5ee94.
Proof. vm_refl. Qed.
Lemma D_5ee94 : decode_any W_5ee94 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee98 : bv 32 := 0x7e013403.
Lemma F_5ee98 : fetch_word AsanUbsan.M.loaded_segments (0x5ee98 : word) = Some W_5ee98.
Proof. vm_refl. Qed.
Lemma D_5ee98 : decode_any W_5ee98 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee9c : bv 32 := 0x7d813483.
Lemma F_5ee9c : fetch_word AsanUbsan.M.loaded_segments (0x5ee9c : word) = Some W_5ee9c.
Proof. vm_refl. Qed.
Lemma D_5ee9c : decode_any W_5ee9c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eea0 : bv 32 := 0x7d013903.
Lemma F_5eea0 : fetch_word AsanUbsan.M.loaded_segments (0x5eea0 : word) = Some W_5eea0.
Proof. vm_refl. Qed.
Lemma D_5eea0 : decode_any W_5eea0 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eea4 : bv 32 := 0x7c813983.
Lemma F_5eea4 : fetch_word AsanUbsan.M.loaded_segments (0x5eea4 : word) = Some W_5eea4.
Proof. vm_refl. Qed.
Lemma D_5eea4 : decode_any W_5eea4 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eea8 : bv 32 := 0x7c013a03.
Lemma F_5eea8 : fetch_word AsanUbsan.M.loaded_segments (0x5eea8 : word) = Some W_5eea8.
Proof. vm_refl. Qed.
Lemma D_5eea8 : decode_any W_5eea8 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eeac : bv 32 := 0x7b813a83.
Lemma F_5eeac : fetch_word AsanUbsan.M.loaded_segments (0x5eeac : word) = Some W_5eeac.
Proof. vm_refl. Qed.
Lemma D_5eeac : decode_any W_5eeac = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eeb0 : bv 32 := 0x7b013b03.
Lemma F_5eeb0 : fetch_word AsanUbsan.M.loaded_segments (0x5eeb0 : word) = Some W_5eeb0.
Proof. vm_refl. Qed.
Lemma D_5eeb0 : decode_any W_5eeb0 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eeb4 : bv 32 := 0x7f010113.
Lemma F_5eeb4 : fetch_word AsanUbsan.M.loaded_segments (0x5eeb4 : word) = Some W_5eeb4.
Proof. vm_refl. Qed.
Lemma D_5eeb4 : decode_any W_5eeb4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eeb8 : bv 32 := 0x7281206f.
Lemma F_5eeb8 : fetch_word AsanUbsan.M.loaded_segments (0x5eeb8 : word) = Some W_5eeb8.
Proof. vm_refl. Qed.
Lemma D_5eeb8 : decode_any W_5eeb8 = Some (Jal 0 75560, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eebc : bv 32 := 0x80040693.
Lemma F_5eebc : fetch_word AsanUbsan.M.loaded_segments (0x5eebc : word) = Some W_5eebc.
Proof. vm_refl. Qed.
Lemma D_5eebc : decode_any W_5eebc = Some (OpImm ALU_ADD 13 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eec0 : bv 32 := 0xfb868693.
Lemma F_5eec0 : fetch_word AsanUbsan.M.loaded_segments (0x5eec0 : word) = Some W_5eec0.
Proof. vm_refl. Qed.
Lemma D_5eec0 : decode_any W_5eec0 = Some (OpImm ALU_ADD 13 13 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eec4 : bv 32 := 0x80040713.
Lemma F_5eec4 : fetch_word AsanUbsan.M.loaded_segments (0x5eec4 : word) = Some W_5eec4.
Proof. vm_refl. Qed.
Lemma D_5eec4 : decode_any W_5eec4 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eec8 : bv 32 := 0xfa870713.
Lemma F_5eec8 : fetch_word AsanUbsan.M.loaded_segments (0x5eec8 : word) = Some W_5eec8.
Proof. vm_refl. Qed.
Lemma D_5eec8 : decode_any W_5eec8 = Some (OpImm ALU_ADD 14 14 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eecc : bv 32 := 0x7ff70a13.
Lemma F_5eecc : fetch_word AsanUbsan.M.loaded_segments (0x5eecc : word) = Some W_5eecc.
Proof. vm_refl. Qed.
Lemma D_5eecc : decode_any W_5eecc = Some (OpImm ALU_ADD 20 14 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eed0 : bv 32 := 0x000a34a3.
Lemma F_5eed0 : fetch_word AsanUbsan.M.loaded_segments (0x5eed0 : word) = Some W_5eed0.
Proof. vm_refl. Qed.
Lemma D_5eed0 : decode_any W_5eed0 = Some (Store SZ8 20 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eed4 : bv 32 := 0x00dab023.
Lemma F_5eed4 : fetch_word AsanUbsan.M.loaded_segments (0x5eed4 : word) = Some W_5eed4.
Proof. vm_refl. Qed.
Lemma D_5eed4 : decode_any W_5eed4 = Some (Store SZ8 21 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eed8 : bv 32 := 0x000ab423.
Lemma F_5eed8 : fetch_word AsanUbsan.M.loaded_segments (0x5eed8 : word) = Some W_5eed8.
Proof. vm_refl. Qed.
Lemma D_5eed8 : decode_any W_5eed8 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eedc : bv 32 := 0x00060493.
Lemma F_5eedc : fetch_word AsanUbsan.M.loaded_segments (0x5eedc : word) = Some W_5eedc.
Proof. vm_refl. Qed.
Lemma D_5eedc : decode_any W_5eedc = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eee0 : bv 32 := 0x00058993.
Lemma F_5eee0 : fetch_word AsanUbsan.M.loaded_segments (0x5eee0 : word) = Some W_5eee0.
Proof. vm_refl. Qed.
Lemma D_5eee0 : decode_any W_5eee0 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eee4 : bv 32 := 0x00050913.
Lemma F_5eee4 : fetch_word AsanUbsan.M.loaded_segments (0x5eee4 : word) = Some W_5eee4.
Proof. vm_refl. Qed.
Lemma D_5eee4 : decode_any W_5eee4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eee8 : bv 32 := 0x3c5210ef.
Lemma F_5eee8 : fetch_word AsanUbsan.M.loaded_segments (0x5eee8 : word) = Some W_5eee8.
Proof. vm_refl. Qed.
Lemma D_5eee8 : decode_any W_5eee8 = Some (Jal 1 138180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eeec : bv 32 := 0x00050593.
Lemma F_5eeec : fetch_word AsanUbsan.M.loaded_segments (0x5eeec : word) = Some W_5eeec.
Proof. vm_refl. Qed.
Lemma D_5eeec : decode_any W_5eeec = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eef0 : bv 32 := 0x00077517.
Lemma F_5eef0 : fetch_word AsanUbsan.M.loaded_segments (0x5eef0 : word) = Some W_5eef0.
Proof. vm_refl. Qed.
Lemma D_5eef0 : decode_any W_5eef0 = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eef4 : bv 32 := 0x5c853503.
Lemma F_5eef4 : fetch_word AsanUbsan.M.loaded_segments (0x5eef4 : word) = Some W_5eef4.
Proof. vm_refl. Qed.
Lemma D_5eef4 : decode_any W_5eef4 = Some (Load SZ8 true 10 10 1480, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eef8 : bv 32 := 0x02154703.
Lemma F_5eef8 : fetch_word AsanUbsan.M.loaded_segments (0x5eef8 : word) = Some W_5eef8.
Proof. vm_refl. Qed.
Lemma D_5eef8 : decode_any W_5eef8 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eefc : bv 32 := 0x008a34a3.
Lemma F_5eefc : fetch_word AsanUbsan.M.loaded_segments (0x5eefc : word) = Some W_5eefc.
Proof. vm_refl. Qed.
Lemma D_5eefc : decode_any W_5eefc = Some (Store SZ8 20 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef00 : bv 32 := 0x80040513.
Lemma F_5ef00 : fetch_word AsanUbsan.M.loaded_segments (0x5ef00 : word) = Some W_5ef00.
Proof. vm_refl. Qed.
Lemma D_5ef00 : decode_any W_5ef00 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef04 : bv 32 := 0xfa850513.
Lemma F_5ef04 : fetch_word AsanUbsan.M.loaded_segments (0x5ef04 : word) = Some W_5ef04.
Proof. vm_refl. Qed.
Lemma D_5ef04 : decode_any W_5ef04 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef08 : bv 32 := 0x0ff00793.
Lemma F_5ef08 : fetch_word AsanUbsan.M.loaded_segments (0x5ef08 : word) = Some W_5ef08.
Proof. vm_refl. Qed.
Lemma D_5ef08 : decode_any W_5ef08 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef0c : bv 32 := 0x00040613.
Lemma F_5ef0c : fetch_word AsanUbsan.M.loaded_segments (0x5ef0c : word) = Some W_5ef0c.
Proof. vm_refl. Qed.
Lemma D_5ef0c : decode_any W_5ef0c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef10 : bv 32 := 0x00000693.
Lemma F_5ef10 : fetch_word AsanUbsan.M.loaded_segments (0x5ef10 : word) = Some W_5ef10.
Proof. vm_refl. Qed.
Lemma D_5ef10 : decode_any W_5ef10 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef14 : bv 32 := 0x0e8090ef.
Lemma F_5ef14 : fetch_word AsanUbsan.M.loaded_segments (0x5ef14 : word) = Some W_5ef14.
Proof. vm_refl. Qed.
Lemma D_5ef14 : decode_any W_5ef14 = Some (Jal 1 37096, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef18 : bv 32 := 0x80040613.
Lemma F_5ef18 : fetch_word AsanUbsan.M.loaded_segments (0x5ef18 : word) = Some W_5ef18.
Proof. vm_refl. Qed.
Lemma D_5ef18 : decode_any W_5ef18 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef1c : bv 32 := 0xfa860613.
Lemma F_5ef1c : fetch_word AsanUbsan.M.loaded_segments (0x5ef1c : word) = Some W_5ef1c.
Proof. vm_refl. Qed.
Lemma D_5ef1c : decode_any W_5ef1c = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef20 : bv 32 := 0x00090513.
Lemma F_5ef20 : fetch_word AsanUbsan.M.loaded_segments (0x5ef20 : word) = Some W_5ef20.
Proof. vm_refl. Qed.
Lemma D_5ef20 : decode_any W_5ef20 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef24 : bv 32 := 0x00048593.
Lemma F_5ef24 : fetch_word AsanUbsan.M.loaded_segments (0x5ef24 : word) = Some W_5ef24.
Proof. vm_refl. Qed.
Lemma D_5ef24 : decode_any W_5ef24 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef28 : bv 32 := 0x68d050ef.
Lemma F_5ef28 : fetch_word AsanUbsan.M.loaded_segments (0x5ef28 : word) = Some W_5ef28.
Proof. vm_refl. Qed.
Lemma D_5ef28 : decode_any W_5ef28 = Some (Jal 1 24204, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef2c : bv 32 := 0x00090513.
Lemma F_5ef2c : fetch_word AsanUbsan.M.loaded_segments (0x5ef2c : word) = Some W_5ef2c.
Proof. vm_refl. Qed.
Lemma D_5ef2c : decode_any W_5ef2c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef30 : bv 32 := 0x00098593.
Lemma F_5ef30 : fetch_word AsanUbsan.M.loaded_segments (0x5ef30 : word) = Some W_5ef30.
Proof. vm_refl. Qed.
Lemma D_5ef30 : decode_any W_5ef30 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef34 : bv 32 := 0x00048613.
Lemma F_5ef34 : fetch_word AsanUbsan.M.loaded_segments (0x5ef34 : word) = Some W_5ef34.
Proof. vm_refl. Qed.
Lemma D_5ef34 : decode_any W_5ef34 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef38 : bv 32 := 0xfbf48693.
Lemma F_5ef38 : fetch_word AsanUbsan.M.loaded_segments (0x5ef38 : word) = Some W_5ef38.
Proof. vm_refl. Qed.
Lemma D_5ef38 : decode_any W_5ef38 = Some (OpImm ALU_ADD 13 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef3c : bv 32 := 0xfbf00713.
Lemma F_5ef3c : fetch_word AsanUbsan.M.loaded_segments (0x5ef3c : word) = Some W_5ef3c.
Proof. vm_refl. Qed.
Lemma D_5ef3c : decode_any W_5ef3c = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef40 : bv 32 := 0xead76ce3.
Lemma F_5ef40 : fetch_word AsanUbsan.M.loaded_segments (0x5ef40 : word) = Some W_5ef40.
Proof. vm_refl. Qed.
Lemma D_5ef40 : decode_any W_5ef40 = Some (Branch BC_LTU 14 13 7864, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef44 : bv 32 := 0x02061e63.
Lemma F_5ef44 : fetch_word AsanUbsan.M.loaded_segments (0x5ef44 : word) = Some W_5ef44.
Proof. vm_refl. Qed.
Lemma D_5ef44 : decode_any W_5ef44 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef48 : bv 32 := 0xeedff06f.
Lemma F_5ef48 : fetch_word AsanUbsan.M.loaded_segments (0x5ef48 : word) = Some W_5ef48.
Proof. vm_refl. Qed.
Lemma D_5ef48 : decode_any W_5ef48 = Some (Jal 0 2096876, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef4c : bv 32 := 0x00070803.
Lemma F_5ef4c : fetch_word AsanUbsan.M.loaded_segments (0x5ef4c : word) = Some W_5ef4c.
Proof. vm_refl. Qed.
Lemma D_5ef4c : decode_any W_5ef4c = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef50 : bv 32 := 0x0077f793.
Lemma F_5ef50 : fetch_word AsanUbsan.M.loaded_segments (0x5ef50 : word) = Some W_5ef50.
Proof. vm_refl. Qed.
Lemma D_5ef50 : decode_any W_5ef50 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef54 : bv 32 := 0x010038b3.
Lemma F_5ef54 : fetch_word AsanUbsan.M.loaded_segments (0x5ef54 : word) = Some W_5ef54.
Proof. vm_refl. Qed.
Lemma D_5ef54 : decode_any W_5ef54 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef58 : bv 32 := 0x0107a7b3.
Lemma F_5ef58 : fetch_word AsanUbsan.M.loaded_segments (0x5ef58 : word) = Some W_5ef58.
Proof. vm_refl. Qed.
Lemma D_5ef58 : decode_any W_5ef58 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef5c : bv 32 := 0x0017c793.
Lemma F_5ef5c : fetch_word AsanUbsan.M.loaded_segments (0x5ef5c : word) = Some W_5ef5c.
Proof. vm_refl. Qed.
Lemma D_5ef5c : decode_any W_5ef5c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef60 : bv 32 := 0x00f8f7b3.
Lemma F_5ef60 : fetch_word AsanUbsan.M.loaded_segments (0x5ef60 : word) = Some W_5ef60.
Proof. vm_refl. Qed.
Lemma D_5ef60 : decode_any W_5ef60 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef64 : bv 32 := 0x00e6fa63.
Lemma F_5ef64 : fetch_word AsanUbsan.M.loaded_segments (0x5ef64 : word) = Some W_5ef64.
Proof. vm_refl. Qed.
Lemma D_5ef64 : decode_any W_5ef64 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef68 : bv 32 := 0x0006c803.
Lemma F_5ef68 : fetch_word AsanUbsan.M.loaded_segments (0x5ef68 : word) = Some W_5ef68.
Proof. vm_refl. Qed.
Lemma D_5ef68 : decode_any W_5ef68 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef6c : bv 32 := 0x00168693.
Lemma F_5ef6c : fetch_word AsanUbsan.M.loaded_segments (0x5ef6c : word) = Some W_5ef6c.
Proof. vm_refl. Qed.
Lemma D_5ef6c : decode_any W_5ef6c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef70 : bv 32 := 0x00f867b3.
Lemma F_5ef70 : fetch_word AsanUbsan.M.loaded_segments (0x5ef70 : word) = Some W_5ef70.
Proof. vm_refl. Qed.
Lemma D_5ef70 : decode_any W_5ef70 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef74 : bv 32 := 0xfee69ae3.
Lemma F_5ef74 : fetch_word AsanUbsan.M.loaded_segments (0x5ef74 : word) = Some W_5ef74.
Proof. vm_refl. Qed.
Lemma D_5ef74 : decode_any W_5ef74 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef78 : bv 32 := 0x0ff7f693.
Lemma F_5ef78 : fetch_word AsanUbsan.M.loaded_segments (0x5ef78 : word) = Some W_5ef78.
Proof. vm_refl. Qed.
Lemma D_5ef78 : decode_any W_5ef78 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef7c : bv 32 := 0xea068ce3.
Lemma F_5ef7c : fetch_word AsanUbsan.M.loaded_segments (0x5ef7c : word) = Some W_5ef7c.
Proof. vm_refl. Qed.
Lemma D_5ef7c : decode_any W_5ef7c = Some (Branch BC_EQ 13 0 7864, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef80 : bv 32 := 0x00050493.
Lemma F_5ef80 : fetch_word AsanUbsan.M.loaded_segments (0x5ef80 : word) = Some W_5ef80.
Proof. vm_refl. Qed.
Lemma D_5ef80 : decode_any W_5ef80 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef84 : bv 32 := 0x00058b13.
Lemma F_5ef84 : fetch_word AsanUbsan.M.loaded_segments (0x5ef84 : word) = Some W_5ef84.
Proof. vm_refl. Qed.
Lemma D_5ef84 : decode_any W_5ef84 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef88 : bv 32 := 0x00060593.
Lemma F_5ef88 : fetch_word AsanUbsan.M.loaded_segments (0x5ef88 : word) = Some W_5ef88.
Proof. vm_refl. Qed.
Lemma D_5ef88 : decode_any W_5ef88 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef8c : bv 32 := 0x00060913.
Lemma F_5ef8c : fetch_word AsanUbsan.M.loaded_segments (0x5ef8c : word) = Some W_5ef8c.
Proof. vm_refl. Qed.
Lemma D_5ef8c : decode_any W_5ef8c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef90 : bv 32 := 0x3f1020ef.
Lemma F_5ef90 : fetch_word AsanUbsan.M.loaded_segments (0x5ef90 : word) = Some W_5ef90.
Proof. vm_refl. Qed.
Lemma D_5ef90 : decode_any W_5ef90 = Some (Jal 1 11248, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef94 : bv 32 := 0x000b0593.
Lemma F_5ef94 : fetch_word AsanUbsan.M.loaded_segments (0x5ef94 : word) = Some W_5ef94.
Proof. vm_refl. Qed.
Lemma D_5ef94 : decode_any W_5ef94 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef98 : bv 32 := 0x00090613.
Lemma F_5ef98 : fetch_word AsanUbsan.M.loaded_segments (0x5ef98 : word) = Some W_5ef98.
Proof. vm_refl. Qed.
Lemma D_5ef98 : decode_any W_5ef98 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef9c : bv 32 := 0x00050993.
Lemma F_5ef9c : fetch_word AsanUbsan.M.loaded_segments (0x5ef9c : word) = Some W_5ef9c.
Proof. vm_refl. Qed.
Lemma D_5ef9c : decode_any W_5ef9c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efa0 : bv 32 := 0x00048513.
Lemma F_5efa0 : fetch_word AsanUbsan.M.loaded_segments (0x5efa0 : word) = Some W_5efa0.
Proof. vm_refl. Qed.
Lemma D_5efa0 : decode_any W_5efa0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efa4 : bv 32 := 0xe80988e3.
Lemma F_5efa4 : fetch_word AsanUbsan.M.loaded_segments (0x5efa4 : word) = Some W_5efa4.
Proof. vm_refl. Qed.
Lemma D_5efa4 : decode_any W_5efa4 = Some (Branch BC_EQ 19 0 7824, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efa8 : bv 32 := 0xfffbb517.
Lemma F_5efa8 : fetch_word AsanUbsan.M.loaded_segments (0x5efa8 : word) = Some W_5efa8.
Proof. vm_refl. Qed.
Lemma D_5efa8 : decode_any W_5efa8 = Some (Auipc 10 1048507, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efac : bv 32 := 0x96450513.
Lemma F_5efac : fetch_word AsanUbsan.M.loaded_segments (0x5efac : word) = Some W_5efac.
Proof. vm_refl. Qed.
Lemma D_5efac : decode_any W_5efac = Some (OpImm ALU_ADD 10 10 2404, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efb0 : bv 32 := 0x7f9090ef.
Lemma F_5efb0 : fetch_word AsanUbsan.M.loaded_segments (0x5efb0 : word) = Some W_5efb0.
Proof. vm_refl. Qed.
Lemma D_5efb0 : decode_any W_5efb0 = Some (Jal 1 40952, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efb4 : bv 32 := 0x000b0593.
Lemma F_5efb4 : fetch_word AsanUbsan.M.loaded_segments (0x5efb4 : word) = Some W_5efb4.
Proof. vm_refl. Qed.
Lemma D_5efb4 : decode_any W_5efb4 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efb8 : bv 32 := 0x00090613.
Lemma F_5efb8 : fetch_word AsanUbsan.M.loaded_segments (0x5efb8 : word) = Some W_5efb8.
Proof. vm_refl. Qed.
Lemma D_5efb8 : decode_any W_5efb8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efbc : bv 32 := 0x00050693.
Lemma F_5efbc : fetch_word AsanUbsan.M.loaded_segments (0x5efbc : word) = Some W_5efbc.
Proof. vm_refl. Qed.
Lemma D_5efbc : decode_any W_5efbc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efc0 : bv 32 := 0x00048513.
Lemma F_5efc0 : fetch_word AsanUbsan.M.loaded_segments (0x5efc0 : word) = Some W_5efc0.
Proof. vm_refl. Qed.
Lemma D_5efc0 : decode_any W_5efc0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efc4 : bv 32 := 0xe60698e3.
Lemma F_5efc4 : fetch_word AsanUbsan.M.loaded_segments (0x5efc4 : word) = Some W_5efc4.
Proof. vm_refl. Qed.
Lemma D_5efc4 : decode_any W_5efc4 = Some (Branch BC_NE 13 0 7792, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efc8 : bv 32 := 0x0480a0ef.
Lemma F_5efc8 : fetch_word AsanUbsan.M.loaded_segments (0x5efc8 : word) = Some W_5efc8.
Proof. vm_refl. Qed.
Lemma D_5efc8 : decode_any W_5efc8 = Some (Jal 1 41032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efcc : bv 32 := 0x06050e63.
Lemma F_5efcc : fetch_word AsanUbsan.M.loaded_segments (0x5efcc : word) = Some W_5efcc.
Proof. vm_refl. Qed.
Lemma D_5efcc : decode_any W_5efcc = Some (Branch BC_EQ 10 0 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efd0 : bv 32 := 0x80040513.
Lemma F_5efd0 : fetch_word AsanUbsan.M.loaded_segments (0x5efd0 : word) = Some W_5efd0.
Proof. vm_refl. Qed.
Lemma D_5efd0 : decode_any W_5efd0 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efd4 : bv 32 := 0xfb850513.
Lemma F_5efd4 : fetch_word AsanUbsan.M.loaded_segments (0x5efd4 : word) = Some W_5efd4.
Proof. vm_refl. Qed.
Lemma D_5efd4 : decode_any W_5efd4 = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efd8 : bv 32 := 0x80040593.
Lemma F_5efd8 : fetch_word AsanUbsan.M.loaded_segments (0x5efd8 : word) = Some W_5efd8.
Proof. vm_refl. Qed.
Lemma D_5efd8 : decode_any W_5efd8 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efdc : bv 32 := 0xfa858593.
Lemma F_5efdc : fetch_word AsanUbsan.M.loaded_segments (0x5efdc : word) = Some W_5efdc.
Proof. vm_refl. Qed.
Lemma D_5efdc : decode_any W_5efdc = Some (OpImm ALU_ADD 11 11 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efe0 : bv 32 := 0x7ff58a13.
Lemma F_5efe0 : fetch_word AsanUbsan.M.loaded_segments (0x5efe0 : word) = Some W_5efe0.
Proof. vm_refl. Qed.
Lemma D_5efe0 : decode_any W_5efe0 = Some (OpImm ALU_ADD 20 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efe4 : bv 32 := 0x000a34a3.
Lemma F_5efe4 : fetch_word AsanUbsan.M.loaded_segments (0x5efe4 : word) = Some W_5efe4.
Proof. vm_refl. Qed.
Lemma D_5efe4 : decode_any W_5efe4 = Some (Store SZ8 20 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efe8 : bv 32 := 0x00aab023.
Lemma F_5efe8 : fetch_word AsanUbsan.M.loaded_segments (0x5efe8 : word) = Some W_5efe8.
Proof. vm_refl. Qed.
Lemma D_5efe8 : decode_any W_5efe8 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efec : bv 32 := 0x000ab423.
Lemma F_5efec : fetch_word AsanUbsan.M.loaded_segments (0x5efec : word) = Some W_5efec.
Proof. vm_refl. Qed.
Lemma D_5efec : decode_any W_5efec = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eff0 : bv 32 := 0x2bd210ef.
Lemma F_5eff0 : fetch_word AsanUbsan.M.loaded_segments (0x5eff0 : word) = Some W_5eff0.
Proof. vm_refl. Qed.
Lemma D_5eff0 : decode_any W_5eff0 = Some (Jal 1 137916, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eff4 : bv 32 := 0x00050593.
Lemma F_5eff4 : fetch_word AsanUbsan.M.loaded_segments (0x5eff4 : word) = Some W_5eff4.
Proof. vm_refl. Qed.
Lemma D_5eff4 : decode_any W_5eff4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eff8 : bv 32 := 0x00077517.
Lemma F_5eff8 : fetch_word AsanUbsan.M.loaded_segments (0x5eff8 : word) = Some W_5eff8.
Proof. vm_refl. Qed.
Lemma D_5eff8 : decode_any W_5eff8 = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5effc : bv 32 := 0x4c053503.
Lemma F_5effc : fetch_word AsanUbsan.M.loaded_segments (0x5effc : word) = Some W_5effc.
Proof. vm_refl. Qed.
Lemma D_5effc : decode_any W_5effc = Some (Load SZ8 true 10 10 1216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f000 : bv 32 := 0x02154703.
Lemma F_5f000 : fetch_word AsanUbsan.M.loaded_segments (0x5f000 : word) = Some W_5f000.
Proof. vm_refl. Qed.
Lemma D_5f000 : decode_any W_5f000 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f004 : bv 32 := 0x008a34a3.
Lemma F_5f004 : fetch_word AsanUbsan.M.loaded_segments (0x5f004 : word) = Some W_5f004.
Proof. vm_refl. Qed.
Lemma D_5f004 : decode_any W_5f004 = Some (Store SZ8 20 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f008 : bv 32 := 0x80040513.
Lemma F_5f008 : fetch_word AsanUbsan.M.loaded_segments (0x5f008 : word) = Some W_5f008.
Proof. vm_refl. Qed.
Lemma D_5f008 : decode_any W_5f008 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f00c : bv 32 := 0xfa850513.
Lemma F_5f00c : fetch_word AsanUbsan.M.loaded_segments (0x5f00c : word) = Some W_5f00c.
Proof. vm_refl. Qed.
Lemma D_5f00c : decode_any W_5f00c = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f010 : bv 32 := 0x0ff00793.
Lemma F_5f010 : fetch_word AsanUbsan.M.loaded_segments (0x5f010 : word) = Some W_5f010.
Proof. vm_refl. Qed.
Lemma D_5f010 : decode_any W_5f010 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f014 : bv 32 := 0x00040613.
Lemma F_5f014 : fetch_word AsanUbsan.M.loaded_segments (0x5f014 : word) = Some W_5f014.
Proof. vm_refl. Qed.
Lemma D_5f014 : decode_any W_5f014 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f018 : bv 32 := 0x00000693.
Lemma F_5f018 : fetch_word AsanUbsan.M.loaded_segments (0x5f018 : word) = Some W_5f018.
Proof. vm_refl. Qed.
Lemma D_5f018 : decode_any W_5f018 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f01c : bv 32 := 0x7e1080ef.
Lemma F_5f01c : fetch_word AsanUbsan.M.loaded_segments (0x5f01c : word) = Some W_5f01c.
Proof. vm_refl. Qed.
Lemma D_5f01c : decode_any W_5f01c = Some (Jal 1 36832, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f020 : bv 32 := 0x80040513.
Lemma F_5f020 : fetch_word AsanUbsan.M.loaded_segments (0x5f020 : word) = Some W_5f020.
Proof. vm_refl. Qed.
Lemma D_5f020 : decode_any W_5f020 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f024 : bv 32 := 0xfa850513.
Lemma F_5f024 : fetch_word AsanUbsan.M.loaded_segments (0x5f024 : word) = Some W_5f024.
Proof. vm_refl. Qed.
Lemma D_5f024 : decode_any W_5f024 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f028 : bv 32 := 0x2f00a0ef.
Lemma F_5f028 : fetch_word AsanUbsan.M.loaded_segments (0x5f028 : word) = Some W_5f028.
Proof. vm_refl. Qed.
Lemma D_5f028 : decode_any W_5f028 = Some (Jal 1 41712, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f02c : bv 32 := 0x00050693.
Lemma F_5f02c : fetch_word AsanUbsan.M.loaded_segments (0x5f02c : word) = Some W_5f02c.
Proof. vm_refl. Qed.
Lemma D_5f02c : decode_any W_5f02c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f030 : bv 32 := 0x00040a13.
Lemma F_5f030 : fetch_word AsanUbsan.M.loaded_segments (0x5f030 : word) = Some W_5f030.
Proof. vm_refl. Qed.
Lemma D_5f030 : decode_any W_5f030 = Some (OpImm ALU_ADD 20 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f034 : bv 32 := 0x00090613.
Lemma F_5f034 : fetch_word AsanUbsan.M.loaded_segments (0x5f034 : word) = Some W_5f034.
Proof. vm_refl. Qed.
Lemma D_5f034 : decode_any W_5f034 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f038 : bv 32 := 0x000b0593.
Lemma F_5f038 : fetch_word AsanUbsan.M.loaded_segments (0x5f038 : word) = Some W_5f038.
Proof. vm_refl. Qed.
Lemma D_5f038 : decode_any W_5f038 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f03c : bv 32 := 0x00048513.
Lemma F_5f03c : fetch_word AsanUbsan.M.loaded_segments (0x5f03c : word) = Some W_5f03c.
Proof. vm_refl. Qed.
Lemma D_5f03c : decode_any W_5f03c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f040 : bv 32 := 0xde069ae3.
Lemma F_5f040 : fetch_word AsanUbsan.M.loaded_segments (0x5f040 : word) = Some W_5f040.
Proof. vm_refl. Qed.
Lemma D_5f040 : decode_any W_5f040 = Some (Branch BC_NE 13 0 7668, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f044 : bv 32 := 0x0080006f.
Lemma F_5f044 : fetch_word AsanUbsan.M.loaded_segments (0x5f044 : word) = Some W_5f044.
Proof. vm_refl. Qed.
Lemma D_5f044 : decode_any W_5f044 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f048 : bv 32 := 0x00040a13.
Lemma F_5f048 : fetch_word AsanUbsan.M.loaded_segments (0x5f048 : word) = Some W_5f048.
Proof. vm_refl. Qed.
Lemma D_5f048 : decode_any W_5f048 = Some (OpImm ALU_ADD 20 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f04c : bv 32 := 0x261210ef.
Lemma F_5f04c : fetch_word AsanUbsan.M.loaded_segments (0x5f04c : word) = Some W_5f04c.
Proof. vm_refl. Qed.
Lemma D_5f04c : decode_any W_5f04c = Some (Jal 1 137824, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f050 : bv 32 := 0xfffb1597.
Lemma F_5f050 : fetch_word AsanUbsan.M.loaded_segments (0x5f050 : word) = Some W_5f050.
Proof. vm_refl. Qed.
Lemma D_5f050 : decode_any W_5f050 = Some (Auipc 11 1048497, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f054 : bv 32 := 0x3b85b583.
Lemma F_5f054 : fetch_word AsanUbsan.M.loaded_segments (0x5f054 : word) = Some W_5f054.
Proof. vm_refl. Qed.
Lemma D_5f054 : decode_any W_5f054 = Some (Load SZ8 true 11 11 952, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f058 : bv 32 := 0x00bab023.
Lemma F_5f058 : fetch_word AsanUbsan.M.loaded_segments (0x5f058 : word) = Some W_5f058.
Proof. vm_refl. Qed.
Lemma D_5f058 : decode_any W_5f058 = Some (Store SZ8 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f05c : bv 32 := 0x80040613.
Lemma F_5f05c : fetch_word AsanUbsan.M.loaded_segments (0x5f05c : word) = Some W_5f05c.
Proof. vm_refl. Qed.
Lemma D_5f05c : decode_any W_5f05c = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f060 : bv 32 := 0xfa860613.
Lemma F_5f060 : fetch_word AsanUbsan.M.loaded_segments (0x5f060 : word) = Some W_5f060.
Proof. vm_refl. Qed.
Lemma D_5f060 : decode_any W_5f060 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f064 : bv 32 := 0x00100713.
Lemma F_5f064 : fetch_word AsanUbsan.M.loaded_segments (0x5f064 : word) = Some W_5f064.
Proof. vm_refl. Qed.
Lemma D_5f064 : decode_any W_5f064 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f068 : bv 32 := 0x000a0593.
Lemma F_5f068 : fetch_word AsanUbsan.M.loaded_segments (0x5f068 : word) = Some W_5f068.
Proof. vm_refl. Qed.
Lemma D_5f068 : decode_any W_5f068 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f06c : bv 32 := 0x00098693.
Lemma F_5f06c : fetch_word AsanUbsan.M.loaded_segments (0x5f06c : word) = Some W_5f06c.
Proof. vm_refl. Qed.
Lemma D_5f06c : decode_any W_5f06c = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f070 : bv 32 := 0x00090793.
Lemma F_5f070 : fetch_word AsanUbsan.M.loaded_segments (0x5f070 : word) = Some W_5f070.
Proof. vm_refl. Qed.
Lemma D_5f070 : decode_any W_5f070 = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f074 : bv 32 := 0x00000813.
Lemma F_5f074 : fetch_word AsanUbsan.M.loaded_segments (0x5f074 : word) = Some W_5f074.
Proof. vm_refl. Qed.
Lemma D_5f074 : decode_any W_5f074 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f078 : bv 32 := 0x00000893.
Lemma F_5f078 : fetch_word AsanUbsan.M.loaded_segments (0x5f078 : word) = Some W_5f078.
Proof. vm_refl. Qed.
Lemma D_5f078 : decode_any W_5f078 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f07c : bv 32 := 0x290060ef.
Lemma F_5f07c : fetch_word AsanUbsan.M.loaded_segments (0x5f07c : word) = Some W_5f07c.
Proof. vm_refl. Qed.
Lemma D_5f07c : decode_any W_5f07c = Some (Jal 1 25232, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f080 : bv 32 := 0x00048513.
Lemma F_5f080 : fetch_word AsanUbsan.M.loaded_segments (0x5f080 : word) = Some W_5f080.
Proof. vm_refl. Qed.
Lemma D_5f080 : decode_any W_5f080 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f084 : bv 32 := 0x000b0593.
Lemma F_5f084 : fetch_word AsanUbsan.M.loaded_segments (0x5f084 : word) = Some W_5f084.
Proof. vm_refl. Qed.
Lemma D_5f084 : decode_any W_5f084 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f088 : bv 32 := 0x00090613.
Lemma F_5f088 : fetch_word AsanUbsan.M.loaded_segments (0x5f088 : word) = Some W_5f088.
Proof. vm_refl. Qed.
Lemma D_5f088 : decode_any W_5f088 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f08c : bv 32 := 0xda9ff06f.
Lemma F_5f08c : fetch_word AsanUbsan.M.loaded_segments (0x5f08c : word) = Some W_5f08c.
Proof. vm_refl. Qed.
Lemma D_5f08c : decode_any W_5f08c = Some (Jal 0 2096552, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f090 : bv 32 := 0x81010113.
Lemma F_5f090 : fetch_word AsanUbsan.M.loaded_segments (0x5f090 : word) = Some W_5f090.
Proof. vm_refl. Qed.
Lemma D_5f090 : decode_any W_5f090 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f094 : bv 32 := 0x7e113423.
Lemma F_5f094 : fetch_word AsanUbsan.M.loaded_segments (0x5f094 : word) = Some W_5f094.
Proof. vm_refl. Qed.
Lemma D_5f094 : decode_any W_5f094 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f098 : bv 32 := 0x7e813023.
Lemma F_5f098 : fetch_word AsanUbsan.M.loaded_segments (0x5f098 : word) = Some W_5f098.
Proof. vm_refl. Qed.
Lemma D_5f098 : decode_any W_5f098 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f09c : bv 32 := 0x7c913c23.
Lemma F_5f09c : fetch_word AsanUbsan.M.loaded_segments (0x5f09c : word) = Some W_5f09c.
Proof. vm_refl. Qed.
Lemma D_5f09c : decode_any W_5f09c = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0a0 : bv 32 := 0x7d213823.
Lemma F_5f0a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f0a0 : word) = Some W_5f0a0.
Proof. vm_refl. Qed.
Lemma D_5f0a0 : decode_any W_5f0a0 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0a4 : bv 32 := 0x7d313423.
Lemma F_5f0a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f0a4 : word) = Some W_5f0a4.
Proof. vm_refl. Qed.
Lemma D_5f0a4 : decode_any W_5f0a4 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0a8 : bv 32 := 0x7d413023.
Lemma F_5f0a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f0a8 : word) = Some W_5f0a8.
Proof. vm_refl. Qed.
Lemma D_5f0a8 : decode_any W_5f0a8 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0ac : bv 32 := 0x7b513c23.
Lemma F_5f0ac : fetch_word AsanUbsan.M.loaded_segments (0x5f0ac : word) = Some W_5f0ac.
Proof. vm_refl. Qed.
Lemma D_5f0ac : decode_any W_5f0ac = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0b0 : bv 32 := 0x7b613823.
Lemma F_5f0b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f0b0 : word) = Some W_5f0b0.
Proof. vm_refl. Qed.
Lemma D_5f0b0 : decode_any W_5f0b0 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0b4 : bv 32 := 0x7b713423.
Lemma F_5f0b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f0b4 : word) = Some W_5f0b4.
Proof. vm_refl. Qed.
Lemma D_5f0b4 : decode_any W_5f0b4 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0b8 : bv 32 := 0x7f010413.
Lemma F_5f0b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f0b8 : word) = Some W_5f0b8.
Proof. vm_refl. Qed.
Lemma D_5f0b8 : decode_any W_5f0b8 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0bc : bv 32 := 0xf9010113.
Lemma F_5f0bc : fetch_word AsanUbsan.M.loaded_segments (0x5f0bc : word) = Some W_5f0bc.
Proof. vm_refl. Qed.
Lemma D_5f0bc : decode_any W_5f0bc = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0c0 : bv 32 := 0x00078697.
Lemma F_5f0c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f0c0 : word) = Some W_5f0c0.
Proof. vm_refl. Qed.
Lemma D_5f0c0 : decode_any W_5f0c0 = Some (Auipc 13 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0c4 : bv 32 := 0xf706b683.
Lemma F_5f0c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f0c4 : word) = Some W_5f0c4.
Proof. vm_refl. Qed.
Lemma D_5f0c4 : decode_any W_5f0c4 = Some (Load SZ8 true 13 13 3952, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0c8 : bv 32 := 0x0006c683.
Lemma F_5f0c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f0c8 : word) = Some W_5f0c8.
Proof. vm_refl. Qed.
Lemma D_5f0c8 : decode_any W_5f0c8 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0cc : bv 32 := 0x0a068463.
Lemma F_5f0cc : fetch_word AsanUbsan.M.loaded_segments (0x5f0cc : word) = Some W_5f0cc.
Proof. vm_refl. Qed.
Lemma D_5f0cc : decode_any W_5f0cc = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0d0 : bv 32 := 0xfff5c693.
Lemma F_5f0d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f0d0 : word) = Some W_5f0d0.
Proof. vm_refl. Qed.
Lemma D_5f0d0 : decode_any W_5f0d0 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0d4 : bv 32 := 0x80040a93.
Lemma F_5f0d4 : fetch_word AsanUbsan.M.loaded_segments (0x5f0d4 : word) = Some W_5f0d4.
Proof. vm_refl. Qed.
Lemma D_5f0d4 : decode_any W_5f0d4 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0d8 : bv 32 := 0xfa0a8a93.
Lemma F_5f0d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f0d8 : word) = Some W_5f0d8.
Proof. vm_refl. Qed.
Lemma D_5f0d8 : decode_any W_5f0d8 = Some (OpImm ALU_ADD 21 21 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0dc : bv 32 := 0x0cc6e663.
Lemma F_5f0dc : fetch_word AsanUbsan.M.loaded_segments (0x5f0dc : word) = Some W_5f0dc.
Proof. vm_refl. Qed.
Lemma D_5f0dc : decode_any W_5f0dc = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0e0 : bv 32 := 0xfbf60a13.
Lemma F_5f0e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f0e0 : word) = Some W_5f0e0.
Proof. vm_refl. Qed.
Lemma D_5f0e0 : decode_any W_5f0e0 = Some (OpImm ALU_ADD 20 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0e4 : bv 32 := 0xfbf00693.
Lemma F_5f0e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f0e4 : word) = Some W_5f0e4.
Proof. vm_refl. Qed.
Lemma D_5f0e4 : decode_any W_5f0e4 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0e8 : bv 32 := 0x1546f463.
Lemma F_5f0e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f0e8 : word) = Some W_5f0e8.
Proof. vm_refl. Qed.
Lemma D_5f0e8 : decode_any W_5f0e8 = Some (Branch BC_GEU 13 20 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0ec : bv 32 := 0x00077697.
Lemma F_5f0ec : fetch_word AsanUbsan.M.loaded_segments (0x5f0ec : word) = Some W_5f0ec.
Proof. vm_refl. Qed.
Lemma D_5f0ec : decode_any W_5f0ec = Some (Auipc 13 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0f0 : bv 32 := 0x3dc6b683.
Lemma F_5f0f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f0f0 : word) = Some W_5f0f0.
Proof. vm_refl. Qed.
Lemma D_5f0f0 : decode_any W_5f0f0 = Some (Load SZ8 true 13 13 988, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0f4 : bv 32 := 0x00c587b3.
Lemma F_5f0f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f0f4 : word) = Some W_5f0f4.
Proof. vm_refl. Qed.
Lemma D_5f0f4 : decode_any W_5f0f4 = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0f8 : bv 32 := 0x0006b703.
Lemma F_5f0f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f0f8 : word) = Some W_5f0f8.
Proof. vm_refl. Qed.
Lemma D_5f0f8 : decode_any W_5f0f8 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0fc : bv 32 := 0x0035d693.
Lemma F_5f0fc : fetch_word AsanUbsan.M.loaded_segments (0x5f0fc : word) = Some W_5f0fc.
Proof. vm_refl. Qed.
Lemma D_5f0fc : decode_any W_5f0fc = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f100 : bv 32 := 0xfff78793.
Lemma F_5f100 : fetch_word AsanUbsan.M.loaded_segments (0x5f100 : word) = Some W_5f100.
Proof. vm_refl. Qed.
Lemma D_5f100 : decode_any W_5f100 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f104 : bv 32 := 0x0037d813.
Lemma F_5f104 : fetch_word AsanUbsan.M.loaded_segments (0x5f104 : word) = Some W_5f104.
Proof. vm_refl. Qed.
Lemma D_5f104 : decode_any W_5f104 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f108 : bv 32 := 0x00d706b3.
Lemma F_5f108 : fetch_word AsanUbsan.M.loaded_segments (0x5f108 : word) = Some W_5f108.
Proof. vm_refl. Qed.
Lemma D_5f108 : decode_any W_5f108 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f10c : bv 32 := 0x01070733.
Lemma F_5f10c : fetch_word AsanUbsan.M.loaded_segments (0x5f10c : word) = Some W_5f10c.
Proof. vm_refl. Qed.
Lemma D_5f10c : decode_any W_5f10c = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f110 : bv 32 := 0xff86f813.
Lemma F_5f110 : fetch_word AsanUbsan.M.loaded_segments (0x5f110 : word) = Some W_5f110.
Proof. vm_refl. Qed.
Lemma D_5f110 : decode_any W_5f110 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f114 : bv 32 := 0xff877893.
Lemma F_5f114 : fetch_word AsanUbsan.M.loaded_segments (0x5f114 : word) = Some W_5f114.
Proof. vm_refl. Qed.
Lemma D_5f114 : decode_any W_5f114 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f118 : bv 32 := 0x00083803.
Lemma F_5f118 : fetch_word AsanUbsan.M.loaded_segments (0x5f118 : word) = Some W_5f118.
Proof. vm_refl. Qed.
Lemma D_5f118 : decode_any W_5f118 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f11c : bv 32 := 0x0008b883.
Lemma F_5f11c : fetch_word AsanUbsan.M.loaded_segments (0x5f11c : word) = Some W_5f11c.
Proof. vm_refl. Qed.
Lemma D_5f11c : decode_any W_5f11c = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f120 : bv 32 := 0x0108e833.
Lemma F_5f120 : fetch_word AsanUbsan.M.loaded_segments (0x5f120 : word) = Some W_5f120.
Proof. vm_refl. Qed.
Lemma D_5f120 : decode_any W_5f120 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f124 : bv 32 := 0x1a081063.
Lemma F_5f124 : fetch_word AsanUbsan.M.loaded_segments (0x5f124 : word) = Some W_5f124.
Proof. vm_refl. Qed.
Lemma D_5f124 : decode_any W_5f124 = Some (Branch BC_NE 16 0 416, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f128 : bv 32 := 0xfff54693.
Lemma F_5f128 : fetch_word AsanUbsan.M.loaded_segments (0x5f128 : word) = Some W_5f128.
Proof. vm_refl. Qed.
Lemma D_5f128 : decode_any W_5f128 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f12c : bv 32 := 0x10c6e663.
Lemma F_5f12c : fetch_word AsanUbsan.M.loaded_segments (0x5f12c : word) = Some W_5f12c.
Proof. vm_refl. Qed.
Lemma D_5f12c : decode_any W_5f12c = Some (Branch BC_LTU 13 12 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f130 : bv 32 := 0xfbf00693.
Lemma F_5f130 : fetch_word AsanUbsan.M.loaded_segments (0x5f130 : word) = Some W_5f130.
Proof. vm_refl. Qed.
Lemma D_5f130 : decode_any W_5f130 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f134 : bv 32 := 0x1946f463.
Lemma F_5f134 : fetch_word AsanUbsan.M.loaded_segments (0x5f134 : word) = Some W_5f134.
Proof. vm_refl. Qed.
Lemma D_5f134 : decode_any W_5f134 = Some (Branch BC_GEU 13 20 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f138 : bv 32 := 0x00077697.
Lemma F_5f138 : fetch_word AsanUbsan.M.loaded_segments (0x5f138 : word) = Some W_5f138.
Proof. vm_refl. Qed.
Lemma D_5f138 : decode_any W_5f138 = Some (Auipc 13 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f13c : bv 32 := 0x3906b683.
Lemma F_5f13c : fetch_word AsanUbsan.M.loaded_segments (0x5f13c : word) = Some W_5f13c.
Proof. vm_refl. Qed.
Lemma D_5f13c : decode_any W_5f13c = Some (Load SZ8 true 13 13 912, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f140 : bv 32 := 0x00c507b3.
Lemma F_5f140 : fetch_word AsanUbsan.M.loaded_segments (0x5f140 : word) = Some W_5f140.
Proof. vm_refl. Qed.
Lemma D_5f140 : decode_any W_5f140 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f144 : bv 32 := 0x0006b703.
Lemma F_5f144 : fetch_word AsanUbsan.M.loaded_segments (0x5f144 : word) = Some W_5f144.
Proof. vm_refl. Qed.
Lemma D_5f144 : decode_any W_5f144 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f148 : bv 32 := 0x00355693.
Lemma F_5f148 : fetch_word AsanUbsan.M.loaded_segments (0x5f148 : word) = Some W_5f148.
Proof. vm_refl. Qed.
Lemma D_5f148 : decode_any W_5f148 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f14c : bv 32 := 0xfff78793.
Lemma F_5f14c : fetch_word AsanUbsan.M.loaded_segments (0x5f14c : word) = Some W_5f14c.
Proof. vm_refl. Qed.
Lemma D_5f14c : decode_any W_5f14c = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f150 : bv 32 := 0x0037d813.
Lemma F_5f150 : fetch_word AsanUbsan.M.loaded_segments (0x5f150 : word) = Some W_5f150.
Proof. vm_refl. Qed.
Lemma D_5f150 : decode_any W_5f150 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f154 : bv 32 := 0x00d706b3.
Lemma F_5f154 : fetch_word AsanUbsan.M.loaded_segments (0x5f154 : word) = Some W_5f154.
Proof. vm_refl. Qed.
Lemma D_5f154 : decode_any W_5f154 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f158 : bv 32 := 0x01070733.
Lemma F_5f158 : fetch_word AsanUbsan.M.loaded_segments (0x5f158 : word) = Some W_5f158.
Proof. vm_refl. Qed.
Lemma D_5f158 : decode_any W_5f158 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f15c : bv 32 := 0xff86f813.
Lemma F_5f15c : fetch_word AsanUbsan.M.loaded_segments (0x5f15c : word) = Some W_5f15c.
Proof. vm_refl. Qed.
Lemma D_5f15c : decode_any W_5f15c = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f160 : bv 32 := 0xff877893.
Lemma F_5f160 : fetch_word AsanUbsan.M.loaded_segments (0x5f160 : word) = Some W_5f160.
Proof. vm_refl. Qed.
Lemma D_5f160 : decode_any W_5f160 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f164 : bv 32 := 0x00083803.
Lemma F_5f164 : fetch_word AsanUbsan.M.loaded_segments (0x5f164 : word) = Some W_5f164.
Proof. vm_refl. Qed.
Lemma D_5f164 : decode_any W_5f164 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f168 : bv 32 := 0x0008b883.
Lemma F_5f168 : fetch_word AsanUbsan.M.loaded_segments (0x5f168 : word) = Some W_5f168.
Proof. vm_refl. Qed.
Lemma D_5f168 : decode_any W_5f168 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f16c : bv 32 := 0x0108e833.
Lemma F_5f16c : fetch_word AsanUbsan.M.loaded_segments (0x5f16c : word) = Some W_5f16c.
Proof. vm_refl. Qed.
Lemma D_5f16c : decode_any W_5f16c = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f170 : bv 32 := 0x24081a63.
Lemma F_5f170 : fetch_word AsanUbsan.M.loaded_segments (0x5f170 : word) = Some W_5f170.
Proof. vm_refl. Qed.
Lemma D_5f170 : decode_any W_5f170 = Some (Branch BC_NE 16 0 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f174 : bv 32 := 0x414120ef.
Lemma F_5f174 : fetch_word AsanUbsan.M.loaded_segments (0x5f174 : word) = Some W_5f174.
Proof. vm_refl. Qed.
Lemma D_5f174 : decode_any W_5f174 = Some (Jal 1 74772, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f178 : bv 32 := 0x07010113.
Lemma F_5f178 : fetch_word AsanUbsan.M.loaded_segments (0x5f178 : word) = Some W_5f178.
Proof. vm_refl. Qed.
Lemma D_5f178 : decode_any W_5f178 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f17c : bv 32 := 0x7e813083.
Lemma F_5f17c : fetch_word AsanUbsan.M.loaded_segments (0x5f17c : word) = Some W_5f17c.
Proof. vm_refl. Qed.
Lemma D_5f17c : decode_any W_5f17c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f180 : bv 32 := 0x7e013403.
Lemma F_5f180 : fetch_word AsanUbsan.M.loaded_segments (0x5f180 : word) = Some W_5f180.
Proof. vm_refl. Qed.
Lemma D_5f180 : decode_any W_5f180 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f184 : bv 32 := 0x7d813483.
Lemma F_5f184 : fetch_word AsanUbsan.M.loaded_segments (0x5f184 : word) = Some W_5f184.
Proof. vm_refl. Qed.
Lemma D_5f184 : decode_any W_5f184 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f188 : bv 32 := 0x7d013903.
Lemma F_5f188 : fetch_word AsanUbsan.M.loaded_segments (0x5f188 : word) = Some W_5f188.
Proof. vm_refl. Qed.
Lemma D_5f188 : decode_any W_5f188 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f18c : bv 32 := 0x7c813983.
Lemma F_5f18c : fetch_word AsanUbsan.M.loaded_segments (0x5f18c : word) = Some W_5f18c.
Proof. vm_refl. Qed.
Lemma D_5f18c : decode_any W_5f18c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f190 : bv 32 := 0x7c013a03.
Lemma F_5f190 : fetch_word AsanUbsan.M.loaded_segments (0x5f190 : word) = Some W_5f190.
Proof. vm_refl. Qed.
Lemma D_5f190 : decode_any W_5f190 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f194 : bv 32 := 0x7b813a83.
Lemma F_5f194 : fetch_word AsanUbsan.M.loaded_segments (0x5f194 : word) = Some W_5f194.
Proof. vm_refl. Qed.
Lemma D_5f194 : decode_any W_5f194 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f198 : bv 32 := 0x7b013b03.
Lemma F_5f198 : fetch_word AsanUbsan.M.loaded_segments (0x5f198 : word) = Some W_5f198.
Proof. vm_refl. Qed.
Lemma D_5f198 : decode_any W_5f198 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f19c : bv 32 := 0x7a813b83.
Lemma F_5f19c : fetch_word AsanUbsan.M.loaded_segments (0x5f19c : word) = Some W_5f19c.
Proof. vm_refl. Qed.
Lemma D_5f19c : decode_any W_5f19c = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1a0 : bv 32 := 0x7f010113.
Lemma F_5f1a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f1a0 : word) = Some W_5f1a0.
Proof. vm_refl. Qed.
Lemma D_5f1a0 : decode_any W_5f1a0 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1a4 : bv 32 := 0x00008067.
Lemma F_5f1a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f1a4 : word) = Some W_5f1a4.
Proof. vm_refl. Qed.
Lemma D_5f1a4 : decode_any W_5f1a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1a8 : bv 32 := 0x80040693.
Lemma F_5f1a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f1a8 : word) = Some W_5f1a8.
Proof. vm_refl. Qed.
Lemma D_5f1a8 : decode_any W_5f1a8 = Some (OpImm ALU_ADD 13 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1ac : bv 32 := 0xfb068693.
Lemma F_5f1ac : fetch_word AsanUbsan.M.loaded_segments (0x5f1ac : word) = Some W_5f1ac.
Proof. vm_refl. Qed.
Lemma D_5f1ac : decode_any W_5f1ac = Some (OpImm ALU_ADD 13 13 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1b0 : bv 32 := 0x80040713.
Lemma F_5f1b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f1b0 : word) = Some W_5f1b0.
Proof. vm_refl. Qed.
Lemma D_5f1b0 : decode_any W_5f1b0 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1b4 : bv 32 := 0xfa070713.
Lemma F_5f1b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f1b4 : word) = Some W_5f1b4.
Proof. vm_refl. Qed.
Lemma D_5f1b4 : decode_any W_5f1b4 = Some (OpImm ALU_ADD 14 14 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1b8 : bv 32 := 0x7ff70a13.
Lemma F_5f1b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f1b8 : word) = Some W_5f1b8.
Proof. vm_refl. Qed.
Lemma D_5f1b8 : decode_any W_5f1b8 = Some (OpImm ALU_ADD 20 14 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1bc : bv 32 := 0x000a34a3.
Lemma F_5f1bc : fetch_word AsanUbsan.M.loaded_segments (0x5f1bc : word) = Some W_5f1bc.
Proof. vm_refl. Qed.
Lemma D_5f1bc : decode_any W_5f1bc = Some (Store SZ8 20 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1c0 : bv 32 := 0x00dab023.
Lemma F_5f1c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f1c0 : word) = Some W_5f1c0.
Proof. vm_refl. Qed.
Lemma D_5f1c0 : decode_any W_5f1c0 = Some (Store SZ8 21 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1c4 : bv 32 := 0x000ab423.
Lemma F_5f1c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f1c4 : word) = Some W_5f1c4.
Proof. vm_refl. Qed.
Lemma D_5f1c4 : decode_any W_5f1c4 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1c8 : bv 32 := 0x00060493.
Lemma F_5f1c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f1c8 : word) = Some W_5f1c8.
Proof. vm_refl. Qed.
Lemma D_5f1c8 : decode_any W_5f1c8 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1cc : bv 32 := 0x00058913.
Lemma F_5f1cc : fetch_word AsanUbsan.M.loaded_segments (0x5f1cc : word) = Some W_5f1cc.
Proof. vm_refl. Qed.
Lemma D_5f1cc : decode_any W_5f1cc = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1d0 : bv 32 := 0x00050993.
Lemma F_5f1d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f1d0 : word) = Some W_5f1d0.
Proof. vm_refl. Qed.
Lemma D_5f1d0 : decode_any W_5f1d0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1d4 : bv 32 := 0x0d9210ef.
Lemma F_5f1d4 : fetch_word AsanUbsan.M.loaded_segments (0x5f1d4 : word) = Some W_5f1d4.
Proof. vm_refl. Qed.
Lemma D_5f1d4 : decode_any W_5f1d4 = Some (Jal 1 137432, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1d8 : bv 32 := 0x00050593.
Lemma F_5f1d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f1d8 : word) = Some W_5f1d8.
Proof. vm_refl. Qed.
Lemma D_5f1d8 : decode_any W_5f1d8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1dc : bv 32 := 0x00077517.
Lemma F_5f1dc : fetch_word AsanUbsan.M.loaded_segments (0x5f1dc : word) = Some W_5f1dc.
Proof. vm_refl. Qed.
Lemma D_5f1dc : decode_any W_5f1dc = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1e0 : bv 32 := 0x2dc53503.
Lemma F_5f1e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f1e0 : word) = Some W_5f1e0.
Proof. vm_refl. Qed.
Lemma D_5f1e0 : decode_any W_5f1e0 = Some (Load SZ8 true 10 10 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1e4 : bv 32 := 0x02154703.
Lemma F_5f1e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f1e4 : word) = Some W_5f1e4.
Proof. vm_refl. Qed.
Lemma D_5f1e4 : decode_any W_5f1e4 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1e8 : bv 32 := 0x008a34a3.
Lemma F_5f1e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f1e8 : word) = Some W_5f1e8.
Proof. vm_refl. Qed.
Lemma D_5f1e8 : decode_any W_5f1e8 = Some (Store SZ8 20 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1ec : bv 32 := 0x80040513.
Lemma F_5f1ec : fetch_word AsanUbsan.M.loaded_segments (0x5f1ec : word) = Some W_5f1ec.
Proof. vm_refl. Qed.
Lemma D_5f1ec : decode_any W_5f1ec = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1f0 : bv 32 := 0xfa050513.
Lemma F_5f1f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f1f0 : word) = Some W_5f1f0.
Proof. vm_refl. Qed.
Lemma D_5f1f0 : decode_any W_5f1f0 = Some (OpImm ALU_ADD 10 10 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1f4 : bv 32 := 0x0ff00793.
Lemma F_5f1f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f1f4 : word) = Some W_5f1f4.
Proof. vm_refl. Qed.
Lemma D_5f1f4 : decode_any W_5f1f4 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1f8 : bv 32 := 0x00040613.
Lemma F_5f1f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f1f8 : word) = Some W_5f1f8.
Proof. vm_refl. Qed.
Lemma D_5f1f8 : decode_any W_5f1f8 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1fc : bv 32 := 0x00000693.
Lemma F_5f1fc : fetch_word AsanUbsan.M.loaded_segments (0x5f1fc : word) = Some W_5f1fc.
Proof. vm_refl. Qed.
Lemma D_5f1fc : decode_any W_5f1fc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f200 : bv 32 := 0x5fd080ef.
Lemma F_5f200 : fetch_word AsanUbsan.M.loaded_segments (0x5f200 : word) = Some W_5f200.
Proof. vm_refl. Qed.
Lemma D_5f200 : decode_any W_5f200 = Some (Jal 1 36348, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f204 : bv 32 := 0x80040613.
Lemma F_5f204 : fetch_word AsanUbsan.M.loaded_segments (0x5f204 : word) = Some W_5f204.
Proof. vm_refl. Qed.
Lemma D_5f204 : decode_any W_5f204 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f208 : bv 32 := 0xfa060613.
Lemma F_5f208 : fetch_word AsanUbsan.M.loaded_segments (0x5f208 : word) = Some W_5f208.
Proof. vm_refl. Qed.
Lemma D_5f208 : decode_any W_5f208 = Some (OpImm ALU_ADD 12 12 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f20c : bv 32 := 0x00090513.
Lemma F_5f20c : fetch_word AsanUbsan.M.loaded_segments (0x5f20c : word) = Some W_5f20c.
Proof. vm_refl. Qed.
Lemma D_5f20c : decode_any W_5f20c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f210 : bv 32 := 0x00048593.
Lemma F_5f210 : fetch_word AsanUbsan.M.loaded_segments (0x5f210 : word) = Some W_5f210.
Proof. vm_refl. Qed.
Lemma D_5f210 : decode_any W_5f210 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f214 : bv 32 := 0x3a1050ef.
Lemma F_5f214 : fetch_word AsanUbsan.M.loaded_segments (0x5f214 : word) = Some W_5f214.
Proof. vm_refl. Qed.
Lemma D_5f214 : decode_any W_5f214 = Some (Jal 1 23456, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f218 : bv 32 := 0x00098513.
Lemma F_5f218 : fetch_word AsanUbsan.M.loaded_segments (0x5f218 : word) = Some W_5f218.
Proof. vm_refl. Qed.
Lemma D_5f218 : decode_any W_5f218 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f21c : bv 32 := 0x00090593.
Lemma F_5f21c : fetch_word AsanUbsan.M.loaded_segments (0x5f21c : word) = Some W_5f21c.
Proof. vm_refl. Qed.
Lemma D_5f21c : decode_any W_5f21c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f220 : bv 32 := 0x00048613.
Lemma F_5f220 : fetch_word AsanUbsan.M.loaded_segments (0x5f220 : word) = Some W_5f220.
Proof. vm_refl. Qed.
Lemma D_5f220 : decode_any W_5f220 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f224 : bv 32 := 0xfbf48a13.
Lemma F_5f224 : fetch_word AsanUbsan.M.loaded_segments (0x5f224 : word) = Some W_5f224.
Proof. vm_refl. Qed.
Lemma D_5f224 : decode_any W_5f224 = Some (OpImm ALU_ADD 20 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f228 : bv 32 := 0xfbf00693.
Lemma F_5f228 : fetch_word AsanUbsan.M.loaded_segments (0x5f228 : word) = Some W_5f228.
Proof. vm_refl. Qed.
Lemma D_5f228 : decode_any W_5f228 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f22c : bv 32 := 0xed46e0e3.
Lemma F_5f22c : fetch_word AsanUbsan.M.loaded_segments (0x5f22c : word) = Some W_5f22c.
Proof. vm_refl. Qed.
Lemma D_5f22c : decode_any W_5f22c = Some (Branch BC_LTU 13 20 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f230 : bv 32 := 0x0c061463.
Lemma F_5f230 : fetch_word AsanUbsan.M.loaded_segments (0x5f230 : word) = Some W_5f230.
Proof. vm_refl. Qed.
Lemma D_5f230 : decode_any W_5f230 = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f234 : bv 32 := 0xef5ff06f.
Lemma F_5f234 : fetch_word AsanUbsan.M.loaded_segments (0x5f234 : word) = Some W_5f234.
Proof. vm_refl. Qed.
Lemma D_5f234 : decode_any W_5f234 = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f238 : bv 32 := 0x80040693.
Lemma F_5f238 : fetch_word AsanUbsan.M.loaded_segments (0x5f238 : word) = Some W_5f238.
Proof. vm_refl. Qed.
Lemma D_5f238 : decode_any W_5f238 = Some (OpImm ALU_ADD 13 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f23c : bv 32 := 0xfb068693.
Lemma F_5f23c : fetch_word AsanUbsan.M.loaded_segments (0x5f23c : word) = Some W_5f23c.
Proof. vm_refl. Qed.
Lemma D_5f23c : decode_any W_5f23c = Some (OpImm ALU_ADD 13 13 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f240 : bv 32 := 0x80040713.
Lemma F_5f240 : fetch_word AsanUbsan.M.loaded_segments (0x5f240 : word) = Some W_5f240.
Proof. vm_refl. Qed.
Lemma D_5f240 : decode_any W_5f240 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f244 : bv 32 := 0xfa070713.
Lemma F_5f244 : fetch_word AsanUbsan.M.loaded_segments (0x5f244 : word) = Some W_5f244.
Proof. vm_refl. Qed.
Lemma D_5f244 : decode_any W_5f244 = Some (OpImm ALU_ADD 14 14 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f248 : bv 32 := 0x7ff70b13.
Lemma F_5f248 : fetch_word AsanUbsan.M.loaded_segments (0x5f248 : word) = Some W_5f248.
Proof. vm_refl. Qed.
Lemma D_5f248 : decode_any W_5f248 = Some (OpImm ALU_ADD 22 14 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f24c : bv 32 := 0x000b34a3.
Lemma F_5f24c : fetch_word AsanUbsan.M.loaded_segments (0x5f24c : word) = Some W_5f24c.
Proof. vm_refl. Qed.
Lemma D_5f24c : decode_any W_5f24c = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f250 : bv 32 := 0x00dab023.
Lemma F_5f250 : fetch_word AsanUbsan.M.loaded_segments (0x5f250 : word) = Some W_5f250.
Proof. vm_refl. Qed.
Lemma D_5f250 : decode_any W_5f250 = Some (Store SZ8 21 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f254 : bv 32 := 0x000ab423.
Lemma F_5f254 : fetch_word AsanUbsan.M.loaded_segments (0x5f254 : word) = Some W_5f254.
Proof. vm_refl. Qed.
Lemma D_5f254 : decode_any W_5f254 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f258 : bv 32 := 0x00060493.
Lemma F_5f258 : fetch_word AsanUbsan.M.loaded_segments (0x5f258 : word) = Some W_5f258.
Proof. vm_refl. Qed.
Lemma D_5f258 : decode_any W_5f258 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f25c : bv 32 := 0x00058993.
Lemma F_5f25c : fetch_word AsanUbsan.M.loaded_segments (0x5f25c : word) = Some W_5f25c.
Proof. vm_refl. Qed.
Lemma D_5f25c : decode_any W_5f25c = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f260 : bv 32 := 0x00050913.
Lemma F_5f260 : fetch_word AsanUbsan.M.loaded_segments (0x5f260 : word) = Some W_5f260.
Proof. vm_refl. Qed.
Lemma D_5f260 : decode_any W_5f260 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f264 : bv 32 := 0x049210ef.
Lemma F_5f264 : fetch_word AsanUbsan.M.loaded_segments (0x5f264 : word) = Some W_5f264.
Proof. vm_refl. Qed.
Lemma D_5f264 : decode_any W_5f264 = Some (Jal 1 137288, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f268 : bv 32 := 0x00050593.
Lemma F_5f268 : fetch_word AsanUbsan.M.loaded_segments (0x5f268 : word) = Some W_5f268.
Proof. vm_refl. Qed.
Lemma D_5f268 : decode_any W_5f268 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f26c : bv 32 := 0x00077517.
Lemma F_5f26c : fetch_word AsanUbsan.M.loaded_segments (0x5f26c : word) = Some W_5f26c.
Proof. vm_refl. Qed.
Lemma D_5f26c : decode_any W_5f26c = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f270 : bv 32 := 0x24c53503.
Lemma F_5f270 : fetch_word AsanUbsan.M.loaded_segments (0x5f270 : word) = Some W_5f270.
Proof. vm_refl. Qed.
Lemma D_5f270 : decode_any W_5f270 = Some (Load SZ8 true 10 10 588, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f274 : bv 32 := 0x02154703.
Lemma F_5f274 : fetch_word AsanUbsan.M.loaded_segments (0x5f274 : word) = Some W_5f274.
Proof. vm_refl. Qed.
Lemma D_5f274 : decode_any W_5f274 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f278 : bv 32 := 0x008b34a3.
Lemma F_5f278 : fetch_word AsanUbsan.M.loaded_segments (0x5f278 : word) = Some W_5f278.
Proof. vm_refl. Qed.
Lemma D_5f278 : decode_any W_5f278 = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f27c : bv 32 := 0x80040513.
Lemma F_5f27c : fetch_word AsanUbsan.M.loaded_segments (0x5f27c : word) = Some W_5f27c.
Proof. vm_refl. Qed.
Lemma D_5f27c : decode_any W_5f27c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f280 : bv 32 := 0xfa050513.
Lemma F_5f280 : fetch_word AsanUbsan.M.loaded_segments (0x5f280 : word) = Some W_5f280.
Proof. vm_refl. Qed.
Lemma D_5f280 : decode_any W_5f280 = Some (OpImm ALU_ADD 10 10 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f284 : bv 32 := 0x0ff00793.
Lemma F_5f284 : fetch_word AsanUbsan.M.loaded_segments (0x5f284 : word) = Some W_5f284.
Proof. vm_refl. Qed.
Lemma D_5f284 : decode_any W_5f284 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f288 : bv 32 := 0x00040613.
Lemma F_5f288 : fetch_word AsanUbsan.M.loaded_segments (0x5f288 : word) = Some W_5f288.
Proof. vm_refl. Qed.
Lemma D_5f288 : decode_any W_5f288 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f28c : bv 32 := 0x00000693.
Lemma F_5f28c : fetch_word AsanUbsan.M.loaded_segments (0x5f28c : word) = Some W_5f28c.
Proof. vm_refl. Qed.
Lemma D_5f28c : decode_any W_5f28c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f290 : bv 32 := 0x56d080ef.
Lemma F_5f290 : fetch_word AsanUbsan.M.loaded_segments (0x5f290 : word) = Some W_5f290.
Proof. vm_refl. Qed.
Lemma D_5f290 : decode_any W_5f290 = Some (Jal 1 36204, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f294 : bv 32 := 0x80040613.
Lemma F_5f294 : fetch_word AsanUbsan.M.loaded_segments (0x5f294 : word) = Some W_5f294.
Proof. vm_refl. Qed.
Lemma D_5f294 : decode_any W_5f294 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f298 : bv 32 := 0xfa060613.
Lemma F_5f298 : fetch_word AsanUbsan.M.loaded_segments (0x5f298 : word) = Some W_5f298.
Proof. vm_refl. Qed.
Lemma D_5f298 : decode_any W_5f298 = Some (OpImm ALU_ADD 12 12 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f29c : bv 32 := 0x00090513.
Lemma F_5f29c : fetch_word AsanUbsan.M.loaded_segments (0x5f29c : word) = Some W_5f29c.
Proof. vm_refl. Qed.
Lemma D_5f29c : decode_any W_5f29c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2a0 : bv 32 := 0x00048593.
Lemma F_5f2a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f2a0 : word) = Some W_5f2a0.
Proof. vm_refl. Qed.
Lemma D_5f2a0 : decode_any W_5f2a0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2a4 : bv 32 := 0x311050ef.
Lemma F_5f2a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f2a4 : word) = Some W_5f2a4.
Proof. vm_refl. Qed.
Lemma D_5f2a4 : decode_any W_5f2a4 = Some (Jal 1 23312, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2a8 : bv 32 := 0x00090513.
Lemma F_5f2a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f2a8 : word) = Some W_5f2a8.
Proof. vm_refl. Qed.
Lemma D_5f2a8 : decode_any W_5f2a8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2ac : bv 32 := 0x00098593.
Lemma F_5f2ac : fetch_word AsanUbsan.M.loaded_segments (0x5f2ac : word) = Some W_5f2ac.
Proof. vm_refl. Qed.
Lemma D_5f2ac : decode_any W_5f2ac = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2b0 : bv 32 := 0x00048613.
Lemma F_5f2b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f2b0 : word) = Some W_5f2b0.
Proof. vm_refl. Qed.
Lemma D_5f2b0 : decode_any W_5f2b0 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2b4 : bv 32 := 0xfbf00693.
Lemma F_5f2b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f2b4 : word) = Some W_5f2b4.
Proof. vm_refl. Qed.
Lemma D_5f2b4 : decode_any W_5f2b4 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2b8 : bv 32 := 0xe946e0e3.
Lemma F_5f2b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f2b8 : word) = Some W_5f2b8.
Proof. vm_refl. Qed.
Lemma D_5f2b8 : decode_any W_5f2b8 = Some (Branch BC_LTU 13 20 7808, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2bc : bv 32 := 0x12061e63.
Lemma F_5f2bc : fetch_word AsanUbsan.M.loaded_segments (0x5f2bc : word) = Some W_5f2bc.
Proof. vm_refl. Qed.
Lemma D_5f2bc : decode_any W_5f2bc = Some (Branch BC_NE 12 0 316, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2c0 : bv 32 := 0xeb5ff06f.
Lemma F_5f2c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f2c0 : word) = Some W_5f2c0.
Proof. vm_refl. Qed.
Lemma D_5f2c0 : decode_any W_5f2c0 = Some (Jal 0 2096820, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2c4 : bv 32 := 0x00070803.
Lemma F_5f2c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f2c4 : word) = Some W_5f2c4.
Proof. vm_refl. Qed.
Lemma D_5f2c4 : decode_any W_5f2c4 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2c8 : bv 32 := 0x0077f793.
Lemma F_5f2c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f2c8 : word) = Some W_5f2c8.
Proof. vm_refl. Qed.
Lemma D_5f2c8 : decode_any W_5f2c8 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2cc : bv 32 := 0x010038b3.
Lemma F_5f2cc : fetch_word AsanUbsan.M.loaded_segments (0x5f2cc : word) = Some W_5f2cc.
Proof. vm_refl. Qed.
Lemma D_5f2cc : decode_any W_5f2cc = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2d0 : bv 32 := 0x0107a7b3.
Lemma F_5f2d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f2d0 : word) = Some W_5f2d0.
Proof. vm_refl. Qed.
Lemma D_5f2d0 : decode_any W_5f2d0 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2d4 : bv 32 := 0x0017c793.
Lemma F_5f2d4 : fetch_word AsanUbsan.M.loaded_segments (0x5f2d4 : word) = Some W_5f2d4.
Proof. vm_refl. Qed.
Lemma D_5f2d4 : decode_any W_5f2d4 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2d8 : bv 32 := 0x00f8f7b3.
Lemma F_5f2d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f2d8 : word) = Some W_5f2d8.
Proof. vm_refl. Qed.
Lemma D_5f2d8 : decode_any W_5f2d8 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2dc : bv 32 := 0x00e6fa63.
Lemma F_5f2dc : fetch_word AsanUbsan.M.loaded_segments (0x5f2dc : word) = Some W_5f2dc.
Proof. vm_refl. Qed.
Lemma D_5f2dc : decode_any W_5f2dc = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2e0 : bv 32 := 0x0006c803.
Lemma F_5f2e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f2e0 : word) = Some W_5f2e0.
Proof. vm_refl. Qed.
Lemma D_5f2e0 : decode_any W_5f2e0 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2e4 : bv 32 := 0x00168693.
Lemma F_5f2e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f2e4 : word) = Some W_5f2e4.
Proof. vm_refl. Qed.
Lemma D_5f2e4 : decode_any W_5f2e4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2e8 : bv 32 := 0x00f867b3.
Lemma F_5f2e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f2e8 : word) = Some W_5f2e8.
Proof. vm_refl. Qed.
Lemma D_5f2e8 : decode_any W_5f2e8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2ec : bv 32 := 0xfee69ae3.
Lemma F_5f2ec : fetch_word AsanUbsan.M.loaded_segments (0x5f2ec : word) = Some W_5f2ec.
Proof. vm_refl. Qed.
Lemma D_5f2ec : decode_any W_5f2ec = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2f0 : bv 32 := 0x0ff7f693.
Lemma F_5f2f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f2f0 : word) = Some W_5f2f0.
Proof. vm_refl. Qed.
Lemma D_5f2f0 : decode_any W_5f2f0 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2f4 : bv 32 := 0xe2068ae3.
Lemma F_5f2f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f2f4 : word) = Some W_5f2f4.
Proof. vm_refl. Qed.
Lemma D_5f2f4 : decode_any W_5f2f4 = Some (Branch BC_EQ 13 0 7732, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2f8 : bv 32 := 0x00050b13.
Lemma F_5f2f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f2f8 : word) = Some W_5f2f8.
Proof. vm_refl. Qed.
Lemma D_5f2f8 : decode_any W_5f2f8 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2fc : bv 32 := 0x00058513.
Lemma F_5f2fc : fetch_word AsanUbsan.M.loaded_segments (0x5f2fc : word) = Some W_5f2fc.
Proof. vm_refl. Qed.
Lemma D_5f2fc : decode_any W_5f2fc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f300 : bv 32 := 0x00058b93.
Lemma F_5f300 : fetch_word AsanUbsan.M.loaded_segments (0x5f300 : word) = Some W_5f300.
Proof. vm_refl. Qed.
Lemma D_5f300 : decode_any W_5f300 = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f304 : bv 32 := 0x00060593.
Lemma F_5f304 : fetch_word AsanUbsan.M.loaded_segments (0x5f304 : word) = Some W_5f304.
Proof. vm_refl. Qed.
Lemma D_5f304 : decode_any W_5f304 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f308 : bv 32 := 0x00060493.
Lemma F_5f308 : fetch_word AsanUbsan.M.loaded_segments (0x5f308 : word) = Some W_5f308.
Proof. vm_refl. Qed.
Lemma D_5f308 : decode_any W_5f308 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f30c : bv 32 := 0x075020ef.
Lemma F_5f30c : fetch_word AsanUbsan.M.loaded_segments (0x5f30c : word) = Some W_5f30c.
Proof. vm_refl. Qed.
Lemma D_5f30c : decode_any W_5f30c = Some (Jal 1 10356, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f310 : bv 32 := 0x000b8593.
Lemma F_5f310 : fetch_word AsanUbsan.M.loaded_segments (0x5f310 : word) = Some W_5f310.
Proof. vm_refl. Qed.
Lemma D_5f310 : decode_any W_5f310 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f314 : bv 32 := 0x00048613.
Lemma F_5f314 : fetch_word AsanUbsan.M.loaded_segments (0x5f314 : word) = Some W_5f314.
Proof. vm_refl. Qed.
Lemma D_5f314 : decode_any W_5f314 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f318 : bv 32 := 0x00050913.
Lemma F_5f318 : fetch_word AsanUbsan.M.loaded_segments (0x5f318 : word) = Some W_5f318.
Proof. vm_refl. Qed.
Lemma D_5f318 : decode_any W_5f318 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f31c : bv 32 := 0x000b0513.
Lemma F_5f31c : fetch_word AsanUbsan.M.loaded_segments (0x5f31c : word) = Some W_5f31c.
Proof. vm_refl. Qed.
Lemma D_5f31c : decode_any W_5f31c = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f320 : bv 32 := 0xe00904e3.
Lemma F_5f320 : fetch_word AsanUbsan.M.loaded_segments (0x5f320 : word) = Some W_5f320.
Proof. vm_refl. Qed.
Lemma D_5f320 : decode_any W_5f320 = Some (Branch BC_EQ 18 0 7688, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f324 : bv 32 := 0xfffc3517.
Lemma F_5f324 : fetch_word AsanUbsan.M.loaded_segments (0x5f324 : word) = Some W_5f324.
Proof. vm_refl. Qed.
Lemma D_5f324 : decode_any W_5f324 = Some (Auipc 10 1048515, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f328 : bv 32 := 0xa0e50513.
Lemma F_5f328 : fetch_word AsanUbsan.M.loaded_segments (0x5f328 : word) = Some W_5f328.
Proof. vm_refl. Qed.
Lemma D_5f328 : decode_any W_5f328 = Some (OpImm ALU_ADD 10 10 2574, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f32c : bv 32 := 0x47d090ef.
Lemma F_5f32c : fetch_word AsanUbsan.M.loaded_segments (0x5f32c : word) = Some W_5f32c.
Proof. vm_refl. Qed.
Lemma D_5f32c : decode_any W_5f32c = Some (Jal 1 40060, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f330 : bv 32 := 0x000b8593.
Lemma F_5f330 : fetch_word AsanUbsan.M.loaded_segments (0x5f330 : word) = Some W_5f330.
Proof. vm_refl. Qed.
Lemma D_5f330 : decode_any W_5f330 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f334 : bv 32 := 0x00048613.
Lemma F_5f334 : fetch_word AsanUbsan.M.loaded_segments (0x5f334 : word) = Some W_5f334.
Proof. vm_refl. Qed.
Lemma D_5f334 : decode_any W_5f334 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f338 : bv 32 := 0x00050693.
Lemma F_5f338 : fetch_word AsanUbsan.M.loaded_segments (0x5f338 : word) = Some W_5f338.
Proof. vm_refl. Qed.
Lemma D_5f338 : decode_any W_5f338 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f33c : bv 32 := 0x000b0513.
Lemma F_5f33c : fetch_word AsanUbsan.M.loaded_segments (0x5f33c : word) = Some W_5f33c.
Proof. vm_refl. Qed.
Lemma D_5f33c : decode_any W_5f33c = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f340 : bv 32 := 0xde0694e3.
Lemma F_5f340 : fetch_word AsanUbsan.M.loaded_segments (0x5f340 : word) = Some W_5f340.
Proof. vm_refl. Qed.
Lemma D_5f340 : decode_any W_5f340 = Some (Branch BC_NE 13 0 7656, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f344 : bv 32 := 0x4cd090ef.
Lemma F_5f344 : fetch_word AsanUbsan.M.loaded_segments (0x5f344 : word) = Some W_5f344.
Proof. vm_refl. Qed.
Lemma D_5f344 : decode_any W_5f344 = Some (Jal 1 40140, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f348 : bv 32 := 0x16050c63.
Lemma F_5f348 : fetch_word AsanUbsan.M.loaded_segments (0x5f348 : word) = Some W_5f348.
Proof. vm_refl. Qed.
Lemma D_5f348 : decode_any W_5f348 = Some (Branch BC_EQ 10 0 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f34c : bv 32 := 0x80040513.
Lemma F_5f34c : fetch_word AsanUbsan.M.loaded_segments (0x5f34c : word) = Some W_5f34c.
Proof. vm_refl. Qed.
Lemma D_5f34c : decode_any W_5f34c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f350 : bv 32 := 0xfb050513.
Lemma F_5f350 : fetch_word AsanUbsan.M.loaded_segments (0x5f350 : word) = Some W_5f350.
Proof. vm_refl. Qed.
Lemma D_5f350 : decode_any W_5f350 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f354 : bv 32 := 0x80040593.
Lemma F_5f354 : fetch_word AsanUbsan.M.loaded_segments (0x5f354 : word) = Some W_5f354.
Proof. vm_refl. Qed.
Lemma D_5f354 : decode_any W_5f354 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f358 : bv 32 := 0xfa058593.
Lemma F_5f358 : fetch_word AsanUbsan.M.loaded_segments (0x5f358 : word) = Some W_5f358.
Proof. vm_refl. Qed.
Lemma D_5f358 : decode_any W_5f358 = Some (OpImm ALU_ADD 11 11 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f35c : bv 32 := 0x7ff58993.
Lemma F_5f35c : fetch_word AsanUbsan.M.loaded_segments (0x5f35c : word) = Some W_5f35c.
Proof. vm_refl. Qed.
Lemma D_5f35c : decode_any W_5f35c = Some (OpImm ALU_ADD 19 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f360 : bv 32 := 0x0009b4a3.
Lemma F_5f360 : fetch_word AsanUbsan.M.loaded_segments (0x5f360 : word) = Some W_5f360.
Proof. vm_refl. Qed.
Lemma D_5f360 : decode_any W_5f360 = Some (Store SZ8 19 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f364 : bv 32 := 0x00aab023.
Lemma F_5f364 : fetch_word AsanUbsan.M.loaded_segments (0x5f364 : word) = Some W_5f364.
Proof. vm_refl. Qed.
Lemma D_5f364 : decode_any W_5f364 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f368 : bv 32 := 0x000ab423.
Lemma F_5f368 : fetch_word AsanUbsan.M.loaded_segments (0x5f368 : word) = Some W_5f368.
Proof. vm_refl. Qed.
Lemma D_5f368 : decode_any W_5f368 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f36c : bv 32 := 0x740210ef.
Lemma F_5f36c : fetch_word AsanUbsan.M.loaded_segments (0x5f36c : word) = Some W_5f36c.
Proof. vm_refl. Qed.
Lemma D_5f36c : decode_any W_5f36c = Some (Jal 1 137024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f370 : bv 32 := 0x00050593.
Lemma F_5f370 : fetch_word AsanUbsan.M.loaded_segments (0x5f370 : word) = Some W_5f370.
Proof. vm_refl. Qed.
Lemma D_5f370 : decode_any W_5f370 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f374 : bv 32 := 0x00077517.
Lemma F_5f374 : fetch_word AsanUbsan.M.loaded_segments (0x5f374 : word) = Some W_5f374.
Proof. vm_refl. Qed.
Lemma D_5f374 : decode_any W_5f374 = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f378 : bv 32 := 0x14453503.
Lemma F_5f378 : fetch_word AsanUbsan.M.loaded_segments (0x5f378 : word) = Some W_5f378.
Proof. vm_refl. Qed.
Lemma D_5f378 : decode_any W_5f378 = Some (Load SZ8 true 10 10 324, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f37c : bv 32 := 0x02154703.
Lemma F_5f37c : fetch_word AsanUbsan.M.loaded_segments (0x5f37c : word) = Some W_5f37c.
Proof. vm_refl. Qed.
Lemma D_5f37c : decode_any W_5f37c = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f380 : bv 32 := 0x0089b4a3.
Lemma F_5f380 : fetch_word AsanUbsan.M.loaded_segments (0x5f380 : word) = Some W_5f380.
Proof. vm_refl. Qed.
Lemma D_5f380 : decode_any W_5f380 = Some (Store SZ8 19 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f384 : bv 32 := 0x80040513.
Lemma F_5f384 : fetch_word AsanUbsan.M.loaded_segments (0x5f384 : word) = Some W_5f384.
Proof. vm_refl. Qed.
Lemma D_5f384 : decode_any W_5f384 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f388 : bv 32 := 0xfa050513.
Lemma F_5f388 : fetch_word AsanUbsan.M.loaded_segments (0x5f388 : word) = Some W_5f388.
Proof. vm_refl. Qed.
Lemma D_5f388 : decode_any W_5f388 = Some (OpImm ALU_ADD 10 10 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f38c : bv 32 := 0x0ff00793.
Lemma F_5f38c : fetch_word AsanUbsan.M.loaded_segments (0x5f38c : word) = Some W_5f38c.
Proof. vm_refl. Qed.
Lemma D_5f38c : decode_any W_5f38c = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f390 : bv 32 := 0x00040613.
Lemma F_5f390 : fetch_word AsanUbsan.M.loaded_segments (0x5f390 : word) = Some W_5f390.
Proof. vm_refl. Qed.
Lemma D_5f390 : decode_any W_5f390 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f394 : bv 32 := 0x00000693.
Lemma F_5f394 : fetch_word AsanUbsan.M.loaded_segments (0x5f394 : word) = Some W_5f394.
Proof. vm_refl. Qed.
Lemma D_5f394 : decode_any W_5f394 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f398 : bv 32 := 0x465080ef.
Lemma F_5f398 : fetch_word AsanUbsan.M.loaded_segments (0x5f398 : word) = Some W_5f398.
Proof. vm_refl. Qed.
Lemma D_5f398 : decode_any W_5f398 = Some (Jal 1 35940, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f39c : bv 32 := 0x80040513.
Lemma F_5f39c : fetch_word AsanUbsan.M.loaded_segments (0x5f39c : word) = Some W_5f39c.
Proof. vm_refl. Qed.
Lemma D_5f39c : decode_any W_5f39c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3a0 : bv 32 := 0xfa050513.
Lemma F_5f3a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f3a0 : word) = Some W_5f3a0.
Proof. vm_refl. Qed.
Lemma D_5f3a0 : decode_any W_5f3a0 = Some (OpImm ALU_ADD 10 10 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3a4 : bv 32 := 0x775090ef.
Lemma F_5f3a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f3a4 : word) = Some W_5f3a4.
Proof. vm_refl. Qed.
Lemma D_5f3a4 : decode_any W_5f3a4 = Some (Jal 1 40820, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3a8 : bv 32 := 0x00050693.
Lemma F_5f3a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f3a8 : word) = Some W_5f3a8.
Proof. vm_refl. Qed.
Lemma D_5f3a8 : decode_any W_5f3a8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3ac : bv 32 := 0x00040993.
Lemma F_5f3ac : fetch_word AsanUbsan.M.loaded_segments (0x5f3ac : word) = Some W_5f3ac.
Proof. vm_refl. Qed.
Lemma D_5f3ac : decode_any W_5f3ac = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3b0 : bv 32 := 0x00048613.
Lemma F_5f3b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f3b0 : word) = Some W_5f3b0.
Proof. vm_refl. Qed.
Lemma D_5f3b0 : decode_any W_5f3b0 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3b4 : bv 32 := 0x000b8593.
Lemma F_5f3b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f3b4 : word) = Some W_5f3b4.
Proof. vm_refl. Qed.
Lemma D_5f3b4 : decode_any W_5f3b4 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3b8 : bv 32 := 0x000b0513.
Lemma F_5f3b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f3b8 : word) = Some W_5f3b8.
Proof. vm_refl. Qed.
Lemma D_5f3b8 : decode_any W_5f3b8 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3bc : bv 32 := 0xd60696e3.
Lemma F_5f3bc : fetch_word AsanUbsan.M.loaded_segments (0x5f3bc : word) = Some W_5f3bc.
Proof. vm_refl. Qed.
Lemma D_5f3bc : decode_any W_5f3bc = Some (Branch BC_NE 13 0 7532, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3c0 : bv 32 := 0x1040006f.
Lemma F_5f3c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f3c0 : word) = Some W_5f3c0.
Proof. vm_refl. Qed.
Lemma D_5f3c0 : decode_any W_5f3c0 = Some (Jal 0 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3c4 : bv 32 := 0x00070803.
Lemma F_5f3c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f3c4 : word) = Some W_5f3c4.
Proof. vm_refl. Qed.
Lemma D_5f3c4 : decode_any W_5f3c4 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3c8 : bv 32 := 0x0077f793.
Lemma F_5f3c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f3c8 : word) = Some W_5f3c8.
Proof. vm_refl. Qed.
Lemma D_5f3c8 : decode_any W_5f3c8 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3cc : bv 32 := 0x010038b3.
Lemma F_5f3cc : fetch_word AsanUbsan.M.loaded_segments (0x5f3cc : word) = Some W_5f3cc.
Proof. vm_refl. Qed.
Lemma D_5f3cc : decode_any W_5f3cc = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3d0 : bv 32 := 0x0107a7b3.
Lemma F_5f3d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f3d0 : word) = Some W_5f3d0.
Proof. vm_refl. Qed.
Lemma D_5f3d0 : decode_any W_5f3d0 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3d4 : bv 32 := 0x0017c793.
Lemma F_5f3d4 : fetch_word AsanUbsan.M.loaded_segments (0x5f3d4 : word) = Some W_5f3d4.
Proof. vm_refl. Qed.
Lemma D_5f3d4 : decode_any W_5f3d4 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3d8 : bv 32 := 0x00f8f7b3.
Lemma F_5f3d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f3d8 : word) = Some W_5f3d8.
Proof. vm_refl. Qed.
Lemma D_5f3d8 : decode_any W_5f3d8 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3dc : bv 32 := 0x00e6fa63.
Lemma F_5f3dc : fetch_word AsanUbsan.M.loaded_segments (0x5f3dc : word) = Some W_5f3dc.
Proof. vm_refl. Qed.
Lemma D_5f3dc : decode_any W_5f3dc = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3e0 : bv 32 := 0x0006c803.
Lemma F_5f3e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f3e0 : word) = Some W_5f3e0.
Proof. vm_refl. Qed.
Lemma D_5f3e0 : decode_any W_5f3e0 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3e4 : bv 32 := 0x00168693.
Lemma F_5f3e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f3e4 : word) = Some W_5f3e4.
Proof. vm_refl. Qed.
Lemma D_5f3e4 : decode_any W_5f3e4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3e8 : bv 32 := 0x00f867b3.
Lemma F_5f3e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f3e8 : word) = Some W_5f3e8.
Proof. vm_refl. Qed.
Lemma D_5f3e8 : decode_any W_5f3e8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3ec : bv 32 := 0xfee69ae3.
Lemma F_5f3ec : fetch_word AsanUbsan.M.loaded_segments (0x5f3ec : word) = Some W_5f3ec.
Proof. vm_refl. Qed.
Lemma D_5f3ec : decode_any W_5f3ec = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3f0 : bv 32 := 0x0ff7f693.
Lemma F_5f3f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f3f0 : word) = Some W_5f3f0.
Proof. vm_refl. Qed.
Lemma D_5f3f0 : decode_any W_5f3f0 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3f4 : bv 32 := 0xd80680e3.
Lemma F_5f3f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f3f4 : word) = Some W_5f3f4.
Proof. vm_refl. Qed.
Lemma D_5f3f4 : decode_any W_5f3f4 = Some (Branch BC_EQ 13 0 7552, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3f8 : bv 32 := 0x00050493.
Lemma F_5f3f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f3f8 : word) = Some W_5f3f8.
Proof. vm_refl. Qed.
Lemma D_5f3f8 : decode_any W_5f3f8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3fc : bv 32 := 0x00058b13.
Lemma F_5f3fc : fetch_word AsanUbsan.M.loaded_segments (0x5f3fc : word) = Some W_5f3fc.
Proof. vm_refl. Qed.
Lemma D_5f3fc : decode_any W_5f3fc = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f400 : bv 32 := 0x00060593.
Lemma F_5f400 : fetch_word AsanUbsan.M.loaded_segments (0x5f400 : word) = Some W_5f400.
Proof. vm_refl. Qed.
Lemma D_5f400 : decode_any W_5f400 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f404 : bv 32 := 0x00060913.
Lemma F_5f404 : fetch_word AsanUbsan.M.loaded_segments (0x5f404 : word) = Some W_5f404.
Proof. vm_refl. Qed.
Lemma D_5f404 : decode_any W_5f404 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f408 : bv 32 := 0x778020ef.
Lemma F_5f408 : fetch_word AsanUbsan.M.loaded_segments (0x5f408 : word) = Some W_5f408.
Proof. vm_refl. Qed.
Lemma D_5f408 : decode_any W_5f408 = Some (Jal 1 10104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f40c : bv 32 := 0x000b0593.
Lemma F_5f40c : fetch_word AsanUbsan.M.loaded_segments (0x5f40c : word) = Some W_5f40c.
Proof. vm_refl. Qed.
Lemma D_5f40c : decode_any W_5f40c = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f410 : bv 32 := 0x00090613.
Lemma F_5f410 : fetch_word AsanUbsan.M.loaded_segments (0x5f410 : word) = Some W_5f410.
Proof. vm_refl. Qed.
Lemma D_5f410 : decode_any W_5f410 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f414 : bv 32 := 0x00050993.
Lemma F_5f414 : fetch_word AsanUbsan.M.loaded_segments (0x5f414 : word) = Some W_5f414.
Proof. vm_refl. Qed.
Lemma D_5f414 : decode_any W_5f414 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f418 : bv 32 := 0x00048513.
Lemma F_5f418 : fetch_word AsanUbsan.M.loaded_segments (0x5f418 : word) = Some W_5f418.
Proof. vm_refl. Qed.
Lemma D_5f418 : decode_any W_5f418 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f41c : bv 32 := 0xd4098ce3.
Lemma F_5f41c : fetch_word AsanUbsan.M.loaded_segments (0x5f41c : word) = Some W_5f41c.
Proof. vm_refl. Qed.
Lemma D_5f41c : decode_any W_5f41c = Some (Branch BC_EQ 19 0 7512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f420 : bv 32 := 0xfffc3517.
Lemma F_5f420 : fetch_word AsanUbsan.M.loaded_segments (0x5f420 : word) = Some W_5f420.
Proof. vm_refl. Qed.
Lemma D_5f420 : decode_any W_5f420 = Some (Auipc 10 1048515, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f424 : bv 32 := 0x91250513.
Lemma F_5f424 : fetch_word AsanUbsan.M.loaded_segments (0x5f424 : word) = Some W_5f424.
Proof. vm_refl. Qed.
Lemma D_5f424 : decode_any W_5f424 = Some (OpImm ALU_ADD 10 10 2322, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f428 : bv 32 := 0x381090ef.
Lemma F_5f428 : fetch_word AsanUbsan.M.loaded_segments (0x5f428 : word) = Some W_5f428.
Proof. vm_refl. Qed.
Lemma D_5f428 : decode_any W_5f428 = Some (Jal 1 39808, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f42c : bv 32 := 0x000b0593.
Lemma F_5f42c : fetch_word AsanUbsan.M.loaded_segments (0x5f42c : word) = Some W_5f42c.
Proof. vm_refl. Qed.
Lemma D_5f42c : decode_any W_5f42c = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f430 : bv 32 := 0x00090613.
Lemma F_5f430 : fetch_word AsanUbsan.M.loaded_segments (0x5f430 : word) = Some W_5f430.
Proof. vm_refl. Qed.
Lemma D_5f430 : decode_any W_5f430 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f434 : bv 32 := 0x00050693.
Lemma F_5f434 : fetch_word AsanUbsan.M.loaded_segments (0x5f434 : word) = Some W_5f434.
Proof. vm_refl. Qed.
Lemma D_5f434 : decode_any W_5f434 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f438 : bv 32 := 0x00048513.
Lemma F_5f438 : fetch_word AsanUbsan.M.loaded_segments (0x5f438 : word) = Some W_5f438.
Proof. vm_refl. Qed.
Lemma D_5f438 : decode_any W_5f438 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f43c : bv 32 := 0xd2069ce3.
Lemma F_5f43c : fetch_word AsanUbsan.M.loaded_segments (0x5f43c : word) = Some W_5f43c.
Proof. vm_refl. Qed.
Lemma D_5f43c : decode_any W_5f43c = Some (Branch BC_NE 13 0 7480, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f440 : bv 32 := 0x3d1090ef.
Lemma F_5f440 : fetch_word AsanUbsan.M.loaded_segments (0x5f440 : word) = Some W_5f440.
Proof. vm_refl. Qed.
Lemma D_5f440 : decode_any W_5f440 = Some (Jal 1 39888, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f444 : bv 32 := 0x0c050263.
Lemma F_5f444 : fetch_word AsanUbsan.M.loaded_segments (0x5f444 : word) = Some W_5f444.
Proof. vm_refl. Qed.
Lemma D_5f444 : decode_any W_5f444 = Some (Branch BC_EQ 10 0 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f448 : bv 32 := 0x80040513.
Lemma F_5f448 : fetch_word AsanUbsan.M.loaded_segments (0x5f448 : word) = Some W_5f448.
Proof. vm_refl. Qed.
Lemma D_5f448 : decode_any W_5f448 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f44c : bv 32 := 0xfb050513.
Lemma F_5f44c : fetch_word AsanUbsan.M.loaded_segments (0x5f44c : word) = Some W_5f44c.
Proof. vm_refl. Qed.
Lemma D_5f44c : decode_any W_5f44c = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f450 : bv 32 := 0x80040593.
Lemma F_5f450 : fetch_word AsanUbsan.M.loaded_segments (0x5f450 : word) = Some W_5f450.
Proof. vm_refl. Qed.
Lemma D_5f450 : decode_any W_5f450 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f454 : bv 32 := 0xfa058593.
Lemma F_5f454 : fetch_word AsanUbsan.M.loaded_segments (0x5f454 : word) = Some W_5f454.
Proof. vm_refl. Qed.
Lemma D_5f454 : decode_any W_5f454 = Some (OpImm ALU_ADD 11 11 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f458 : bv 32 := 0x7ff58a13.
Lemma F_5f458 : fetch_word AsanUbsan.M.loaded_segments (0x5f458 : word) = Some W_5f458.
Proof. vm_refl. Qed.
Lemma D_5f458 : decode_any W_5f458 = Some (OpImm ALU_ADD 20 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f45c : bv 32 := 0x000a34a3.
Lemma F_5f45c : fetch_word AsanUbsan.M.loaded_segments (0x5f45c : word) = Some W_5f45c.
Proof. vm_refl. Qed.
Lemma D_5f45c : decode_any W_5f45c = Some (Store SZ8 20 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f460 : bv 32 := 0x00aab023.
Lemma F_5f460 : fetch_word AsanUbsan.M.loaded_segments (0x5f460 : word) = Some W_5f460.
Proof. vm_refl. Qed.
Lemma D_5f460 : decode_any W_5f460 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f464 : bv 32 := 0x000ab423.
Lemma F_5f464 : fetch_word AsanUbsan.M.loaded_segments (0x5f464 : word) = Some W_5f464.
Proof. vm_refl. Qed.
Lemma D_5f464 : decode_any W_5f464 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f468 : bv 32 := 0x644210ef.
Lemma F_5f468 : fetch_word AsanUbsan.M.loaded_segments (0x5f468 : word) = Some W_5f468.
Proof. vm_refl. Qed.
Lemma D_5f468 : decode_any W_5f468 = Some (Jal 1 136772, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f46c : bv 32 := 0x00050593.
Lemma F_5f46c : fetch_word AsanUbsan.M.loaded_segments (0x5f46c : word) = Some W_5f46c.
Proof. vm_refl. Qed.
Lemma D_5f46c : decode_any W_5f46c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f470 : bv 32 := 0x00077517.
Lemma F_5f470 : fetch_word AsanUbsan.M.loaded_segments (0x5f470 : word) = Some W_5f470.
Proof. vm_refl. Qed.
Lemma D_5f470 : decode_any W_5f470 = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f474 : bv 32 := 0x04853503.
Lemma F_5f474 : fetch_word AsanUbsan.M.loaded_segments (0x5f474 : word) = Some W_5f474.
Proof. vm_refl. Qed.
Lemma D_5f474 : decode_any W_5f474 = Some (Load SZ8 true 10 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f478 : bv 32 := 0x02154703.
Lemma F_5f478 : fetch_word AsanUbsan.M.loaded_segments (0x5f478 : word) = Some W_5f478.
Proof. vm_refl. Qed.
Lemma D_5f478 : decode_any W_5f478 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f47c : bv 32 := 0x008a34a3.
Lemma F_5f47c : fetch_word AsanUbsan.M.loaded_segments (0x5f47c : word) = Some W_5f47c.
Proof. vm_refl. Qed.
Lemma D_5f47c : decode_any W_5f47c = Some (Store SZ8 20 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f480 : bv 32 := 0x80040513.
Lemma F_5f480 : fetch_word AsanUbsan.M.loaded_segments (0x5f480 : word) = Some W_5f480.
Proof. vm_refl. Qed.
Lemma D_5f480 : decode_any W_5f480 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f484 : bv 32 := 0xfa050513.
Lemma F_5f484 : fetch_word AsanUbsan.M.loaded_segments (0x5f484 : word) = Some W_5f484.
Proof. vm_refl. Qed.
Lemma D_5f484 : decode_any W_5f484 = Some (OpImm ALU_ADD 10 10 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f488 : bv 32 := 0x0ff00793.
Lemma F_5f488 : fetch_word AsanUbsan.M.loaded_segments (0x5f488 : word) = Some W_5f488.
Proof. vm_refl. Qed.
Lemma D_5f488 : decode_any W_5f488 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f48c : bv 32 := 0x00040613.
Lemma F_5f48c : fetch_word AsanUbsan.M.loaded_segments (0x5f48c : word) = Some W_5f48c.
Proof. vm_refl. Qed.
Lemma D_5f48c : decode_any W_5f48c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f490 : bv 32 := 0x00000693.
Lemma F_5f490 : fetch_word AsanUbsan.M.loaded_segments (0x5f490 : word) = Some W_5f490.
Proof. vm_refl. Qed.
Lemma D_5f490 : decode_any W_5f490 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f494 : bv 32 := 0x369080ef.
Lemma F_5f494 : fetch_word AsanUbsan.M.loaded_segments (0x5f494 : word) = Some W_5f494.
Proof. vm_refl. Qed.
Lemma D_5f494 : decode_any W_5f494 = Some (Jal 1 35688, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f498 : bv 32 := 0x80040513.
Lemma F_5f498 : fetch_word AsanUbsan.M.loaded_segments (0x5f498 : word) = Some W_5f498.
Proof. vm_refl. Qed.
Lemma D_5f498 : decode_any W_5f498 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f49c : bv 32 := 0xfa050513.
Lemma F_5f49c : fetch_word AsanUbsan.M.loaded_segments (0x5f49c : word) = Some W_5f49c.
Proof. vm_refl. Qed.
Lemma D_5f49c : decode_any W_5f49c = Some (OpImm ALU_ADD 10 10 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4a0 : bv 32 := 0x679090ef.
Lemma F_5f4a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f4a0 : word) = Some W_5f4a0.
Proof. vm_refl. Qed.
Lemma D_5f4a0 : decode_any W_5f4a0 = Some (Jal 1 40568, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4a4 : bv 32 := 0x00050693.
Lemma F_5f4a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f4a4 : word) = Some W_5f4a4.
Proof. vm_refl. Qed.
Lemma D_5f4a4 : decode_any W_5f4a4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4a8 : bv 32 := 0x00040a13.
Lemma F_5f4a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f4a8 : word) = Some W_5f4a8.
Proof. vm_refl. Qed.
Lemma D_5f4a8 : decode_any W_5f4a8 = Some (OpImm ALU_ADD 20 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4ac : bv 32 := 0x00090613.
Lemma F_5f4ac : fetch_word AsanUbsan.M.loaded_segments (0x5f4ac : word) = Some W_5f4ac.
Proof. vm_refl. Qed.
Lemma D_5f4ac : decode_any W_5f4ac = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4b0 : bv 32 := 0x000b0593.
Lemma F_5f4b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f4b0 : word) = Some W_5f4b0.
Proof. vm_refl. Qed.
Lemma D_5f4b0 : decode_any W_5f4b0 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4b4 : bv 32 := 0x00048513.
Lemma F_5f4b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f4b4 : word) = Some W_5f4b4.
Proof. vm_refl. Qed.
Lemma D_5f4b4 : decode_any W_5f4b4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4b8 : bv 32 := 0xca069ee3.
Lemma F_5f4b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f4b8 : word) = Some W_5f4b8.
Proof. vm_refl. Qed.
Lemma D_5f4b8 : decode_any W_5f4b8 = Some (Branch BC_NE 13 0 7356, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4bc : bv 32 := 0x0500006f.
Lemma F_5f4bc : fetch_word AsanUbsan.M.loaded_segments (0x5f4bc : word) = Some W_5f4bc.
Proof. vm_refl. Qed.
Lemma D_5f4bc : decode_any W_5f4bc = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4c0 : bv 32 := 0x00040993.
Lemma F_5f4c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f4c0 : word) = Some W_5f4c0.
Proof. vm_refl. Qed.
Lemma D_5f4c0 : decode_any W_5f4c0 = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4c4 : bv 32 := 0x5e8210ef.
Lemma F_5f4c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f4c4 : word) = Some W_5f4c4.
Proof. vm_refl. Qed.
Lemma D_5f4c4 : decode_any W_5f4c4 = Some (Jal 1 136680, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4c8 : bv 32 := 0xfffb1597.
Lemma F_5f4c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f4c8 : word) = Some W_5f4c8.
Proof. vm_refl. Qed.
Lemma D_5f4c8 : decode_any W_5f4c8 = Some (Auipc 11 1048497, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4cc : bv 32 := 0xf405b583.
Lemma F_5f4cc : fetch_word AsanUbsan.M.loaded_segments (0x5f4cc : word) = Some W_5f4cc.
Proof. vm_refl. Qed.
Lemma D_5f4cc : decode_any W_5f4cc = Some (Load SZ8 true 11 11 3904, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4d0 : bv 32 := 0x00bab023.
Lemma F_5f4d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f4d0 : word) = Some W_5f4d0.
Proof. vm_refl. Qed.
Lemma D_5f4d0 : decode_any W_5f4d0 = Some (Store SZ8 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4d4 : bv 32 := 0x80040613.
Lemma F_5f4d4 : fetch_word AsanUbsan.M.loaded_segments (0x5f4d4 : word) = Some W_5f4d4.
Proof. vm_refl. Qed.
Lemma D_5f4d4 : decode_any W_5f4d4 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4d8 : bv 32 := 0xfa060613.
Lemma F_5f4d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f4d8 : word) = Some W_5f4d8.
Proof. vm_refl. Qed.
Lemma D_5f4d8 : decode_any W_5f4d8 = Some (OpImm ALU_ADD 12 12 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4dc : bv 32 := 0x00098593.
Lemma F_5f4dc : fetch_word AsanUbsan.M.loaded_segments (0x5f4dc : word) = Some W_5f4dc.
Proof. vm_refl. Qed.
Lemma D_5f4dc : decode_any W_5f4dc = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4e0 : bv 32 := 0x00090693.
Lemma F_5f4e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f4e0 : word) = Some W_5f4e0.
Proof. vm_refl. Qed.
Lemma D_5f4e0 : decode_any W_5f4e0 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4e4 : bv 32 := 0x00000713.
Lemma F_5f4e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f4e4 : word) = Some W_5f4e4.
Proof. vm_refl. Qed.
Lemma D_5f4e4 : decode_any W_5f4e4 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4e8 : bv 32 := 0x00048793.
Lemma F_5f4e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f4e8 : word) = Some W_5f4e8.
Proof. vm_refl. Qed.
Lemma D_5f4e8 : decode_any W_5f4e8 = Some (OpImm ALU_ADD 15 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4ec : bv 32 := 0x00000813.
Lemma F_5f4ec : fetch_word AsanUbsan.M.loaded_segments (0x5f4ec : word) = Some W_5f4ec.
Proof. vm_refl. Qed.
Lemma D_5f4ec : decode_any W_5f4ec = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4f0 : bv 32 := 0x00000893.
Lemma F_5f4f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f4f0 : word) = Some W_5f4f0.
Proof. vm_refl. Qed.
Lemma D_5f4f0 : decode_any W_5f4f0 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4f4 : bv 32 := 0x619050ef.
Lemma F_5f4f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f4f4 : word) = Some W_5f4f4.
Proof. vm_refl. Qed.
Lemma D_5f4f4 : decode_any W_5f4f4 = Some (Jal 1 24088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4f8 : bv 32 := 0x000b0513.
Lemma F_5f4f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f4f8 : word) = Some W_5f4f8.
Proof. vm_refl. Qed.
Lemma D_5f4f8 : decode_any W_5f4f8 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4fc : bv 32 := 0x000b8593.
Lemma F_5f4fc : fetch_word AsanUbsan.M.loaded_segments (0x5f4fc : word) = Some W_5f4fc.
Proof. vm_refl. Qed.
Lemma D_5f4fc : decode_any W_5f4fc = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f500 : bv 32 := 0x00048613.
Lemma F_5f500 : fetch_word AsanUbsan.M.loaded_segments (0x5f500 : word) = Some W_5f500.
Proof. vm_refl. Qed.
Lemma D_5f500 : decode_any W_5f500 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f504 : bv 32 := 0xc25ff06f.
Lemma F_5f504 : fetch_word AsanUbsan.M.loaded_segments (0x5f504 : word) = Some W_5f504.
Proof. vm_refl. Qed.
Lemma D_5f504 : decode_any W_5f504 = Some (Jal 0 2096164, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f508 : bv 32 := 0x00040a13.
Lemma F_5f508 : fetch_word AsanUbsan.M.loaded_segments (0x5f508 : word) = Some W_5f508.
Proof. vm_refl. Qed.
Lemma D_5f508 : decode_any W_5f508 = Some (OpImm ALU_ADD 20 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f50c : bv 32 := 0x5a0210ef.
Lemma F_5f50c : fetch_word AsanUbsan.M.loaded_segments (0x5f50c : word) = Some W_5f50c.
Proof. vm_refl. Qed.
Lemma D_5f50c : decode_any W_5f50c = Some (Jal 1 136608, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f510 : bv 32 := 0xfffb1597.
Lemma F_5f510 : fetch_word AsanUbsan.M.loaded_segments (0x5f510 : word) = Some W_5f510.
Proof. vm_refl. Qed.
Lemma D_5f510 : decode_any W_5f510 = Some (Auipc 11 1048497, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f514 : bv 32 := 0xef85b583.
Lemma F_5f514 : fetch_word AsanUbsan.M.loaded_segments (0x5f514 : word) = Some W_5f514.
Proof. vm_refl. Qed.
Lemma D_5f514 : decode_any W_5f514 = Some (Load SZ8 true 11 11 3832, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f518 : bv 32 := 0x00bab023.
Lemma F_5f518 : fetch_word AsanUbsan.M.loaded_segments (0x5f518 : word) = Some W_5f518.
Proof. vm_refl. Qed.
Lemma D_5f518 : decode_any W_5f518 = Some (Store SZ8 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f51c : bv 32 := 0x80040613.
Lemma F_5f51c : fetch_word AsanUbsan.M.loaded_segments (0x5f51c : word) = Some W_5f51c.
Proof. vm_refl. Qed.
Lemma D_5f51c : decode_any W_5f51c = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f520 : bv 32 := 0xfa060613.
Lemma F_5f520 : fetch_word AsanUbsan.M.loaded_segments (0x5f520 : word) = Some W_5f520.
Proof. vm_refl. Qed.
Lemma D_5f520 : decode_any W_5f520 = Some (OpImm ALU_ADD 12 12 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f524 : bv 32 := 0x00100713.
Lemma F_5f524 : fetch_word AsanUbsan.M.loaded_segments (0x5f524 : word) = Some W_5f524.
Proof. vm_refl. Qed.
Lemma D_5f524 : decode_any W_5f524 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f528 : bv 32 := 0x000a0593.
Lemma F_5f528 : fetch_word AsanUbsan.M.loaded_segments (0x5f528 : word) = Some W_5f528.
Proof. vm_refl. Qed.
Lemma D_5f528 : decode_any W_5f528 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f52c : bv 32 := 0x00098693.
Lemma F_5f52c : fetch_word AsanUbsan.M.loaded_segments (0x5f52c : word) = Some W_5f52c.
Proof. vm_refl. Qed.
Lemma D_5f52c : decode_any W_5f52c = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f530 : bv 32 := 0x00090793.
Lemma F_5f530 : fetch_word AsanUbsan.M.loaded_segments (0x5f530 : word) = Some W_5f530.
Proof. vm_refl. Qed.
Lemma D_5f530 : decode_any W_5f530 = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f534 : bv 32 := 0x00000813.
Lemma F_5f534 : fetch_word AsanUbsan.M.loaded_segments (0x5f534 : word) = Some W_5f534.
Proof. vm_refl. Qed.
Lemma D_5f534 : decode_any W_5f534 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f538 : bv 32 := 0x00000893.
Lemma F_5f538 : fetch_word AsanUbsan.M.loaded_segments (0x5f538 : word) = Some W_5f538.
Proof. vm_refl. Qed.
Lemma D_5f538 : decode_any W_5f538 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f53c : bv 32 := 0x5d1050ef.
Lemma F_5f53c : fetch_word AsanUbsan.M.loaded_segments (0x5f53c : word) = Some W_5f53c.
Proof. vm_refl. Qed.
Lemma D_5f53c : decode_any W_5f53c = Some (Jal 1 24016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f540 : bv 32 := 0x00048513.
Lemma F_5f540 : fetch_word AsanUbsan.M.loaded_segments (0x5f540 : word) = Some W_5f540.
Proof. vm_refl. Qed.
Lemma D_5f540 : decode_any W_5f540 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f544 : bv 32 := 0x000b0593.
Lemma F_5f544 : fetch_word AsanUbsan.M.loaded_segments (0x5f544 : word) = Some W_5f544.
Proof. vm_refl. Qed.
Lemma D_5f544 : decode_any W_5f544 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f548 : bv 32 := 0x00090613.
Lemma F_5f548 : fetch_word AsanUbsan.M.loaded_segments (0x5f548 : word) = Some W_5f548.
Proof. vm_refl. Qed.
Lemma D_5f548 : decode_any W_5f548 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f54c : bv 32 := 0xc29ff06f.
Lemma F_5f54c : fetch_word AsanUbsan.M.loaded_segments (0x5f54c : word) = Some W_5f54c.
Proof. vm_refl. Qed.
Lemma D_5f54c : decode_any W_5f54c = Some (Jal 0 2096168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f550 : bv 32 := 0x81010113.
Lemma F_5f550 : fetch_word AsanUbsan.M.loaded_segments (0x5f550 : word) = Some W_5f550.
Proof. vm_refl. Qed.
Lemma D_5f550 : decode_any W_5f550 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f554 : bv 32 := 0x7e113423.
Lemma F_5f554 : fetch_word AsanUbsan.M.loaded_segments (0x5f554 : word) = Some W_5f554.
Proof. vm_refl. Qed.
Lemma D_5f554 : decode_any W_5f554 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f558 : bv 32 := 0x7e813023.
Lemma F_5f558 : fetch_word AsanUbsan.M.loaded_segments (0x5f558 : word) = Some W_5f558.
Proof. vm_refl. Qed.
Lemma D_5f558 : decode_any W_5f558 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f55c : bv 32 := 0x7c913c23.
Lemma F_5f55c : fetch_word AsanUbsan.M.loaded_segments (0x5f55c : word) = Some W_5f55c.
Proof. vm_refl. Qed.
Lemma D_5f55c : decode_any W_5f55c = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f560 : bv 32 := 0x7d213823.
Lemma F_5f560 : fetch_word AsanUbsan.M.loaded_segments (0x5f560 : word) = Some W_5f560.
Proof. vm_refl. Qed.
Lemma D_5f560 : decode_any W_5f560 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f564 : bv 32 := 0x7d313423.
Lemma F_5f564 : fetch_word AsanUbsan.M.loaded_segments (0x5f564 : word) = Some W_5f564.
Proof. vm_refl. Qed.
Lemma D_5f564 : decode_any W_5f564 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f568 : bv 32 := 0x7d413023.
Lemma F_5f568 : fetch_word AsanUbsan.M.loaded_segments (0x5f568 : word) = Some W_5f568.
Proof. vm_refl. Qed.
Lemma D_5f568 : decode_any W_5f568 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f56c : bv 32 := 0x7b513c23.
Lemma F_5f56c : fetch_word AsanUbsan.M.loaded_segments (0x5f56c : word) = Some W_5f56c.
Proof. vm_refl. Qed.
Lemma D_5f56c : decode_any W_5f56c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f570 : bv 32 := 0x7b613823.
Lemma F_5f570 : fetch_word AsanUbsan.M.loaded_segments (0x5f570 : word) = Some W_5f570.
Proof. vm_refl. Qed.
Lemma D_5f570 : decode_any W_5f570 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f574 : bv 32 := 0x7b713423.
Lemma F_5f574 : fetch_word AsanUbsan.M.loaded_segments (0x5f574 : word) = Some W_5f574.
Proof. vm_refl. Qed.
Lemma D_5f574 : decode_any W_5f574 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f578 : bv 32 := 0x7b813023.
Lemma F_5f578 : fetch_word AsanUbsan.M.loaded_segments (0x5f578 : word) = Some W_5f578.
Proof. vm_refl. Qed.
Lemma D_5f578 : decode_any W_5f578 = Some (Store SZ8 2 24 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f57c : bv 32 := 0x7f010413.
Lemma F_5f57c : fetch_word AsanUbsan.M.loaded_segments (0x5f57c : word) = Some W_5f57c.
Proof. vm_refl. Qed.
Lemma D_5f57c : decode_any W_5f57c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f580 : bv 32 := 0xf8010113.
Lemma F_5f580 : fetch_word AsanUbsan.M.loaded_segments (0x5f580 : word) = Some W_5f580.
Proof. vm_refl. Qed.
Lemma D_5f580 : decode_any W_5f580 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f584 : bv 32 := 0x00078697.
Lemma F_5f584 : fetch_word AsanUbsan.M.loaded_segments (0x5f584 : word) = Some W_5f584.
Proof. vm_refl. Qed.
Lemma D_5f584 : decode_any W_5f584 = Some (Auipc 13 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f588 : bv 32 := 0xaac6b683.
Lemma F_5f588 : fetch_word AsanUbsan.M.loaded_segments (0x5f588 : word) = Some W_5f588.
Proof. vm_refl. Qed.
Lemma D_5f588 : decode_any W_5f588 = Some (Load SZ8 true 13 13 2732, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f58c : bv 32 := 0x0006c683.
Lemma F_5f58c : fetch_word AsanUbsan.M.loaded_segments (0x5f58c : word) = Some W_5f58c.
Proof. vm_refl. Qed.
Lemma D_5f58c : decode_any W_5f58c = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f590 : bv 32 := 0x0e068a63.
Lemma F_5f590 : fetch_word AsanUbsan.M.loaded_segments (0x5f590 : word) = Some W_5f590.
Proof. vm_refl. Qed.
Lemma D_5f590 : decode_any W_5f590 = Some (Branch BC_EQ 13 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f594 : bv 32 := 0x80040a93.
Lemma F_5f594 : fetch_word AsanUbsan.M.loaded_segments (0x5f594 : word) = Some W_5f594.
Proof. vm_refl. Qed.
Lemma D_5f594 : decode_any W_5f594 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f598 : bv 32 := 0xf98a8a93.
Lemma F_5f598 : fetch_word AsanUbsan.M.loaded_segments (0x5f598 : word) = Some W_5f598.
Proof. vm_refl. Qed.
Lemma D_5f598 : decode_any W_5f598 = Some (OpImm ALU_ADD 21 21 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f59c : bv 32 := 0x00c589b3.
Lemma F_5f59c : fetch_word AsanUbsan.M.loaded_segments (0x5f59c : word) = Some W_5f59c.
Proof. vm_refl. Qed.
Lemma D_5f59c : decode_any W_5f59c = Some (Op ALU_ADD 19 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5a0 : bv 32 := 0x00c50a33.
Lemma F_5f5a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f5a0 : word) = Some W_5f5a0.
Proof. vm_refl. Qed.
Lemma D_5f5a0 : decode_any W_5f5a0 = Some (Op ALU_ADD 20 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5a4 : bv 32 := 0x00b50663.
Lemma F_5f5a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f5a4 : word) = Some W_5f5a4.
Proof. vm_refl. Qed.
Lemma D_5f5a4 : decode_any W_5f5a4 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5a8 : bv 32 := 0x0145f463.
Lemma F_5f5a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f5a8 : word) = Some W_5f5a8.
Proof. vm_refl. Qed.
Lemma D_5f5a8 : decode_any W_5f5a8 = Some (Branch BC_GEU 11 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5ac : bv 32 := 0x1b356e63.
Lemma F_5f5ac : fetch_word AsanUbsan.M.loaded_segments (0x5f5ac : word) = Some W_5f5ac.
Proof. vm_refl. Qed.
Lemma D_5f5ac : decode_any W_5f5ac = Some (Branch BC_LTU 10 19 444, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5b0 : bv 32 := 0xfff5c693.
Lemma F_5f5b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f5b0 : word) = Some W_5f5b0.
Proof. vm_refl. Qed.
Lemma D_5f5b0 : decode_any W_5f5b0 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5b4 : bv 32 := 0x26c6e863.
Lemma F_5f5b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f5b4 : word) = Some W_5f5b4.
Proof. vm_refl. Qed.
Lemma D_5f5b4 : decode_any W_5f5b4 = Some (Branch BC_LTU 13 12 624, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5b8 : bv 32 := 0xfbf60b13.
Lemma F_5f5b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f5b8 : word) = Some W_5f5b8.
Proof. vm_refl. Qed.
Lemma D_5f5b8 : decode_any W_5f5b8 = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5bc : bv 32 := 0xfbf00693.
Lemma F_5f5bc : fetch_word AsanUbsan.M.loaded_segments (0x5f5bc : word) = Some W_5f5bc.
Proof. vm_refl. Qed.
Lemma D_5f5bc : decode_any W_5f5bc = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5c0 : bv 32 := 0x2f66f663.
Lemma F_5f5c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f5c0 : word) = Some W_5f5c0.
Proof. vm_refl. Qed.
Lemma D_5f5c0 : decode_any W_5f5c0 = Some (Branch BC_GEU 13 22 748, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5c4 : bv 32 := 0x00077697.
Lemma F_5f5c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f5c4 : word) = Some W_5f5c4.
Proof. vm_refl. Qed.
Lemma D_5f5c4 : decode_any W_5f5c4 = Some (Auipc 13 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5c8 : bv 32 := 0xf046b683.
Lemma F_5f5c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f5c8 : word) = Some W_5f5c8.
Proof. vm_refl. Qed.
Lemma D_5f5c8 : decode_any W_5f5c8 = Some (Load SZ8 true 13 13 3844, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5cc : bv 32 := 0x0006b703.
Lemma F_5f5cc : fetch_word AsanUbsan.M.loaded_segments (0x5f5cc : word) = Some W_5f5cc.
Proof. vm_refl. Qed.
Lemma D_5f5cc : decode_any W_5f5cc = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5d0 : bv 32 := 0xfff98993.
Lemma F_5f5d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f5d0 : word) = Some W_5f5d0.
Proof. vm_refl. Qed.
Lemma D_5f5d0 : decode_any W_5f5d0 = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5d4 : bv 32 := 0x0035d693.
Lemma F_5f5d4 : fetch_word AsanUbsan.M.loaded_segments (0x5f5d4 : word) = Some W_5f5d4.
Proof. vm_refl. Qed.
Lemma D_5f5d4 : decode_any W_5f5d4 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5d8 : bv 32 := 0x0039d793.
Lemma F_5f5d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f5d8 : word) = Some W_5f5d8.
Proof. vm_refl. Qed.
Lemma D_5f5d8 : decode_any W_5f5d8 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5dc : bv 32 := 0x00d706b3.
Lemma F_5f5dc : fetch_word AsanUbsan.M.loaded_segments (0x5f5dc : word) = Some W_5f5dc.
Proof. vm_refl. Qed.
Lemma D_5f5dc : decode_any W_5f5dc = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5e0 : bv 32 := 0x00f70733.
Lemma F_5f5e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f5e0 : word) = Some W_5f5e0.
Proof. vm_refl. Qed.
Lemma D_5f5e0 : decode_any W_5f5e0 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5e4 : bv 32 := 0xff86f793.
Lemma F_5f5e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f5e4 : word) = Some W_5f5e4.
Proof. vm_refl. Qed.
Lemma D_5f5e4 : decode_any W_5f5e4 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5e8 : bv 32 := 0xff877813.
Lemma F_5f5e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f5e8 : word) = Some W_5f5e8.
Proof. vm_refl. Qed.
Lemma D_5f5e8 : decode_any W_5f5e8 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5ec : bv 32 := 0x0007b783.
Lemma F_5f5ec : fetch_word AsanUbsan.M.loaded_segments (0x5f5ec : word) = Some W_5f5ec.
Proof. vm_refl. Qed.
Lemma D_5f5ec : decode_any W_5f5ec = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5f0 : bv 32 := 0x00083803.
Lemma F_5f5f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f5f0 : word) = Some W_5f5f0.
Proof. vm_refl. Qed.
Lemma D_5f5f0 : decode_any W_5f5f0 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5f4 : bv 32 := 0x00f867b3.
Lemma F_5f5f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f5f4 : word) = Some W_5f5f4.
Proof. vm_refl. Qed.
Lemma D_5f5f4 : decode_any W_5f5f4 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5f8 : bv 32 := 0x2a079e63.
Lemma F_5f5f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f5f8 : word) = Some W_5f5f8.
Proof. vm_refl. Qed.
Lemma D_5f5f8 : decode_any W_5f5f8 = Some (Branch BC_NE 15 0 700, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f5fc : bv 32 := 0xfff54693.
Lemma F_5f5fc : fetch_word AsanUbsan.M.loaded_segments (0x5f5fc : word) = Some W_5f5fc.
Proof. vm_refl. Qed.
Lemma D_5f5fc : decode_any W_5f5fc = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f600 : bv 32 := 0x0cc6ee63.
Lemma F_5f600 : fetch_word AsanUbsan.M.loaded_segments (0x5f600 : word) = Some W_5f600.
Proof. vm_refl. Qed.
Lemma D_5f600 : decode_any W_5f600 = Some (Branch BC_LTU 13 12 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f604 : bv 32 := 0xfbf00693.
Lemma F_5f604 : fetch_word AsanUbsan.M.loaded_segments (0x5f604 : word) = Some W_5f604.
Proof. vm_refl. Qed.
Lemma D_5f604 : decode_any W_5f604 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f608 : bv 32 := 0x1566fc63.
Lemma F_5f608 : fetch_word AsanUbsan.M.loaded_segments (0x5f608 : word) = Some W_5f608.
Proof. vm_refl. Qed.
Lemma D_5f608 : decode_any W_5f608 = Some (Branch BC_GEU 13 22 344, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f60c : bv 32 := 0x00077697.
Lemma F_5f60c : fetch_word AsanUbsan.M.loaded_segments (0x5f60c : word) = Some W_5f60c.
Proof. vm_refl. Qed.
Lemma D_5f60c : decode_any W_5f60c = Some (Auipc 13 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f610 : bv 32 := 0xebc6b683.
Lemma F_5f610 : fetch_word AsanUbsan.M.loaded_segments (0x5f610 : word) = Some W_5f610.
Proof. vm_refl. Qed.
Lemma D_5f610 : decode_any W_5f610 = Some (Load SZ8 true 13 13 3772, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f614 : bv 32 := 0x0006b703.
Lemma F_5f614 : fetch_word AsanUbsan.M.loaded_segments (0x5f614 : word) = Some W_5f614.
Proof. vm_refl. Qed.
Lemma D_5f614 : decode_any W_5f614 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f618 : bv 32 := 0xfffa0a13.
Lemma F_5f618 : fetch_word AsanUbsan.M.loaded_segments (0x5f618 : word) = Some W_5f618.
Proof. vm_refl. Qed.
Lemma D_5f618 : decode_any W_5f618 = Some (OpImm ALU_ADD 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f61c : bv 32 := 0x00355693.
Lemma F_5f61c : fetch_word AsanUbsan.M.loaded_segments (0x5f61c : word) = Some W_5f61c.
Proof. vm_refl. Qed.
Lemma D_5f61c : decode_any W_5f61c = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f620 : bv 32 := 0x003a5793.
Lemma F_5f620 : fetch_word AsanUbsan.M.loaded_segments (0x5f620 : word) = Some W_5f620.
Proof. vm_refl. Qed.
Lemma D_5f620 : decode_any W_5f620 = Some (ShiftImm ALU_SRL 15 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f624 : bv 32 := 0x00d706b3.
Lemma F_5f624 : fetch_word AsanUbsan.M.loaded_segments (0x5f624 : word) = Some W_5f624.
Proof. vm_refl. Qed.
Lemma D_5f624 : decode_any W_5f624 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f628 : bv 32 := 0x00f70733.
Lemma F_5f628 : fetch_word AsanUbsan.M.loaded_segments (0x5f628 : word) = Some W_5f628.
Proof. vm_refl. Qed.
Lemma D_5f628 : decode_any W_5f628 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f62c : bv 32 := 0xff86f793.
Lemma F_5f62c : fetch_word AsanUbsan.M.loaded_segments (0x5f62c : word) = Some W_5f62c.
Proof. vm_refl. Qed.
Lemma D_5f62c : decode_any W_5f62c = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f630 : bv 32 := 0xff877813.
Lemma F_5f630 : fetch_word AsanUbsan.M.loaded_segments (0x5f630 : word) = Some W_5f630.
Proof. vm_refl. Qed.
Lemma D_5f630 : decode_any W_5f630 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f634 : bv 32 := 0x0007b783.
Lemma F_5f634 : fetch_word AsanUbsan.M.loaded_segments (0x5f634 : word) = Some W_5f634.
Proof. vm_refl. Qed.
Lemma D_5f634 : decode_any W_5f634 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f638 : bv 32 := 0x00083803.
Lemma F_5f638 : fetch_word AsanUbsan.M.loaded_segments (0x5f638 : word) = Some W_5f638.
Proof. vm_refl. Qed.
Lemma D_5f638 : decode_any W_5f638 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f63c : bv 32 := 0x00f867b3.
Lemma F_5f63c : fetch_word AsanUbsan.M.loaded_segments (0x5f63c : word) = Some W_5f63c.
Proof. vm_refl. Qed.
Lemma D_5f63c : decode_any W_5f63c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f640 : bv 32 := 0x36079a63.
Lemma F_5f640 : fetch_word AsanUbsan.M.loaded_segments (0x5f640 : word) = Some W_5f640.
Proof. vm_refl. Qed.
Lemma D_5f640 : decode_any W_5f640 = Some (Branch BC_NE 15 0 884, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f644 : bv 32 := 0x00079697.
Lemma F_5f644 : fetch_word AsanUbsan.M.loaded_segments (0x5f644 : word) = Some W_5f644.
Proof. vm_refl. Qed.
Lemma D_5f644 : decode_any W_5f644 = Some (Auipc 13 121, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f648 : bv 32 := 0xddc6b683.
Lemma F_5f648 : fetch_word AsanUbsan.M.loaded_segments (0x5f648 : word) = Some W_5f648.
Proof. vm_refl. Qed.
Lemma D_5f648 : decode_any W_5f648 = Some (Load SZ8 true 13 13 3548, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f64c : bv 32 := 0x000680e7.
Lemma F_5f64c : fetch_word AsanUbsan.M.loaded_segments (0x5f64c : word) = Some W_5f64c.
Proof. vm_refl. Qed.
Lemma D_5f64c : decode_any W_5f64c = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f650 : bv 32 := 0x08010113.
Lemma F_5f650 : fetch_word AsanUbsan.M.loaded_segments (0x5f650 : word) = Some W_5f650.
Proof. vm_refl. Qed.
Lemma D_5f650 : decode_any W_5f650 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f654 : bv 32 := 0x7e813083.
Lemma F_5f654 : fetch_word AsanUbsan.M.loaded_segments (0x5f654 : word) = Some W_5f654.
Proof. vm_refl. Qed.
Lemma D_5f654 : decode_any W_5f654 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f658 : bv 32 := 0x7e013403.
Lemma F_5f658 : fetch_word AsanUbsan.M.loaded_segments (0x5f658 : word) = Some W_5f658.
Proof. vm_refl. Qed.
Lemma D_5f658 : decode_any W_5f658 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f65c : bv 32 := 0x7d813483.
Lemma F_5f65c : fetch_word AsanUbsan.M.loaded_segments (0x5f65c : word) = Some W_5f65c.
Proof. vm_refl. Qed.
Lemma D_5f65c : decode_any W_5f65c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f660 : bv 32 := 0x7d013903.
Lemma F_5f660 : fetch_word AsanUbsan.M.loaded_segments (0x5f660 : word) = Some W_5f660.
Proof. vm_refl. Qed.
Lemma D_5f660 : decode_any W_5f660 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f664 : bv 32 := 0x7c813983.
Lemma F_5f664 : fetch_word AsanUbsan.M.loaded_segments (0x5f664 : word) = Some W_5f664.
Proof. vm_refl. Qed.
Lemma D_5f664 : decode_any W_5f664 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f668 : bv 32 := 0x7c013a03.
Lemma F_5f668 : fetch_word AsanUbsan.M.loaded_segments (0x5f668 : word) = Some W_5f668.
Proof. vm_refl. Qed.
Lemma D_5f668 : decode_any W_5f668 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f66c : bv 32 := 0x7b813a83.
Lemma F_5f66c : fetch_word AsanUbsan.M.loaded_segments (0x5f66c : word) = Some W_5f66c.
Proof. vm_refl. Qed.
Lemma D_5f66c : decode_any W_5f66c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f670 : bv 32 := 0x7b013b03.
Lemma F_5f670 : fetch_word AsanUbsan.M.loaded_segments (0x5f670 : word) = Some W_5f670.
Proof. vm_refl. Qed.
Lemma D_5f670 : decode_any W_5f670 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f674 : bv 32 := 0x7a813b83.
Lemma F_5f674 : fetch_word AsanUbsan.M.loaded_segments (0x5f674 : word) = Some W_5f674.
Proof. vm_refl. Qed.
Lemma D_5f674 : decode_any W_5f674 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f678 : bv 32 := 0x7a013c03.
Lemma F_5f678 : fetch_word AsanUbsan.M.loaded_segments (0x5f678 : word) = Some W_5f678.
Proof. vm_refl. Qed.
Lemma D_5f678 : decode_any W_5f678 = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f67c : bv 32 := 0x7f010113.
Lemma F_5f67c : fetch_word AsanUbsan.M.loaded_segments (0x5f67c : word) = Some W_5f67c.
Proof. vm_refl. Qed.
Lemma D_5f67c : decode_any W_5f67c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f680 : bv 32 := 0x00008067.
Lemma F_5f680 : fetch_word AsanUbsan.M.loaded_segments (0x5f680 : word) = Some W_5f680.
Proof. vm_refl. Qed.
Lemma D_5f680 : decode_any W_5f680 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f684 : bv 32 := 0x00060913.
Lemma F_5f684 : fetch_word AsanUbsan.M.loaded_segments (0x5f684 : word) = Some W_5f684.
Proof. vm_refl. Qed.
Lemma D_5f684 : decode_any W_5f684 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f688 : bv 32 := 0x00058993.
Lemma F_5f688 : fetch_word AsanUbsan.M.loaded_segments (0x5f688 : word) = Some W_5f688.
Proof. vm_refl. Qed.
Lemma D_5f688 : decode_any W_5f688 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f68c : bv 32 := 0x00050493.
Lemma F_5f68c : fetch_word AsanUbsan.M.loaded_segments (0x5f68c : word) = Some W_5f68c.
Proof. vm_refl. Qed.
Lemma D_5f68c : decode_any W_5f68c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f690 : bv 32 := 0x4c5060ef.
Lemma F_5f690 : fetch_word AsanUbsan.M.loaded_segments (0x5f690 : word) = Some W_5f690.
Proof. vm_refl. Qed.
Lemma D_5f690 : decode_any W_5f690 = Some (Jal 1 27844, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f694 : bv 32 := 0x00098593.
Lemma F_5f694 : fetch_word AsanUbsan.M.loaded_segments (0x5f694 : word) = Some W_5f694.
Proof. vm_refl. Qed.
Lemma D_5f694 : decode_any W_5f694 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f698 : bv 32 := 0x00090613.
Lemma F_5f698 : fetch_word AsanUbsan.M.loaded_segments (0x5f698 : word) = Some W_5f698.
Proof. vm_refl. Qed.
Lemma D_5f698 : decode_any W_5f698 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f69c : bv 32 := 0x00050693.
Lemma F_5f69c : fetch_word AsanUbsan.M.loaded_segments (0x5f69c : word) = Some W_5f69c.
Proof. vm_refl. Qed.
Lemma D_5f69c : decode_any W_5f69c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6a0 : bv 32 := 0x00048513.
Lemma F_5f6a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f6a0 : word) = Some W_5f6a0.
Proof. vm_refl. Qed.
Lemma D_5f6a0 : decode_any W_5f6a0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6a4 : bv 32 := 0xfa0690e3.
Lemma F_5f6a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f6a4 : word) = Some W_5f6a4.
Proof. vm_refl. Qed.
Lemma D_5f6a4 : decode_any W_5f6a4 = Some (Branch BC_NE 13 0 8096, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6a8 : bv 32 := 0x08010113.
Lemma F_5f6a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f6a8 : word) = Some W_5f6a8.
Proof. vm_refl. Qed.
Lemma D_5f6a8 : decode_any W_5f6a8 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6ac : bv 32 := 0x7e813083.
Lemma F_5f6ac : fetch_word AsanUbsan.M.loaded_segments (0x5f6ac : word) = Some W_5f6ac.
Proof. vm_refl. Qed.
Lemma D_5f6ac : decode_any W_5f6ac = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6b0 : bv 32 := 0x7e013403.
Lemma F_5f6b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f6b0 : word) = Some W_5f6b0.
Proof. vm_refl. Qed.
Lemma D_5f6b0 : decode_any W_5f6b0 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6b4 : bv 32 := 0x7d813483.
Lemma F_5f6b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f6b4 : word) = Some W_5f6b4.
Proof. vm_refl. Qed.
Lemma D_5f6b4 : decode_any W_5f6b4 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6b8 : bv 32 := 0x7d013903.
Lemma F_5f6b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f6b8 : word) = Some W_5f6b8.
Proof. vm_refl. Qed.
Lemma D_5f6b8 : decode_any W_5f6b8 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6bc : bv 32 := 0x7c813983.
Lemma F_5f6bc : fetch_word AsanUbsan.M.loaded_segments (0x5f6bc : word) = Some W_5f6bc.
Proof. vm_refl. Qed.
Lemma D_5f6bc : decode_any W_5f6bc = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6c0 : bv 32 := 0x7c013a03.
Lemma F_5f6c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f6c0 : word) = Some W_5f6c0.
Proof. vm_refl. Qed.
Lemma D_5f6c0 : decode_any W_5f6c0 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6c4 : bv 32 := 0x7b813a83.
Lemma F_5f6c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f6c4 : word) = Some W_5f6c4.
Proof. vm_refl. Qed.
Lemma D_5f6c4 : decode_any W_5f6c4 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6c8 : bv 32 := 0x7b013b03.
Lemma F_5f6c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f6c8 : word) = Some W_5f6c8.
Proof. vm_refl. Qed.
Lemma D_5f6c8 : decode_any W_5f6c8 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6cc : bv 32 := 0x7a813b83.
Lemma F_5f6cc : fetch_word AsanUbsan.M.loaded_segments (0x5f6cc : word) = Some W_5f6cc.
Proof. vm_refl. Qed.
Lemma D_5f6cc : decode_any W_5f6cc = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6d0 : bv 32 := 0x7a013c03.
Lemma F_5f6d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f6d0 : word) = Some W_5f6d0.
Proof. vm_refl. Qed.
Lemma D_5f6d0 : decode_any W_5f6d0 = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6d4 : bv 32 := 0x7f010113.
Lemma F_5f6d4 : fetch_word AsanUbsan.M.loaded_segments (0x5f6d4 : word) = Some W_5f6d4.
Proof. vm_refl. Qed.
Lemma D_5f6d4 : decode_any W_5f6d4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6d8 : bv 32 := 0x68d1106f.
Lemma F_5f6d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f6d8 : word) = Some W_5f6d8.
Proof. vm_refl. Qed.
Lemma D_5f6d8 : decode_any W_5f6d8 = Some (Jal 0 73356, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6dc : bv 32 := 0x80040693.
Lemma F_5f6dc : fetch_word AsanUbsan.M.loaded_segments (0x5f6dc : word) = Some W_5f6dc.
Proof. vm_refl. Qed.
Lemma D_5f6dc : decode_any W_5f6dc = Some (OpImm ALU_ADD 13 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6e0 : bv 32 := 0xfa868693.
Lemma F_5f6e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f6e0 : word) = Some W_5f6e0.
Proof. vm_refl. Qed.
Lemma D_5f6e0 : decode_any W_5f6e0 = Some (OpImm ALU_ADD 13 13 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6e4 : bv 32 := 0x80040713.
Lemma F_5f6e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f6e4 : word) = Some W_5f6e4.
Proof. vm_refl. Qed.
Lemma D_5f6e4 : decode_any W_5f6e4 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6e8 : bv 32 := 0xf9870713.
Lemma F_5f6e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f6e8 : word) = Some W_5f6e8.
Proof. vm_refl. Qed.
Lemma D_5f6e8 : decode_any W_5f6e8 = Some (OpImm ALU_ADD 14 14 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6ec : bv 32 := 0x7ff70b93.
Lemma F_5f6ec : fetch_word AsanUbsan.M.loaded_segments (0x5f6ec : word) = Some W_5f6ec.
Proof. vm_refl. Qed.
Lemma D_5f6ec : decode_any W_5f6ec = Some (OpImm ALU_ADD 23 14 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6f0 : bv 32 := 0x000bb4a3.
Lemma F_5f6f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f6f0 : word) = Some W_5f6f0.
Proof. vm_refl. Qed.
Lemma D_5f6f0 : decode_any W_5f6f0 = Some (Store SZ8 23 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6f4 : bv 32 := 0x00dab023.
Lemma F_5f6f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f6f4 : word) = Some W_5f6f4.
Proof. vm_refl. Qed.
Lemma D_5f6f4 : decode_any W_5f6f4 = Some (Store SZ8 21 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6f8 : bv 32 := 0x000ab423.
Lemma F_5f6f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f6f8 : word) = Some W_5f6f8.
Proof. vm_refl. Qed.
Lemma D_5f6f8 : decode_any W_5f6f8 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f6fc : bv 32 := 0x00060493.
Lemma F_5f6fc : fetch_word AsanUbsan.M.loaded_segments (0x5f6fc : word) = Some W_5f6fc.
Proof. vm_refl. Qed.
Lemma D_5f6fc : decode_any W_5f6fc = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f700 : bv 32 := 0x00058993.
Lemma F_5f700 : fetch_word AsanUbsan.M.loaded_segments (0x5f700 : word) = Some W_5f700.
Proof. vm_refl. Qed.
Lemma D_5f700 : decode_any W_5f700 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f704 : bv 32 := 0x00050913.
Lemma F_5f704 : fetch_word AsanUbsan.M.loaded_segments (0x5f704 : word) = Some W_5f704.
Proof. vm_refl. Qed.
Lemma D_5f704 : decode_any W_5f704 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f708 : bv 32 := 0x3a4210ef.
Lemma F_5f708 : fetch_word AsanUbsan.M.loaded_segments (0x5f708 : word) = Some W_5f708.
Proof. vm_refl. Qed.
Lemma D_5f708 : decode_any W_5f708 = Some (Jal 1 136100, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f70c : bv 32 := 0x00050593.
Lemma F_5f70c : fetch_word AsanUbsan.M.loaded_segments (0x5f70c : word) = Some W_5f70c.
Proof. vm_refl. Qed.
Lemma D_5f70c : decode_any W_5f70c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f710 : bv 32 := 0x00077517.
Lemma F_5f710 : fetch_word AsanUbsan.M.loaded_segments (0x5f710 : word) = Some W_5f710.
Proof. vm_refl. Qed.
Lemma D_5f710 : decode_any W_5f710 = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f714 : bv 32 := 0xda853503.
Lemma F_5f714 : fetch_word AsanUbsan.M.loaded_segments (0x5f714 : word) = Some W_5f714.
Proof. vm_refl. Qed.
Lemma D_5f714 : decode_any W_5f714 = Some (Load SZ8 true 10 10 3496, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f718 : bv 32 := 0x02154703.
Lemma F_5f718 : fetch_word AsanUbsan.M.loaded_segments (0x5f718 : word) = Some W_5f718.
Proof. vm_refl. Qed.
Lemma D_5f718 : decode_any W_5f718 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f71c : bv 32 := 0x008bb4a3.
Lemma F_5f71c : fetch_word AsanUbsan.M.loaded_segments (0x5f71c : word) = Some W_5f71c.
Proof. vm_refl. Qed.
Lemma D_5f71c : decode_any W_5f71c = Some (Store SZ8 23 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f720 : bv 32 := 0x80040513.
Lemma F_5f720 : fetch_word AsanUbsan.M.loaded_segments (0x5f720 : word) = Some W_5f720.
Proof. vm_refl. Qed.
Lemma D_5f720 : decode_any W_5f720 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f724 : bv 32 := 0xf9850513.
Lemma F_5f724 : fetch_word AsanUbsan.M.loaded_segments (0x5f724 : word) = Some W_5f724.
Proof. vm_refl. Qed.
Lemma D_5f724 : decode_any W_5f724 = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f728 : bv 32 := 0x0ff00793.
Lemma F_5f728 : fetch_word AsanUbsan.M.loaded_segments (0x5f728 : word) = Some W_5f728.
Proof. vm_refl. Qed.
Lemma D_5f728 : decode_any W_5f728 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f72c : bv 32 := 0x00040613.
Lemma F_5f72c : fetch_word AsanUbsan.M.loaded_segments (0x5f72c : word) = Some W_5f72c.
Proof. vm_refl. Qed.
Lemma D_5f72c : decode_any W_5f72c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f730 : bv 32 := 0x00000693.
Lemma F_5f730 : fetch_word AsanUbsan.M.loaded_segments (0x5f730 : word) = Some W_5f730.
Proof. vm_refl. Qed.
Lemma D_5f730 : decode_any W_5f730 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f734 : bv 32 := 0x0c9080ef.
Lemma F_5f734 : fetch_word AsanUbsan.M.loaded_segments (0x5f734 : word) = Some W_5f734.
Proof. vm_refl. Qed.
Lemma D_5f734 : decode_any W_5f734 = Some (Jal 1 35016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f738 : bv 32 := 0x80040613.
Lemma F_5f738 : fetch_word AsanUbsan.M.loaded_segments (0x5f738 : word) = Some W_5f738.
Proof. vm_refl. Qed.
Lemma D_5f738 : decode_any W_5f738 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f73c : bv 32 := 0xf9860613.
Lemma F_5f73c : fetch_word AsanUbsan.M.loaded_segments (0x5f73c : word) = Some W_5f73c.
Proof. vm_refl. Qed.
Lemma D_5f73c : decode_any W_5f73c = Some (OpImm ALU_ADD 12 12 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f740 : bv 32 := 0x00090513.
Lemma F_5f740 : fetch_word AsanUbsan.M.loaded_segments (0x5f740 : word) = Some W_5f740.
Proof. vm_refl. Qed.
Lemma D_5f740 : decode_any W_5f740 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f744 : bv 32 := 0x00048593.
Lemma F_5f744 : fetch_word AsanUbsan.M.loaded_segments (0x5f744 : word) = Some W_5f744.
Proof. vm_refl. Qed.
Lemma D_5f744 : decode_any W_5f744 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f748 : bv 32 := 0x66c050ef.
Lemma F_5f748 : fetch_word AsanUbsan.M.loaded_segments (0x5f748 : word) = Some W_5f748.
Proof. vm_refl. Qed.
Lemma D_5f748 : decode_any W_5f748 = Some (Jal 1 22124, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f74c : bv 32 := 0x00090513.
Lemma F_5f74c : fetch_word AsanUbsan.M.loaded_segments (0x5f74c : word) = Some W_5f74c.
Proof. vm_refl. Qed.
Lemma D_5f74c : decode_any W_5f74c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f750 : bv 32 := 0x00098593.
Lemma F_5f750 : fetch_word AsanUbsan.M.loaded_segments (0x5f750 : word) = Some W_5f750.
Proof. vm_refl. Qed.
Lemma D_5f750 : decode_any W_5f750 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f754 : bv 32 := 0x00048613.
Lemma F_5f754 : fetch_word AsanUbsan.M.loaded_segments (0x5f754 : word) = Some W_5f754.
Proof. vm_refl. Qed.
Lemma D_5f754 : decode_any W_5f754 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f758 : bv 32 := 0xfbf00693.
Lemma F_5f758 : fetch_word AsanUbsan.M.loaded_segments (0x5f758 : word) = Some W_5f758.
Proof. vm_refl. Qed.
Lemma D_5f758 : decode_any W_5f758 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f75c : bv 32 := 0xeb66e8e3.
Lemma F_5f75c : fetch_word AsanUbsan.M.loaded_segments (0x5f75c : word) = Some W_5f75c.
Proof. vm_refl. Qed.
Lemma D_5f75c : decode_any W_5f75c = Some (Branch BC_LTU 13 22 7856, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f760 : bv 32 := 0x28061463.
Lemma F_5f760 : fetch_word AsanUbsan.M.loaded_segments (0x5f760 : word) = Some W_5f760.
Proof. vm_refl. Qed.
Lemma D_5f760 : decode_any W_5f760 = Some (Branch BC_NE 12 0 648, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f764 : bv 32 := 0xee1ff06f.
Lemma F_5f764 : fetch_word AsanUbsan.M.loaded_segments (0x5f764 : word) = Some W_5f764.
Proof. vm_refl. Qed.
Lemma D_5f764 : decode_any W_5f764 = Some (Jal 0 2096864, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f768 : bv 32 := 0x00050493.
Lemma F_5f768 : fetch_word AsanUbsan.M.loaded_segments (0x5f768 : word) = Some W_5f768.
Proof. vm_refl. Qed.
Lemma D_5f768 : decode_any W_5f768 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f76c : bv 32 := 0x00058913.
Lemma F_5f76c : fetch_word AsanUbsan.M.loaded_segments (0x5f76c : word) = Some W_5f76c.
Proof. vm_refl. Qed.
Lemma D_5f76c : decode_any W_5f76c = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f770 : bv 32 := 0x00060b13.
Lemma F_5f770 : fetch_word AsanUbsan.M.loaded_segments (0x5f770 : word) = Some W_5f770.
Proof. vm_refl. Qed.
Lemma D_5f770 : decode_any W_5f770 = Some (OpImm ALU_ADD 22 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f774 : bv 32 := 0x80040513.
Lemma F_5f774 : fetch_word AsanUbsan.M.loaded_segments (0x5f774 : word) = Some W_5f774.
Proof. vm_refl. Qed.
Lemma D_5f774 : decode_any W_5f774 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f778 : bv 32 := 0xfa850513.
Lemma F_5f778 : fetch_word AsanUbsan.M.loaded_segments (0x5f778 : word) = Some W_5f778.
Proof. vm_refl. Qed.
Lemma D_5f778 : decode_any W_5f778 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f77c : bv 32 := 0x80040593.
Lemma F_5f77c : fetch_word AsanUbsan.M.loaded_segments (0x5f77c : word) = Some W_5f77c.
Proof. vm_refl. Qed.
Lemma D_5f77c : decode_any W_5f77c = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f780 : bv 32 := 0xf9858593.
Lemma F_5f780 : fetch_word AsanUbsan.M.loaded_segments (0x5f780 : word) = Some W_5f780.
Proof. vm_refl. Qed.
Lemma D_5f780 : decode_any W_5f780 = Some (OpImm ALU_ADD 11 11 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f784 : bv 32 := 0x7ff58b93.
Lemma F_5f784 : fetch_word AsanUbsan.M.loaded_segments (0x5f784 : word) = Some W_5f784.
Proof. vm_refl. Qed.
Lemma D_5f784 : decode_any W_5f784 = Some (OpImm ALU_ADD 23 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f788 : bv 32 := 0x000bb4a3.
Lemma F_5f788 : fetch_word AsanUbsan.M.loaded_segments (0x5f788 : word) = Some W_5f788.
Proof. vm_refl. Qed.
Lemma D_5f788 : decode_any W_5f788 = Some (Store SZ8 23 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f78c : bv 32 := 0x00aab023.
Lemma F_5f78c : fetch_word AsanUbsan.M.loaded_segments (0x5f78c : word) = Some W_5f78c.
Proof. vm_refl. Qed.
Lemma D_5f78c : decode_any W_5f78c = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f790 : bv 32 := 0x000ab423.
Lemma F_5f790 : fetch_word AsanUbsan.M.loaded_segments (0x5f790 : word) = Some W_5f790.
Proof. vm_refl. Qed.
Lemma D_5f790 : decode_any W_5f790 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f794 : bv 32 := 0x318210ef.
Lemma F_5f794 : fetch_word AsanUbsan.M.loaded_segments (0x5f794 : word) = Some W_5f794.
Proof. vm_refl. Qed.
Lemma D_5f794 : decode_any W_5f794 = Some (Jal 1 135960, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f798 : bv 32 := 0x00050593.
Lemma F_5f798 : fetch_word AsanUbsan.M.loaded_segments (0x5f798 : word) = Some W_5f798.
Proof. vm_refl. Qed.
Lemma D_5f798 : decode_any W_5f798 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f79c : bv 32 := 0x00077517.
Lemma F_5f79c : fetch_word AsanUbsan.M.loaded_segments (0x5f79c : word) = Some W_5f79c.
Proof. vm_refl. Qed.
Lemma D_5f79c : decode_any W_5f79c = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7a0 : bv 32 := 0xd1c53503.
Lemma F_5f7a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f7a0 : word) = Some W_5f7a0.
Proof. vm_refl. Qed.
Lemma D_5f7a0 : decode_any W_5f7a0 = Some (Load SZ8 true 10 10 3356, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7a4 : bv 32 := 0x02154703.
Lemma F_5f7a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f7a4 : word) = Some W_5f7a4.
Proof. vm_refl. Qed.
Lemma D_5f7a4 : decode_any W_5f7a4 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7a8 : bv 32 := 0x008bb4a3.
Lemma F_5f7a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f7a8 : word) = Some W_5f7a8.
Proof. vm_refl. Qed.
Lemma D_5f7a8 : decode_any W_5f7a8 = Some (Store SZ8 23 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7ac : bv 32 := 0x80040513.
Lemma F_5f7ac : fetch_word AsanUbsan.M.loaded_segments (0x5f7ac : word) = Some W_5f7ac.
Proof. vm_refl. Qed.
Lemma D_5f7ac : decode_any W_5f7ac = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7b0 : bv 32 := 0xf9850513.
Lemma F_5f7b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f7b0 : word) = Some W_5f7b0.
Proof. vm_refl. Qed.
Lemma D_5f7b0 : decode_any W_5f7b0 = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7b4 : bv 32 := 0x0ff00793.
Lemma F_5f7b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f7b4 : word) = Some W_5f7b4.
Proof. vm_refl. Qed.
Lemma D_5f7b4 : decode_any W_5f7b4 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7b8 : bv 32 := 0x00040613.
Lemma F_5f7b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f7b8 : word) = Some W_5f7b8.
Proof. vm_refl. Qed.
Lemma D_5f7b8 : decode_any W_5f7b8 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7bc : bv 32 := 0x00000693.
Lemma F_5f7bc : fetch_word AsanUbsan.M.loaded_segments (0x5f7bc : word) = Some W_5f7bc.
Proof. vm_refl. Qed.
Lemma D_5f7bc : decode_any W_5f7bc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7c0 : bv 32 := 0x03d080ef.
Lemma F_5f7c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f7c0 : word) = Some W_5f7c0.
Proof. vm_refl. Qed.
Lemma D_5f7c0 : decode_any W_5f7c0 = Some (Jal 1 34876, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7c4 : bv 32 := 0xfffb6517.
Lemma F_5f7c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f7c4 : word) = Some W_5f7c4.
Proof. vm_refl. Qed.
Lemma D_5f7c4 : decode_any W_5f7c4 = Some (Auipc 10 1048502, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7c8 : bv 32 := 0x8c050513.
Lemma F_5f7c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f7c8 : word) = Some W_5f7c8.
Proof. vm_refl. Qed.
Lemma D_5f7c8 : decode_any W_5f7c8 = Some (OpImm ALU_ADD 10 10 2240, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7cc : bv 32 := 0x7dc090ef.
Lemma F_5f7cc : fetch_word AsanUbsan.M.loaded_segments (0x5f7cc : word) = Some W_5f7cc.
Proof. vm_refl. Qed.
Lemma D_5f7cc : decode_any W_5f7cc = Some (Jal 1 38876, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7d0 : bv 32 := 0x04051063.
Lemma F_5f7d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f7d0 : word) = Some W_5f7d0.
Proof. vm_refl. Qed.
Lemma D_5f7d0 : decode_any W_5f7d0 = Some (Branch BC_NE 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7d4 : bv 32 := 0x03d090ef.
Lemma F_5f7d4 : fetch_word AsanUbsan.M.loaded_segments (0x5f7d4 : word) = Some W_5f7d4.
Proof. vm_refl. Qed.
Lemma D_5f7d4 : decode_any W_5f7d4 = Some (Jal 1 38972, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7d8 : bv 32 := 0x00050a63.
Lemma F_5f7d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f7d8 : word) = Some W_5f7d8.
Proof. vm_refl. Qed.
Lemma D_5f7d8 : decode_any W_5f7d8 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7dc : bv 32 := 0x80040513.
Lemma F_5f7dc : fetch_word AsanUbsan.M.loaded_segments (0x5f7dc : word) = Some W_5f7dc.
Proof. vm_refl. Qed.
Lemma D_5f7dc : decode_any W_5f7dc = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7e0 : bv 32 := 0xf9850513.
Lemma F_5f7e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f7e0 : word) = Some W_5f7e0.
Proof. vm_refl. Qed.
Lemma D_5f7e0 : decode_any W_5f7e0 = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7e4 : bv 32 := 0x335090ef.
Lemma F_5f7e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f7e4 : word) = Some W_5f7e4.
Proof. vm_refl. Qed.
Lemma D_5f7e4 : decode_any W_5f7e4 = Some (Jal 1 39732, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7e8 : bv 32 := 0x02051463.
Lemma F_5f7e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f7e8 : word) = Some W_5f7e8.
Proof. vm_refl. Qed.
Lemma D_5f7e8 : decode_any W_5f7e8 = Some (Branch BC_NE 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7ec : bv 32 := 0xfffb6517.
Lemma F_5f7ec : fetch_word AsanUbsan.M.loaded_segments (0x5f7ec : word) = Some W_5f7ec.
Proof. vm_refl. Qed.
Lemma D_5f7ec : decode_any W_5f7ec = Some (Auipc 10 1048502, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7f0 : bv 32 := 0x89850513.
Lemma F_5f7f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f7f0 : word) = Some W_5f7f0.
Proof. vm_refl. Qed.
Lemma D_5f7f0 : decode_any W_5f7f0 = Some (OpImm ALU_ADD 10 10 2200, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7f4 : bv 32 := 0x80040793.
Lemma F_5f7f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f7f4 : word) = Some W_5f7f4.
Proof. vm_refl. Qed.
Lemma D_5f7f4 : decode_any W_5f7f4 = Some (OpImm ALU_ADD 15 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7f8 : bv 32 := 0xf9878793.
Lemma F_5f7f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f7f8 : word) = Some W_5f7f8.
Proof. vm_refl. Qed.
Lemma D_5f7f8 : decode_any W_5f7f8 = Some (OpImm ALU_ADD 15 15 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f7fc : bv 32 := 0x00048593.
Lemma F_5f7fc : fetch_word AsanUbsan.M.loaded_segments (0x5f7fc : word) = Some W_5f7fc.
Proof. vm_refl. Qed.
Lemma D_5f7fc : decode_any W_5f7fc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f800 : bv 32 := 0x000b0613.
Lemma F_5f800 : fetch_word AsanUbsan.M.loaded_segments (0x5f800 : word) = Some W_5f800.
Proof. vm_refl. Qed.
Lemma D_5f800 : decode_any W_5f800 = Some (OpImm ALU_ADD 12 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f804 : bv 32 := 0x00090693.
Lemma F_5f804 : fetch_word AsanUbsan.M.loaded_segments (0x5f804 : word) = Some W_5f804.
Proof. vm_refl. Qed.
Lemma D_5f804 : decode_any W_5f804 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f808 : bv 32 := 0x000b0713.
Lemma F_5f808 : fetch_word AsanUbsan.M.loaded_segments (0x5f808 : word) = Some W_5f808.
Proof. vm_refl. Qed.
Lemma D_5f808 : decode_any W_5f808 = Some (OpImm ALU_ADD 14 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f80c : bv 32 := 0x2d4050ef.
Lemma F_5f80c : fetch_word AsanUbsan.M.loaded_segments (0x5f80c : word) = Some W_5f80c.
Proof. vm_refl. Qed.
Lemma D_5f80c : decode_any W_5f80c = Some (Jal 1 21204, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f810 : bv 32 := 0x000b0613.
Lemma F_5f810 : fetch_word AsanUbsan.M.loaded_segments (0x5f810 : word) = Some W_5f810.
Proof. vm_refl. Qed.
Lemma D_5f810 : decode_any W_5f810 = Some (OpImm ALU_ADD 12 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f814 : bv 32 := 0x00090593.
Lemma F_5f814 : fetch_word AsanUbsan.M.loaded_segments (0x5f814 : word) = Some W_5f814.
Proof. vm_refl. Qed.
Lemma D_5f814 : decode_any W_5f814 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f818 : bv 32 := 0x00048513.
Lemma F_5f818 : fetch_word AsanUbsan.M.loaded_segments (0x5f818 : word) = Some W_5f818.
Proof. vm_refl. Qed.
Lemma D_5f818 : decode_any W_5f818 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f81c : bv 32 := 0xfff94693.
Lemma F_5f81c : fetch_word AsanUbsan.M.loaded_segments (0x5f81c : word) = Some W_5f81c.
Proof. vm_refl. Qed.
Lemma D_5f81c : decode_any W_5f81c = Some (OpImm ALU_XOR 13 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f820 : bv 32 := 0xd966fce3.
Lemma F_5f820 : fetch_word AsanUbsan.M.loaded_segments (0x5f820 : word) = Some W_5f820.
Proof. vm_refl. Qed.
Lemma D_5f820 : decode_any W_5f820 = Some (Branch BC_GEU 13 22 7576, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f824 : bv 32 := 0x80040693.
Lemma F_5f824 : fetch_word AsanUbsan.M.loaded_segments (0x5f824 : word) = Some W_5f824.
Proof. vm_refl. Qed.
Lemma D_5f824 : decode_any W_5f824 = Some (OpImm ALU_ADD 13 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f828 : bv 32 := 0xfa868693.
Lemma F_5f828 : fetch_word AsanUbsan.M.loaded_segments (0x5f828 : word) = Some W_5f828.
Proof. vm_refl. Qed.
Lemma D_5f828 : decode_any W_5f828 = Some (OpImm ALU_ADD 13 13 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f82c : bv 32 := 0x80040713.
Lemma F_5f82c : fetch_word AsanUbsan.M.loaded_segments (0x5f82c : word) = Some W_5f82c.
Proof. vm_refl. Qed.
Lemma D_5f82c : decode_any W_5f82c = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f830 : bv 32 := 0xf9870713.
Lemma F_5f830 : fetch_word AsanUbsan.M.loaded_segments (0x5f830 : word) = Some W_5f830.
Proof. vm_refl. Qed.
Lemma D_5f830 : decode_any W_5f830 = Some (OpImm ALU_ADD 14 14 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f834 : bv 32 := 0x7ff70b93.
Lemma F_5f834 : fetch_word AsanUbsan.M.loaded_segments (0x5f834 : word) = Some W_5f834.
Proof. vm_refl. Qed.
Lemma D_5f834 : decode_any W_5f834 = Some (OpImm ALU_ADD 23 14 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f838 : bv 32 := 0x000bb4a3.
Lemma F_5f838 : fetch_word AsanUbsan.M.loaded_segments (0x5f838 : word) = Some W_5f838.
Proof. vm_refl. Qed.
Lemma D_5f838 : decode_any W_5f838 = Some (Store SZ8 23 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f83c : bv 32 := 0x00dab023.
Lemma F_5f83c : fetch_word AsanUbsan.M.loaded_segments (0x5f83c : word) = Some W_5f83c.
Proof. vm_refl. Qed.
Lemma D_5f83c : decode_any W_5f83c = Some (Store SZ8 21 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f840 : bv 32 := 0x000ab423.
Lemma F_5f840 : fetch_word AsanUbsan.M.loaded_segments (0x5f840 : word) = Some W_5f840.
Proof. vm_refl. Qed.
Lemma D_5f840 : decode_any W_5f840 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f844 : bv 32 := 0x00060493.
Lemma F_5f844 : fetch_word AsanUbsan.M.loaded_segments (0x5f844 : word) = Some W_5f844.
Proof. vm_refl. Qed.
Lemma D_5f844 : decode_any W_5f844 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f848 : bv 32 := 0x00058913.
Lemma F_5f848 : fetch_word AsanUbsan.M.loaded_segments (0x5f848 : word) = Some W_5f848.
Proof. vm_refl. Qed.
Lemma D_5f848 : decode_any W_5f848 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f84c : bv 32 := 0x00050b13.
Lemma F_5f84c : fetch_word AsanUbsan.M.loaded_segments (0x5f84c : word) = Some W_5f84c.
Proof. vm_refl. Qed.
Lemma D_5f84c : decode_any W_5f84c = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f850 : bv 32 := 0x25c210ef.
Lemma F_5f850 : fetch_word AsanUbsan.M.loaded_segments (0x5f850 : word) = Some W_5f850.
Proof. vm_refl. Qed.
Lemma D_5f850 : decode_any W_5f850 = Some (Jal 1 135772, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f854 : bv 32 := 0x00050593.
Lemma F_5f854 : fetch_word AsanUbsan.M.loaded_segments (0x5f854 : word) = Some W_5f854.
Proof. vm_refl. Qed.
Lemma D_5f854 : decode_any W_5f854 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f858 : bv 32 := 0x00077517.
Lemma F_5f858 : fetch_word AsanUbsan.M.loaded_segments (0x5f858 : word) = Some W_5f858.
Proof. vm_refl. Qed.
Lemma D_5f858 : decode_any W_5f858 = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f85c : bv 32 := 0xc6053503.
Lemma F_5f85c : fetch_word AsanUbsan.M.loaded_segments (0x5f85c : word) = Some W_5f85c.
Proof. vm_refl. Qed.
Lemma D_5f85c : decode_any W_5f85c = Some (Load SZ8 true 10 10 3168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f860 : bv 32 := 0x02154703.
Lemma F_5f860 : fetch_word AsanUbsan.M.loaded_segments (0x5f860 : word) = Some W_5f860.
Proof. vm_refl. Qed.
Lemma D_5f860 : decode_any W_5f860 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f864 : bv 32 := 0x008bb4a3.
Lemma F_5f864 : fetch_word AsanUbsan.M.loaded_segments (0x5f864 : word) = Some W_5f864.
Proof. vm_refl. Qed.
Lemma D_5f864 : decode_any W_5f864 = Some (Store SZ8 23 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f868 : bv 32 := 0x80040513.
Lemma F_5f868 : fetch_word AsanUbsan.M.loaded_segments (0x5f868 : word) = Some W_5f868.
Proof. vm_refl. Qed.
Lemma D_5f868 : decode_any W_5f868 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f86c : bv 32 := 0xf9850513.
Lemma F_5f86c : fetch_word AsanUbsan.M.loaded_segments (0x5f86c : word) = Some W_5f86c.
Proof. vm_refl. Qed.
Lemma D_5f86c : decode_any W_5f86c = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f870 : bv 32 := 0x0ff00793.
Lemma F_5f870 : fetch_word AsanUbsan.M.loaded_segments (0x5f870 : word) = Some W_5f870.
Proof. vm_refl. Qed.
Lemma D_5f870 : decode_any W_5f870 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f874 : bv 32 := 0x00040613.
Lemma F_5f874 : fetch_word AsanUbsan.M.loaded_segments (0x5f874 : word) = Some W_5f874.
Proof. vm_refl. Qed.
Lemma D_5f874 : decode_any W_5f874 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f878 : bv 32 := 0x00000693.
Lemma F_5f878 : fetch_word AsanUbsan.M.loaded_segments (0x5f878 : word) = Some W_5f878.
Proof. vm_refl. Qed.
Lemma D_5f878 : decode_any W_5f878 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f87c : bv 32 := 0x780080ef.
Lemma F_5f87c : fetch_word AsanUbsan.M.loaded_segments (0x5f87c : word) = Some W_5f87c.
Proof. vm_refl. Qed.
Lemma D_5f87c : decode_any W_5f87c = Some (Jal 1 34688, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f880 : bv 32 := 0x80040613.
Lemma F_5f880 : fetch_word AsanUbsan.M.loaded_segments (0x5f880 : word) = Some W_5f880.
Proof. vm_refl. Qed.
Lemma D_5f880 : decode_any W_5f880 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f884 : bv 32 := 0xf9860613.
Lemma F_5f884 : fetch_word AsanUbsan.M.loaded_segments (0x5f884 : word) = Some W_5f884.
Proof. vm_refl. Qed.
Lemma D_5f884 : decode_any W_5f884 = Some (OpImm ALU_ADD 12 12 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f888 : bv 32 := 0x00090513.
Lemma F_5f888 : fetch_word AsanUbsan.M.loaded_segments (0x5f888 : word) = Some W_5f888.
Proof. vm_refl. Qed.
Lemma D_5f888 : decode_any W_5f888 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f88c : bv 32 := 0x00048593.
Lemma F_5f88c : fetch_word AsanUbsan.M.loaded_segments (0x5f88c : word) = Some W_5f88c.
Proof. vm_refl. Qed.
Lemma D_5f88c : decode_any W_5f88c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f890 : bv 32 := 0x524050ef.
Lemma F_5f890 : fetch_word AsanUbsan.M.loaded_segments (0x5f890 : word) = Some W_5f890.
Proof. vm_refl. Qed.
Lemma D_5f890 : decode_any W_5f890 = Some (Jal 1 21796, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f894 : bv 32 := 0x000b0513.
Lemma F_5f894 : fetch_word AsanUbsan.M.loaded_segments (0x5f894 : word) = Some W_5f894.
Proof. vm_refl. Qed.
Lemma D_5f894 : decode_any W_5f894 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f898 : bv 32 := 0x00090593.
Lemma F_5f898 : fetch_word AsanUbsan.M.loaded_segments (0x5f898 : word) = Some W_5f898.
Proof. vm_refl. Qed.
Lemma D_5f898 : decode_any W_5f898 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f89c : bv 32 := 0x00048613.
Lemma F_5f89c : fetch_word AsanUbsan.M.loaded_segments (0x5f89c : word) = Some W_5f89c.
Proof. vm_refl. Qed.
Lemma D_5f89c : decode_any W_5f89c = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8a0 : bv 32 := 0xfbf48b13.
Lemma F_5f8a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f8a0 : word) = Some W_5f8a0.
Proof. vm_refl. Qed.
Lemma D_5f8a0 : decode_any W_5f8a0 = Some (OpImm ALU_ADD 22 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8a4 : bv 32 := 0xfbf00693.
Lemma F_5f8a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f8a4 : word) = Some W_5f8a4.
Proof. vm_refl. Qed.
Lemma D_5f8a4 : decode_any W_5f8a4 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8a8 : bv 32 := 0xd166eee3.
Lemma F_5f8a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f8a8 : word) = Some W_5f8a8.
Proof. vm_refl. Qed.
Lemma D_5f8a8 : decode_any W_5f8a8 = Some (Branch BC_LTU 13 22 7452, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8ac : bv 32 := 0x02061e63.
Lemma F_5f8ac : fetch_word AsanUbsan.M.loaded_segments (0x5f8ac : word) = Some W_5f8ac.
Proof. vm_refl. Qed.
Lemma D_5f8ac : decode_any W_5f8ac = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8b0 : bv 32 := 0xd4dff06f.
Lemma F_5f8b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f8b0 : word) = Some W_5f8b0.
Proof. vm_refl. Qed.
Lemma D_5f8b0 : decode_any W_5f8b0 = Some (Jal 0 2096460, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8b4 : bv 32 := 0x00070783.
Lemma F_5f8b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f8b4 : word) = Some W_5f8b4.
Proof. vm_refl. Qed.
Lemma D_5f8b4 : decode_any W_5f8b4 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8b8 : bv 32 := 0x0079f813.
Lemma F_5f8b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f8b8 : word) = Some W_5f8b8.
Proof. vm_refl. Qed.
Lemma D_5f8b8 : decode_any W_5f8b8 = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8bc : bv 32 := 0x00f038b3.
Lemma F_5f8bc : fetch_word AsanUbsan.M.loaded_segments (0x5f8bc : word) = Some W_5f8bc.
Proof. vm_refl. Qed.
Lemma D_5f8bc : decode_any W_5f8bc = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8c0 : bv 32 := 0x00f827b3.
Lemma F_5f8c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f8c0 : word) = Some W_5f8c0.
Proof. vm_refl. Qed.
Lemma D_5f8c0 : decode_any W_5f8c0 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8c4 : bv 32 := 0x0017c793.
Lemma F_5f8c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f8c4 : word) = Some W_5f8c4.
Proof. vm_refl. Qed.
Lemma D_5f8c4 : decode_any W_5f8c4 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8c8 : bv 32 := 0x00f8f7b3.
Lemma F_5f8c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f8c8 : word) = Some W_5f8c8.
Proof. vm_refl. Qed.
Lemma D_5f8c8 : decode_any W_5f8c8 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8cc : bv 32 := 0x00e6fa63.
Lemma F_5f8cc : fetch_word AsanUbsan.M.loaded_segments (0x5f8cc : word) = Some W_5f8cc.
Proof. vm_refl. Qed.
Lemma D_5f8cc : decode_any W_5f8cc = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8d0 : bv 32 := 0x0006c803.
Lemma F_5f8d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f8d0 : word) = Some W_5f8d0.
Proof. vm_refl. Qed.
Lemma D_5f8d0 : decode_any W_5f8d0 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8d4 : bv 32 := 0x00168693.
Lemma F_5f8d4 : fetch_word AsanUbsan.M.loaded_segments (0x5f8d4 : word) = Some W_5f8d4.
Proof. vm_refl. Qed.
Lemma D_5f8d4 : decode_any W_5f8d4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8d8 : bv 32 := 0x00f867b3.
Lemma F_5f8d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f8d8 : word) = Some W_5f8d8.
Proof. vm_refl. Qed.
Lemma D_5f8d8 : decode_any W_5f8d8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8dc : bv 32 := 0xfee69ae3.
Lemma F_5f8dc : fetch_word AsanUbsan.M.loaded_segments (0x5f8dc : word) = Some W_5f8dc.
Proof. vm_refl. Qed.
Lemma D_5f8dc : decode_any W_5f8dc = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8e0 : bv 32 := 0x0ff7f693.
Lemma F_5f8e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f8e0 : word) = Some W_5f8e0.
Proof. vm_refl. Qed.
Lemma D_5f8e0 : decode_any W_5f8e0 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8e4 : bv 32 := 0xd0068ce3.
Lemma F_5f8e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f8e4 : word) = Some W_5f8e4.
Proof. vm_refl. Qed.
Lemma D_5f8e4 : decode_any W_5f8e4 = Some (Branch BC_EQ 13 0 7448, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8e8 : bv 32 := 0x00050b93.
Lemma F_5f8e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f8e8 : word) = Some W_5f8e8.
Proof. vm_refl. Qed.
Lemma D_5f8e8 : decode_any W_5f8e8 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8ec : bv 32 := 0x00058513.
Lemma F_5f8ec : fetch_word AsanUbsan.M.loaded_segments (0x5f8ec : word) = Some W_5f8ec.
Proof. vm_refl. Qed.
Lemma D_5f8ec : decode_any W_5f8ec = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8f0 : bv 32 := 0x00058c13.
Lemma F_5f8f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f8f0 : word) = Some W_5f8f0.
Proof. vm_refl. Qed.
Lemma D_5f8f0 : decode_any W_5f8f0 = Some (OpImm ALU_ADD 24 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8f4 : bv 32 := 0x00060593.
Lemma F_5f8f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f8f4 : word) = Some W_5f8f4.
Proof. vm_refl. Qed.
Lemma D_5f8f4 : decode_any W_5f8f4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8f8 : bv 32 := 0x00060493.
Lemma F_5f8f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f8f8 : word) = Some W_5f8f8.
Proof. vm_refl. Qed.
Lemma D_5f8f8 : decode_any W_5f8f8 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f8fc : bv 32 := 0x284020ef.
Lemma F_5f8fc : fetch_word AsanUbsan.M.loaded_segments (0x5f8fc : word) = Some W_5f8fc.
Proof. vm_refl. Qed.
Lemma D_5f8fc : decode_any W_5f8fc = Some (Jal 1 8836, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f900 : bv 32 := 0x000c0593.
Lemma F_5f900 : fetch_word AsanUbsan.M.loaded_segments (0x5f900 : word) = Some W_5f900.
Proof. vm_refl. Qed.
Lemma D_5f900 : decode_any W_5f900 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f904 : bv 32 := 0x00048613.
Lemma F_5f904 : fetch_word AsanUbsan.M.loaded_segments (0x5f904 : word) = Some W_5f904.
Proof. vm_refl. Qed.
Lemma D_5f904 : decode_any W_5f904 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f908 : bv 32 := 0x00050913.
Lemma F_5f908 : fetch_word AsanUbsan.M.loaded_segments (0x5f908 : word) = Some W_5f908.
Proof. vm_refl. Qed.
Lemma D_5f908 : decode_any W_5f908 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f90c : bv 32 := 0x000b8513.
Lemma F_5f90c : fetch_word AsanUbsan.M.loaded_segments (0x5f90c : word) = Some W_5f90c.
Proof. vm_refl. Qed.
Lemma D_5f90c : decode_any W_5f90c = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f910 : bv 32 := 0xce0906e3.
Lemma F_5f910 : fetch_word AsanUbsan.M.loaded_segments (0x5f910 : word) = Some W_5f910.
Proof. vm_refl. Qed.
Lemma D_5f910 : decode_any W_5f910 = Some (Branch BC_EQ 18 0 7404, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f914 : bv 32 := 0xfffb5517.
Lemma F_5f914 : fetch_word AsanUbsan.M.loaded_segments (0x5f914 : word) = Some W_5f914.
Proof. vm_refl. Qed.
Lemma D_5f914 : decode_any W_5f914 = Some (Auipc 10 1048501, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f918 : bv 32 := 0x77050513.
Lemma F_5f918 : fetch_word AsanUbsan.M.loaded_segments (0x5f918 : word) = Some W_5f918.
Proof. vm_refl. Qed.
Lemma D_5f918 : decode_any W_5f918 = Some (OpImm ALU_ADD 10 10 1904, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f91c : bv 32 := 0x68c090ef.
Lemma F_5f91c : fetch_word AsanUbsan.M.loaded_segments (0x5f91c : word) = Some W_5f91c.
Proof. vm_refl. Qed.
Lemma D_5f91c : decode_any W_5f91c = Some (Jal 1 38540, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f920 : bv 32 := 0x000c0593.
Lemma F_5f920 : fetch_word AsanUbsan.M.loaded_segments (0x5f920 : word) = Some W_5f920.
Proof. vm_refl. Qed.
Lemma D_5f920 : decode_any W_5f920 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f924 : bv 32 := 0x00048613.
Lemma F_5f924 : fetch_word AsanUbsan.M.loaded_segments (0x5f924 : word) = Some W_5f924.
Proof. vm_refl. Qed.
Lemma D_5f924 : decode_any W_5f924 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f928 : bv 32 := 0x00050693.
Lemma F_5f928 : fetch_word AsanUbsan.M.loaded_segments (0x5f928 : word) = Some W_5f928.
Proof. vm_refl. Qed.
Lemma D_5f928 : decode_any W_5f928 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f92c : bv 32 := 0x000b8513.
Lemma F_5f92c : fetch_word AsanUbsan.M.loaded_segments (0x5f92c : word) = Some W_5f92c.
Proof. vm_refl. Qed.
Lemma D_5f92c : decode_any W_5f92c = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f930 : bv 32 := 0xcc0696e3.
Lemma F_5f930 : fetch_word AsanUbsan.M.loaded_segments (0x5f930 : word) = Some W_5f930.
Proof. vm_refl. Qed.
Lemma D_5f930 : decode_any W_5f930 = Some (Branch BC_NE 13 0 7372, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f934 : bv 32 := 0x6dc090ef.
Lemma F_5f934 : fetch_word AsanUbsan.M.loaded_segments (0x5f934 : word) = Some W_5f934.
Proof. vm_refl. Qed.
Lemma D_5f934 : decode_any W_5f934 = Some (Jal 1 38620, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f938 : bv 32 := 0x16050c63.
Lemma F_5f938 : fetch_word AsanUbsan.M.loaded_segments (0x5f938 : word) = Some W_5f938.
Proof. vm_refl. Qed.
Lemma D_5f938 : decode_any W_5f938 = Some (Branch BC_EQ 10 0 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f93c : bv 32 := 0x80040513.
Lemma F_5f93c : fetch_word AsanUbsan.M.loaded_segments (0x5f93c : word) = Some W_5f93c.
Proof. vm_refl. Qed.
Lemma D_5f93c : decode_any W_5f93c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f940 : bv 32 := 0xfa850513.
Lemma F_5f940 : fetch_word AsanUbsan.M.loaded_segments (0x5f940 : word) = Some W_5f940.
Proof. vm_refl. Qed.
Lemma D_5f940 : decode_any W_5f940 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f944 : bv 32 := 0x80040593.
Lemma F_5f944 : fetch_word AsanUbsan.M.loaded_segments (0x5f944 : word) = Some W_5f944.
Proof. vm_refl. Qed.
Lemma D_5f944 : decode_any W_5f944 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f948 : bv 32 := 0xf9858593.
Lemma F_5f948 : fetch_word AsanUbsan.M.loaded_segments (0x5f948 : word) = Some W_5f948.
Proof. vm_refl. Qed.
Lemma D_5f948 : decode_any W_5f948 = Some (OpImm ALU_ADD 11 11 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f94c : bv 32 := 0x7ff58993.
Lemma F_5f94c : fetch_word AsanUbsan.M.loaded_segments (0x5f94c : word) = Some W_5f94c.
Proof. vm_refl. Qed.
Lemma D_5f94c : decode_any W_5f94c = Some (OpImm ALU_ADD 19 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f950 : bv 32 := 0x0009b4a3.
Lemma F_5f950 : fetch_word AsanUbsan.M.loaded_segments (0x5f950 : word) = Some W_5f950.
Proof. vm_refl. Qed.
Lemma D_5f950 : decode_any W_5f950 = Some (Store SZ8 19 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f954 : bv 32 := 0x00aab023.
Lemma F_5f954 : fetch_word AsanUbsan.M.loaded_segments (0x5f954 : word) = Some W_5f954.
Proof. vm_refl. Qed.
Lemma D_5f954 : decode_any W_5f954 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f958 : bv 32 := 0x000ab423.
Lemma F_5f958 : fetch_word AsanUbsan.M.loaded_segments (0x5f958 : word) = Some W_5f958.
Proof. vm_refl. Qed.
Lemma D_5f958 : decode_any W_5f958 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f95c : bv 32 := 0x150210ef.
Lemma F_5f95c : fetch_word AsanUbsan.M.loaded_segments (0x5f95c : word) = Some W_5f95c.
Proof. vm_refl. Qed.
Lemma D_5f95c : decode_any W_5f95c = Some (Jal 1 135504, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f960 : bv 32 := 0x00050593.
Lemma F_5f960 : fetch_word AsanUbsan.M.loaded_segments (0x5f960 : word) = Some W_5f960.
Proof. vm_refl. Qed.
Lemma D_5f960 : decode_any W_5f960 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f964 : bv 32 := 0x00077517.
Lemma F_5f964 : fetch_word AsanUbsan.M.loaded_segments (0x5f964 : word) = Some W_5f964.
Proof. vm_refl. Qed.
Lemma D_5f964 : decode_any W_5f964 = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f968 : bv 32 := 0xb5453503.
Lemma F_5f968 : fetch_word AsanUbsan.M.loaded_segments (0x5f968 : word) = Some W_5f968.
Proof. vm_refl. Qed.
Lemma D_5f968 : decode_any W_5f968 = Some (Load SZ8 true 10 10 2900, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f96c : bv 32 := 0x02154703.
Lemma F_5f96c : fetch_word AsanUbsan.M.loaded_segments (0x5f96c : word) = Some W_5f96c.
Proof. vm_refl. Qed.
Lemma D_5f96c : decode_any W_5f96c = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f970 : bv 32 := 0x0089b4a3.
Lemma F_5f970 : fetch_word AsanUbsan.M.loaded_segments (0x5f970 : word) = Some W_5f970.
Proof. vm_refl. Qed.
Lemma D_5f970 : decode_any W_5f970 = Some (Store SZ8 19 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f974 : bv 32 := 0x80040513.
Lemma F_5f974 : fetch_word AsanUbsan.M.loaded_segments (0x5f974 : word) = Some W_5f974.
Proof. vm_refl. Qed.
Lemma D_5f974 : decode_any W_5f974 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f978 : bv 32 := 0xf9850513.
Lemma F_5f978 : fetch_word AsanUbsan.M.loaded_segments (0x5f978 : word) = Some W_5f978.
Proof. vm_refl. Qed.
Lemma D_5f978 : decode_any W_5f978 = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f97c : bv 32 := 0x0ff00793.
Lemma F_5f97c : fetch_word AsanUbsan.M.loaded_segments (0x5f97c : word) = Some W_5f97c.
Proof. vm_refl. Qed.
Lemma D_5f97c : decode_any W_5f97c = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f980 : bv 32 := 0x00040613.
Lemma F_5f980 : fetch_word AsanUbsan.M.loaded_segments (0x5f980 : word) = Some W_5f980.
Proof. vm_refl. Qed.
Lemma D_5f980 : decode_any W_5f980 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f984 : bv 32 := 0x00000693.
Lemma F_5f984 : fetch_word AsanUbsan.M.loaded_segments (0x5f984 : word) = Some W_5f984.
Proof. vm_refl. Qed.
Lemma D_5f984 : decode_any W_5f984 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f988 : bv 32 := 0x674080ef.
Lemma F_5f988 : fetch_word AsanUbsan.M.loaded_segments (0x5f988 : word) = Some W_5f988.
Proof. vm_refl. Qed.
Lemma D_5f988 : decode_any W_5f988 = Some (Jal 1 34420, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f98c : bv 32 := 0x80040513.
Lemma F_5f98c : fetch_word AsanUbsan.M.loaded_segments (0x5f98c : word) = Some W_5f98c.
Proof. vm_refl. Qed.
Lemma D_5f98c : decode_any W_5f98c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f990 : bv 32 := 0xf9850513.
Lemma F_5f990 : fetch_word AsanUbsan.M.loaded_segments (0x5f990 : word) = Some W_5f990.
Proof. vm_refl. Qed.
Lemma D_5f990 : decode_any W_5f990 = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f994 : bv 32 := 0x185090ef.
Lemma F_5f994 : fetch_word AsanUbsan.M.loaded_segments (0x5f994 : word) = Some W_5f994.
Proof. vm_refl. Qed.
Lemma D_5f994 : decode_any W_5f994 = Some (Jal 1 39300, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f998 : bv 32 := 0x00050693.
Lemma F_5f998 : fetch_word AsanUbsan.M.loaded_segments (0x5f998 : word) = Some W_5f998.
Proof. vm_refl. Qed.
Lemma D_5f998 : decode_any W_5f998 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f99c : bv 32 := 0x00040993.
Lemma F_5f99c : fetch_word AsanUbsan.M.loaded_segments (0x5f99c : word) = Some W_5f99c.
Proof. vm_refl. Qed.
Lemma D_5f99c : decode_any W_5f99c = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9a0 : bv 32 := 0x00048613.
Lemma F_5f9a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f9a0 : word) = Some W_5f9a0.
Proof. vm_refl. Qed.
Lemma D_5f9a0 : decode_any W_5f9a0 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9a4 : bv 32 := 0x000c0593.
Lemma F_5f9a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f9a4 : word) = Some W_5f9a4.
Proof. vm_refl. Qed.
Lemma D_5f9a4 : decode_any W_5f9a4 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9a8 : bv 32 := 0x000b8513.
Lemma F_5f9a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f9a8 : word) = Some W_5f9a8.
Proof. vm_refl. Qed.
Lemma D_5f9a8 : decode_any W_5f9a8 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9ac : bv 32 := 0xc40698e3.
Lemma F_5f9ac : fetch_word AsanUbsan.M.loaded_segments (0x5f9ac : word) = Some W_5f9ac.
Proof. vm_refl. Qed.
Lemma D_5f9ac : decode_any W_5f9ac = Some (Branch BC_NE 13 0 7248, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9b0 : bv 32 := 0x1040006f.
Lemma F_5f9b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f9b0 : word) = Some W_5f9b0.
Proof. vm_refl. Qed.
Lemma D_5f9b0 : decode_any W_5f9b0 = Some (Jal 0 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9b4 : bv 32 := 0x00070783.
Lemma F_5f9b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f9b4 : word) = Some W_5f9b4.
Proof. vm_refl. Qed.
Lemma D_5f9b4 : decode_any W_5f9b4 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9b8 : bv 32 := 0x007a7813.
Lemma F_5f9b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f9b8 : word) = Some W_5f9b8.
Proof. vm_refl. Qed.
Lemma D_5f9b8 : decode_any W_5f9b8 = Some (OpImm ALU_AND 16 20 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9bc : bv 32 := 0x00f038b3.
Lemma F_5f9bc : fetch_word AsanUbsan.M.loaded_segments (0x5f9bc : word) = Some W_5f9bc.
Proof. vm_refl. Qed.
Lemma D_5f9bc : decode_any W_5f9bc = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9c0 : bv 32 := 0x00f827b3.
Lemma F_5f9c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f9c0 : word) = Some W_5f9c0.
Proof. vm_refl. Qed.
Lemma D_5f9c0 : decode_any W_5f9c0 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9c4 : bv 32 := 0x0017c793.
Lemma F_5f9c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f9c4 : word) = Some W_5f9c4.
Proof. vm_refl. Qed.
Lemma D_5f9c4 : decode_any W_5f9c4 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9c8 : bv 32 := 0x00f8f7b3.
Lemma F_5f9c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f9c8 : word) = Some W_5f9c8.
Proof. vm_refl. Qed.
Lemma D_5f9c8 : decode_any W_5f9c8 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9cc : bv 32 := 0x00e6fa63.
Lemma F_5f9cc : fetch_word AsanUbsan.M.loaded_segments (0x5f9cc : word) = Some W_5f9cc.
Proof. vm_refl. Qed.
Lemma D_5f9cc : decode_any W_5f9cc = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9d0 : bv 32 := 0x0006c803.
Lemma F_5f9d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f9d0 : word) = Some W_5f9d0.
Proof. vm_refl. Qed.
Lemma D_5f9d0 : decode_any W_5f9d0 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9d4 : bv 32 := 0x00168693.
Lemma F_5f9d4 : fetch_word AsanUbsan.M.loaded_segments (0x5f9d4 : word) = Some W_5f9d4.
Proof. vm_refl. Qed.
Lemma D_5f9d4 : decode_any W_5f9d4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9d8 : bv 32 := 0x00f867b3.
Lemma F_5f9d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f9d8 : word) = Some W_5f9d8.
Proof. vm_refl. Qed.
Lemma D_5f9d8 : decode_any W_5f9d8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9dc : bv 32 := 0xfee69ae3.
Lemma F_5f9dc : fetch_word AsanUbsan.M.loaded_segments (0x5f9dc : word) = Some W_5f9dc.
Proof. vm_refl. Qed.
Lemma D_5f9dc : decode_any W_5f9dc = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9e0 : bv 32 := 0x0ff7f693.
Lemma F_5f9e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f9e0 : word) = Some W_5f9e0.
Proof. vm_refl. Qed.
Lemma D_5f9e0 : decode_any W_5f9e0 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9e4 : bv 32 := 0xc60680e3.
Lemma F_5f9e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f9e4 : word) = Some W_5f9e4.
Proof. vm_refl. Qed.
Lemma D_5f9e4 : decode_any W_5f9e4 = Some (Branch BC_EQ 13 0 7264, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9e8 : bv 32 := 0x00050493.
Lemma F_5f9e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f9e8 : word) = Some W_5f9e8.
Proof. vm_refl. Qed.
Lemma D_5f9e8 : decode_any W_5f9e8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9ec : bv 32 := 0x00058b13.
Lemma F_5f9ec : fetch_word AsanUbsan.M.loaded_segments (0x5f9ec : word) = Some W_5f9ec.
Proof. vm_refl. Qed.
Lemma D_5f9ec : decode_any W_5f9ec = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9f0 : bv 32 := 0x00060593.
Lemma F_5f9f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f9f0 : word) = Some W_5f9f0.
Proof. vm_refl. Qed.
Lemma D_5f9f0 : decode_any W_5f9f0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9f4 : bv 32 := 0x00060913.
Lemma F_5f9f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f9f4 : word) = Some W_5f9f4.
Proof. vm_refl. Qed.
Lemma D_5f9f4 : decode_any W_5f9f4 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9f8 : bv 32 := 0x188020ef.
Lemma F_5f9f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f9f8 : word) = Some W_5f9f8.
Proof. vm_refl. Qed.
Lemma D_5f9f8 : decode_any W_5f9f8 = Some (Jal 1 8584, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9fc : bv 32 := 0x000b0593.
Lemma F_5f9fc : fetch_word AsanUbsan.M.loaded_segments (0x5f9fc : word) = Some W_5f9fc.
Proof. vm_refl. Qed.
Lemma D_5f9fc : decode_any W_5f9fc = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa00 : bv 32 := 0x00090613.
Lemma F_5fa00 : fetch_word AsanUbsan.M.loaded_segments (0x5fa00 : word) = Some W_5fa00.
Proof. vm_refl. Qed.
Lemma D_5fa00 : decode_any W_5fa00 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa04 : bv 32 := 0x00050993.
Lemma F_5fa04 : fetch_word AsanUbsan.M.loaded_segments (0x5fa04 : word) = Some W_5fa04.
Proof. vm_refl. Qed.
Lemma D_5fa04 : decode_any W_5fa04 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa08 : bv 32 := 0x00048513.
Lemma F_5fa08 : fetch_word AsanUbsan.M.loaded_segments (0x5fa08 : word) = Some W_5fa08.
Proof. vm_refl. Qed.
Lemma D_5fa08 : decode_any W_5fa08 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa0c : bv 32 := 0xc2098ce3.
Lemma F_5fa0c : fetch_word AsanUbsan.M.loaded_segments (0x5fa0c : word) = Some W_5fa0c.
Proof. vm_refl. Qed.
Lemma D_5fa0c : decode_any W_5fa0c = Some (Branch BC_EQ 19 0 7224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa10 : bv 32 := 0xfffb5517.
Lemma F_5fa10 : fetch_word AsanUbsan.M.loaded_segments (0x5fa10 : word) = Some W_5fa10.
Proof. vm_refl. Qed.
Lemma D_5fa10 : decode_any W_5fa10 = Some (Auipc 10 1048501, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa14 : bv 32 := 0x67450513.
Lemma F_5fa14 : fetch_word AsanUbsan.M.loaded_segments (0x5fa14 : word) = Some W_5fa14.
Proof. vm_refl. Qed.
Lemma D_5fa14 : decode_any W_5fa14 = Some (OpImm ALU_ADD 10 10 1652, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa18 : bv 32 := 0x590090ef.
Lemma F_5fa18 : fetch_word AsanUbsan.M.loaded_segments (0x5fa18 : word) = Some W_5fa18.
Proof. vm_refl. Qed.
Lemma D_5fa18 : decode_any W_5fa18 = Some (Jal 1 38288, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa1c : bv 32 := 0x000b0593.
Lemma F_5fa1c : fetch_word AsanUbsan.M.loaded_segments (0x5fa1c : word) = Some W_5fa1c.
Proof. vm_refl. Qed.
Lemma D_5fa1c : decode_any W_5fa1c = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa20 : bv 32 := 0x00090613.
Lemma F_5fa20 : fetch_word AsanUbsan.M.loaded_segments (0x5fa20 : word) = Some W_5fa20.
Proof. vm_refl. Qed.
Lemma D_5fa20 : decode_any W_5fa20 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa24 : bv 32 := 0x00050693.
Lemma F_5fa24 : fetch_word AsanUbsan.M.loaded_segments (0x5fa24 : word) = Some W_5fa24.
Proof. vm_refl. Qed.
Lemma D_5fa24 : decode_any W_5fa24 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa28 : bv 32 := 0x00048513.
Lemma F_5fa28 : fetch_word AsanUbsan.M.loaded_segments (0x5fa28 : word) = Some W_5fa28.
Proof. vm_refl. Qed.
Lemma D_5fa28 : decode_any W_5fa28 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa2c : bv 32 := 0xc0069ce3.
Lemma F_5fa2c : fetch_word AsanUbsan.M.loaded_segments (0x5fa2c : word) = Some W_5fa2c.
Proof. vm_refl. Qed.
Lemma D_5fa2c : decode_any W_5fa2c = Some (Branch BC_NE 13 0 7192, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa30 : bv 32 := 0x5e0090ef.
Lemma F_5fa30 : fetch_word AsanUbsan.M.loaded_segments (0x5fa30 : word) = Some W_5fa30.
Proof. vm_refl. Qed.
Lemma D_5fa30 : decode_any W_5fa30 = Some (Jal 1 38368, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa34 : bv 32 := 0x0c050263.
Lemma F_5fa34 : fetch_word AsanUbsan.M.loaded_segments (0x5fa34 : word) = Some W_5fa34.
Proof. vm_refl. Qed.
Lemma D_5fa34 : decode_any W_5fa34 = Some (Branch BC_EQ 10 0 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa38 : bv 32 := 0x80040513.
Lemma F_5fa38 : fetch_word AsanUbsan.M.loaded_segments (0x5fa38 : word) = Some W_5fa38.
Proof. vm_refl. Qed.
Lemma D_5fa38 : decode_any W_5fa38 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa3c : bv 32 := 0xfa850513.
Lemma F_5fa3c : fetch_word AsanUbsan.M.loaded_segments (0x5fa3c : word) = Some W_5fa3c.
Proof. vm_refl. Qed.
Lemma D_5fa3c : decode_any W_5fa3c = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa40 : bv 32 := 0x80040593.
Lemma F_5fa40 : fetch_word AsanUbsan.M.loaded_segments (0x5fa40 : word) = Some W_5fa40.
Proof. vm_refl. Qed.
Lemma D_5fa40 : decode_any W_5fa40 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa44 : bv 32 := 0xf9858593.
Lemma F_5fa44 : fetch_word AsanUbsan.M.loaded_segments (0x5fa44 : word) = Some W_5fa44.
Proof. vm_refl. Qed.
Lemma D_5fa44 : decode_any W_5fa44 = Some (OpImm ALU_ADD 11 11 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa48 : bv 32 := 0x7ff58a13.
Lemma F_5fa48 : fetch_word AsanUbsan.M.loaded_segments (0x5fa48 : word) = Some W_5fa48.
Proof. vm_refl. Qed.
Lemma D_5fa48 : decode_any W_5fa48 = Some (OpImm ALU_ADD 20 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa4c : bv 32 := 0x000a34a3.
Lemma F_5fa4c : fetch_word AsanUbsan.M.loaded_segments (0x5fa4c : word) = Some W_5fa4c.
Proof. vm_refl. Qed.
Lemma D_5fa4c : decode_any W_5fa4c = Some (Store SZ8 20 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa50 : bv 32 := 0x00aab023.
Lemma F_5fa50 : fetch_word AsanUbsan.M.loaded_segments (0x5fa50 : word) = Some W_5fa50.
Proof. vm_refl. Qed.
Lemma D_5fa50 : decode_any W_5fa50 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa54 : bv 32 := 0x000ab423.
Lemma F_5fa54 : fetch_word AsanUbsan.M.loaded_segments (0x5fa54 : word) = Some W_5fa54.
Proof. vm_refl. Qed.
Lemma D_5fa54 : decode_any W_5fa54 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa58 : bv 32 := 0x054210ef.
Lemma F_5fa58 : fetch_word AsanUbsan.M.loaded_segments (0x5fa58 : word) = Some W_5fa58.
Proof. vm_refl. Qed.
Lemma D_5fa58 : decode_any W_5fa58 = Some (Jal 1 135252, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa5c : bv 32 := 0x00050593.
Lemma F_5fa5c : fetch_word AsanUbsan.M.loaded_segments (0x5fa5c : word) = Some W_5fa5c.
Proof. vm_refl. Qed.
Lemma D_5fa5c : decode_any W_5fa5c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa60 : bv 32 := 0x00077517.
Lemma F_5fa60 : fetch_word AsanUbsan.M.loaded_segments (0x5fa60 : word) = Some W_5fa60.
Proof. vm_refl. Qed.
Lemma D_5fa60 : decode_any W_5fa60 = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa64 : bv 32 := 0xa5853503.
Lemma F_5fa64 : fetch_word AsanUbsan.M.loaded_segments (0x5fa64 : word) = Some W_5fa64.
Proof. vm_refl. Qed.
Lemma D_5fa64 : decode_any W_5fa64 = Some (Load SZ8 true 10 10 2648, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa68 : bv 32 := 0x02154703.
Lemma F_5fa68 : fetch_word AsanUbsan.M.loaded_segments (0x5fa68 : word) = Some W_5fa68.
Proof. vm_refl. Qed.
Lemma D_5fa68 : decode_any W_5fa68 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa6c : bv 32 := 0x008a34a3.
Lemma F_5fa6c : fetch_word AsanUbsan.M.loaded_segments (0x5fa6c : word) = Some W_5fa6c.
Proof. vm_refl. Qed.
Lemma D_5fa6c : decode_any W_5fa6c = Some (Store SZ8 20 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa70 : bv 32 := 0x80040513.
Lemma F_5fa70 : fetch_word AsanUbsan.M.loaded_segments (0x5fa70 : word) = Some W_5fa70.
Proof. vm_refl. Qed.
Lemma D_5fa70 : decode_any W_5fa70 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa74 : bv 32 := 0xf9850513.
Lemma F_5fa74 : fetch_word AsanUbsan.M.loaded_segments (0x5fa74 : word) = Some W_5fa74.
Proof. vm_refl. Qed.
Lemma D_5fa74 : decode_any W_5fa74 = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa78 : bv 32 := 0x0ff00793.
Lemma F_5fa78 : fetch_word AsanUbsan.M.loaded_segments (0x5fa78 : word) = Some W_5fa78.
Proof. vm_refl. Qed.
Lemma D_5fa78 : decode_any W_5fa78 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa7c : bv 32 := 0x00040613.
Lemma F_5fa7c : fetch_word AsanUbsan.M.loaded_segments (0x5fa7c : word) = Some W_5fa7c.
Proof. vm_refl. Qed.
Lemma D_5fa7c : decode_any W_5fa7c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa80 : bv 32 := 0x00000693.
Lemma F_5fa80 : fetch_word AsanUbsan.M.loaded_segments (0x5fa80 : word) = Some W_5fa80.
Proof. vm_refl. Qed.
Lemma D_5fa80 : decode_any W_5fa80 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa84 : bv 32 := 0x578080ef.
Lemma F_5fa84 : fetch_word AsanUbsan.M.loaded_segments (0x5fa84 : word) = Some W_5fa84.
Proof. vm_refl. Qed.
Lemma D_5fa84 : decode_any W_5fa84 = Some (Jal 1 34168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa88 : bv 32 := 0x80040513.
Lemma F_5fa88 : fetch_word AsanUbsan.M.loaded_segments (0x5fa88 : word) = Some W_5fa88.
Proof. vm_refl. Qed.
Lemma D_5fa88 : decode_any W_5fa88 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa8c : bv 32 := 0xf9850513.
Lemma F_5fa8c : fetch_word AsanUbsan.M.loaded_segments (0x5fa8c : word) = Some W_5fa8c.
Proof. vm_refl. Qed.
Lemma D_5fa8c : decode_any W_5fa8c = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa90 : bv 32 := 0x089090ef.
Lemma F_5fa90 : fetch_word AsanUbsan.M.loaded_segments (0x5fa90 : word) = Some W_5fa90.
Proof. vm_refl. Qed.
Lemma D_5fa90 : decode_any W_5fa90 = Some (Jal 1 39048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa94 : bv 32 := 0x00050693.
Lemma F_5fa94 : fetch_word AsanUbsan.M.loaded_segments (0x5fa94 : word) = Some W_5fa94.
Proof. vm_refl. Qed.
Lemma D_5fa94 : decode_any W_5fa94 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa98 : bv 32 := 0x00040a13.
Lemma F_5fa98 : fetch_word AsanUbsan.M.loaded_segments (0x5fa98 : word) = Some W_5fa98.
Proof. vm_refl. Qed.
Lemma D_5fa98 : decode_any W_5fa98 = Some (OpImm ALU_ADD 20 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa9c : bv 32 := 0x00090613.
Lemma F_5fa9c : fetch_word AsanUbsan.M.loaded_segments (0x5fa9c : word) = Some W_5fa9c.
Proof. vm_refl. Qed.
Lemma D_5fa9c : decode_any W_5fa9c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5faa0 : bv 32 := 0x000b0593.
Lemma F_5faa0 : fetch_word AsanUbsan.M.loaded_segments (0x5faa0 : word) = Some W_5faa0.
Proof. vm_refl. Qed.
Lemma D_5faa0 : decode_any W_5faa0 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5faa4 : bv 32 := 0x00048513.
Lemma F_5faa4 : fetch_word AsanUbsan.M.loaded_segments (0x5faa4 : word) = Some W_5faa4.
Proof. vm_refl. Qed.
Lemma D_5faa4 : decode_any W_5faa4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5faa8 : bv 32 := 0xb8069ee3.
Lemma F_5faa8 : fetch_word AsanUbsan.M.loaded_segments (0x5faa8 : word) = Some W_5faa8.
Proof. vm_refl. Qed.
Lemma D_5faa8 : decode_any W_5faa8 = Some (Branch BC_NE 13 0 7068, 4%Z).
Proof. vm_refl. Qed.

Definition W_5faac : bv 32 := 0x0500006f.
Lemma F_5faac : fetch_word AsanUbsan.M.loaded_segments (0x5faac : word) = Some W_5faac.
Proof. vm_refl. Qed.
Lemma D_5faac : decode_any W_5faac = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fab0 : bv 32 := 0x00040993.
Lemma F_5fab0 : fetch_word AsanUbsan.M.loaded_segments (0x5fab0 : word) = Some W_5fab0.
Proof. vm_refl. Qed.
Lemma D_5fab0 : decode_any W_5fab0 = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fab4 : bv 32 := 0x7f9200ef.
Lemma F_5fab4 : fetch_word AsanUbsan.M.loaded_segments (0x5fab4 : word) = Some W_5fab4.
Proof. vm_refl. Qed.
Lemma D_5fab4 : decode_any W_5fab4 = Some (Jal 1 135160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fab8 : bv 32 := 0xfffb1597.
Lemma F_5fab8 : fetch_word AsanUbsan.M.loaded_segments (0x5fab8 : word) = Some W_5fab8.
Proof. vm_refl. Qed.
Lemma D_5fab8 : decode_any W_5fab8 = Some (Auipc 11 1048497, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fabc : bv 32 := 0x9505b583.
Lemma F_5fabc : fetch_word AsanUbsan.M.loaded_segments (0x5fabc : word) = Some W_5fabc.
Proof. vm_refl. Qed.
Lemma D_5fabc : decode_any W_5fabc = Some (Load SZ8 true 11 11 2384, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fac0 : bv 32 := 0x00bab023.
Lemma F_5fac0 : fetch_word AsanUbsan.M.loaded_segments (0x5fac0 : word) = Some W_5fac0.
Proof. vm_refl. Qed.
Lemma D_5fac0 : decode_any W_5fac0 = Some (Store SZ8 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fac4 : bv 32 := 0x80040613.
Lemma F_5fac4 : fetch_word AsanUbsan.M.loaded_segments (0x5fac4 : word) = Some W_5fac4.
Proof. vm_refl. Qed.
Lemma D_5fac4 : decode_any W_5fac4 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fac8 : bv 32 := 0xf9860613.
Lemma F_5fac8 : fetch_word AsanUbsan.M.loaded_segments (0x5fac8 : word) = Some W_5fac8.
Proof. vm_refl. Qed.
Lemma D_5fac8 : decode_any W_5fac8 = Some (OpImm ALU_ADD 12 12 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5facc : bv 32 := 0x00098593.
Lemma F_5facc : fetch_word AsanUbsan.M.loaded_segments (0x5facc : word) = Some W_5facc.
Proof. vm_refl. Qed.
Lemma D_5facc : decode_any W_5facc = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fad0 : bv 32 := 0x00090693.
Lemma F_5fad0 : fetch_word AsanUbsan.M.loaded_segments (0x5fad0 : word) = Some W_5fad0.
Proof. vm_refl. Qed.
Lemma D_5fad0 : decode_any W_5fad0 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fad4 : bv 32 := 0x00000713.
Lemma F_5fad4 : fetch_word AsanUbsan.M.loaded_segments (0x5fad4 : word) = Some W_5fad4.
Proof. vm_refl. Qed.
Lemma D_5fad4 : decode_any W_5fad4 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fad8 : bv 32 := 0x00048793.
Lemma F_5fad8 : fetch_word AsanUbsan.M.loaded_segments (0x5fad8 : word) = Some W_5fad8.
Proof. vm_refl. Qed.
Lemma D_5fad8 : decode_any W_5fad8 = Some (OpImm ALU_ADD 15 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fadc : bv 32 := 0x00000813.
Lemma F_5fadc : fetch_word AsanUbsan.M.loaded_segments (0x5fadc : word) = Some W_5fadc.
Proof. vm_refl. Qed.
Lemma D_5fadc : decode_any W_5fadc = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fae0 : bv 32 := 0x00000893.
Lemma F_5fae0 : fetch_word AsanUbsan.M.loaded_segments (0x5fae0 : word) = Some W_5fae0.
Proof. vm_refl. Qed.
Lemma D_5fae0 : decode_any W_5fae0 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fae4 : bv 32 := 0x029050ef.
Lemma F_5fae4 : fetch_word AsanUbsan.M.loaded_segments (0x5fae4 : word) = Some W_5fae4.
Proof. vm_refl. Qed.
Lemma D_5fae4 : decode_any W_5fae4 = Some (Jal 1 22568, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fae8 : bv 32 := 0x000b8513.
Lemma F_5fae8 : fetch_word AsanUbsan.M.loaded_segments (0x5fae8 : word) = Some W_5fae8.
Proof. vm_refl. Qed.
Lemma D_5fae8 : decode_any W_5fae8 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5faec : bv 32 := 0x000c0593.
Lemma F_5faec : fetch_word AsanUbsan.M.loaded_segments (0x5faec : word) = Some W_5faec.
Proof. vm_refl. Qed.
Lemma D_5faec : decode_any W_5faec = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5faf0 : bv 32 := 0x00048613.
Lemma F_5faf0 : fetch_word AsanUbsan.M.loaded_segments (0x5faf0 : word) = Some W_5faf0.
Proof. vm_refl. Qed.
Lemma D_5faf0 : decode_any W_5faf0 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5faf4 : bv 32 := 0xb09ff06f.
Lemma F_5faf4 : fetch_word AsanUbsan.M.loaded_segments (0x5faf4 : word) = Some W_5faf4.
Proof. vm_refl. Qed.
Lemma D_5faf4 : decode_any W_5faf4 = Some (Jal 0 2095880, 4%Z).
Proof. vm_refl. Qed.

Definition W_5faf8 : bv 32 := 0x00040a13.
Lemma F_5faf8 : fetch_word AsanUbsan.M.loaded_segments (0x5faf8 : word) = Some W_5faf8.
Proof. vm_refl. Qed.
Lemma D_5faf8 : decode_any W_5faf8 = Some (OpImm ALU_ADD 20 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fafc : bv 32 := 0x7b1200ef.
Lemma F_5fafc : fetch_word AsanUbsan.M.loaded_segments (0x5fafc : word) = Some W_5fafc.
Proof. vm_refl. Qed.
Lemma D_5fafc : decode_any W_5fafc = Some (Jal 1 135088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fb00 : bv 32 := 0xfffb1597.
Lemma F_5fb00 : fetch_word AsanUbsan.M.loaded_segments (0x5fb00 : word) = Some W_5fb00.
Proof. vm_refl. Qed.
Lemma D_5fb00 : decode_any W_5fb00 = Some (Auipc 11 1048497, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fb04 : bv 32 := 0x9085b583.
Lemma F_5fb04 : fetch_word AsanUbsan.M.loaded_segments (0x5fb04 : word) = Some W_5fb04.
Proof. vm_refl. Qed.
Lemma D_5fb04 : decode_any W_5fb04 = Some (Load SZ8 true 11 11 2312, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fb08 : bv 32 := 0x00bab023.
Lemma F_5fb08 : fetch_word AsanUbsan.M.loaded_segments (0x5fb08 : word) = Some W_5fb08.
Proof. vm_refl. Qed.
Lemma D_5fb08 : decode_any W_5fb08 = Some (Store SZ8 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fb0c : bv 32 := 0x80040613.
Lemma F_5fb0c : fetch_word AsanUbsan.M.loaded_segments (0x5fb0c : word) = Some W_5fb0c.
Proof. vm_refl. Qed.
Lemma D_5fb0c : decode_any W_5fb0c = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fb10 : bv 32 := 0xf9860613.
Lemma F_5fb10 : fetch_word AsanUbsan.M.loaded_segments (0x5fb10 : word) = Some W_5fb10.
Proof. vm_refl. Qed.
Lemma D_5fb10 : decode_any W_5fb10 = Some (OpImm ALU_ADD 12 12 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fb14 : bv 32 := 0x00100713.
Lemma F_5fb14 : fetch_word AsanUbsan.M.loaded_segments (0x5fb14 : word) = Some W_5fb14.
Proof. vm_refl. Qed.
Lemma D_5fb14 : decode_any W_5fb14 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fb18 : bv 32 := 0x000a0593.
Lemma F_5fb18 : fetch_word AsanUbsan.M.loaded_segments (0x5fb18 : word) = Some W_5fb18.
Proof. vm_refl. Qed.
Lemma D_5fb18 : decode_any W_5fb18 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fb1c : bv 32 := 0x00098693.
Lemma F_5fb1c : fetch_word AsanUbsan.M.loaded_segments (0x5fb1c : word) = Some W_5fb1c.
Proof. vm_refl. Qed.
Lemma D_5fb1c : decode_any W_5fb1c = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fb20 : bv 32 := 0x00090793.
Lemma F_5fb20 : fetch_word AsanUbsan.M.loaded_segments (0x5fb20 : word) = Some W_5fb20.
Proof. vm_refl. Qed.
Lemma D_5fb20 : decode_any W_5fb20 = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fb24 : bv 32 := 0x00000813.
Lemma F_5fb24 : fetch_word AsanUbsan.M.loaded_segments (0x5fb24 : word) = Some W_5fb24.
Proof. vm_refl. Qed.
Lemma D_5fb24 : decode_any W_5fb24 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fb28 : bv 32 := 0x00000893.
Lemma F_5fb28 : fetch_word AsanUbsan.M.loaded_segments (0x5fb28 : word) = Some W_5fb28.
Proof. vm_refl. Qed.
Lemma D_5fb28 : decode_any W_5fb28 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fb2c : bv 32 := 0x7e0050ef.
Lemma F_5fb2c : fetch_word AsanUbsan.M.loaded_segments (0x5fb2c : word) = Some W_5fb2c.
Proof. vm_refl. Qed.
Lemma D_5fb2c : decode_any W_5fb2c = Some (Jal 1 22496, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fb30 : bv 32 := 0x00048513.
Lemma F_5fb30 : fetch_word AsanUbsan.M.loaded_segments (0x5fb30 : word) = Some W_5fb30.
Proof. vm_refl. Qed.
Lemma D_5fb30 : decode_any W_5fb30 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fb34 : bv 32 := 0x000b0593.
Lemma F_5fb34 : fetch_word AsanUbsan.M.loaded_segments (0x5fb34 : word) = Some W_5fb34.
Proof. vm_refl. Qed.
Lemma D_5fb34 : decode_any W_5fb34 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fb38 : bv 32 := 0x00090613.
Lemma F_5fb38 : fetch_word AsanUbsan.M.loaded_segments (0x5fb38 : word) = Some W_5fb38.
Proof. vm_refl. Qed.
Lemma D_5fb38 : decode_any W_5fb38 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fb3c : bv 32 := 0xb09ff06f.
Lemma F_5fb3c : fetch_word AsanUbsan.M.loaded_segments (0x5fb3c : word) = Some W_5fb3c.
Proof. vm_refl. Qed.
Lemma D_5fb3c : decode_any W_5fb3c = Some (Jal 0 2095880, 4%Z).
Proof. vm_refl. Qed.
