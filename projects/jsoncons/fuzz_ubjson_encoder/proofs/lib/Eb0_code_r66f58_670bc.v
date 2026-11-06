(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_82344 : bv 32 := 0xfb010113.
Lemma F_82344 : fetch_word AsanUbsan.M.loaded_segments (0x82394 : word) = Some W_82344.
Proof. vm_refl. Qed.
Lemma D_82344 : decode_any W_82344 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_82348 : bv 32 := 0x04113423.
Lemma F_82348 : fetch_word AsanUbsan.M.loaded_segments (0x82398 : word) = Some W_82348.
Proof. vm_refl. Qed.
Lemma D_82348 : decode_any W_82348 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8234c : bv 32 := 0x04813023.
Lemma F_8234c : fetch_word AsanUbsan.M.loaded_segments (0x8239c : word) = Some W_8234c.
Proof. vm_refl. Qed.
Lemma D_8234c : decode_any W_8234c = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_82350 : bv 32 := 0x02913c23.
Lemma F_82350 : fetch_word AsanUbsan.M.loaded_segments (0x823a0 : word) = Some W_82350.
Proof. vm_refl. Qed.
Lemma D_82350 : decode_any W_82350 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_82354 : bv 32 := 0x03213823.
Lemma F_82354 : fetch_word AsanUbsan.M.loaded_segments (0x823a4 : word) = Some W_82354.
Proof. vm_refl. Qed.
Lemma D_82354 : decode_any W_82354 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_82358 : bv 32 := 0x03313423.
Lemma F_82358 : fetch_word AsanUbsan.M.loaded_segments (0x823a8 : word) = Some W_82358.
Proof. vm_refl. Qed.
Lemma D_82358 : decode_any W_82358 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8235c : bv 32 := 0x000c5517.
Lemma F_8235c : fetch_word AsanUbsan.M.loaded_segments (0x823ac : word) = Some W_8235c.
Proof. vm_refl. Qed.
Lemma D_8235c : decode_any W_8235c = Some (Auipc 10 197, 4%Z).
Proof. vm_refl. Qed.

Definition W_82360 : bv 32 := 0xa2c50493.
Lemma F_82360 : fetch_word AsanUbsan.M.loaded_segments (0x823b0 : word) = Some W_82360.
Proof. vm_refl. Qed.
Lemma D_82360 : decode_any W_82360 = Some (OpImm ALU_ADD 9 10 2604, 4%Z).
Proof. vm_refl. Qed.

Definition W_82364 : bv 32 := 0x00048503.
Lemma F_82364 : fetch_word AsanUbsan.M.loaded_segments (0x823b4 : word) = Some W_82364.
Proof. vm_refl. Qed.
Lemma D_82364 : decode_any W_82364 = Some (Load SZ1 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82368 : bv 32 := 0x00100593.
Lemma F_82368 : fetch_word AsanUbsan.M.loaded_segments (0x823b8 : word) = Some W_82368.
Proof. vm_refl. Qed.
Lemma D_82368 : decode_any W_82368 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8236c : bv 32 := 0x0230000f.
Lemma F_8236c : fetch_word AsanUbsan.M.loaded_segments (0x823bc : word) = Some W_8236c.
Proof. vm_refl. Qed.
Lemma D_8236c : decode_any W_8236c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82370 : bv 32 := 0x10b51e63.
Lemma F_82370 : fetch_word AsanUbsan.M.loaded_segments (0x823c0 : word) = Some W_82370.
Proof. vm_refl. Qed.
Lemma D_82370 : decode_any W_82370 = Some (Branch BC_NE 10 11 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_82374 : bv 32 := 0xbe1fa0ef.
Lemma F_82374 : fetch_word AsanUbsan.M.loaded_segments (0x823c4 : word) = Some W_82374.
Proof. vm_refl. Qed.
Lemma D_82374 : decode_any W_82374 = Some (Jal 1 2075616, 4%Z).
Proof. vm_refl. Qed.

Definition W_82378 : bv 32 := 0x0e051663.
Lemma F_82378 : fetch_word AsanUbsan.M.loaded_segments (0x823c8 : word) = Some W_82378.
Proof. vm_refl. Qed.
Lemma D_82378 : decode_any W_82378 = Some (Branch BC_NE 10 0 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_8237c : bv 32 := 0xfff8e517.
Lemma F_8237c : fetch_word AsanUbsan.M.loaded_segments (0x823cc : word) = Some W_8237c.
Proof. vm_refl. Qed.
Lemma D_8237c : decode_any W_8237c = Some (Auipc 10 1048462, 4%Z).
Proof. vm_refl. Qed.

Definition W_82380 : bv 32 := 0x0a453403.
Lemma F_82380 : fetch_word AsanUbsan.M.loaded_segments (0x823d0 : word) = Some W_82380.
Proof. vm_refl. Qed.
Lemma D_82380 : decode_any W_82380 = Some (Load SZ8 true 8 10 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_82384 : bv 32 := 0x02813023.
Lemma F_82384 : fetch_word AsanUbsan.M.loaded_segments (0x823d4 : word) = Some W_82384.
Proof. vm_refl. Qed.
Lemma D_82384 : decode_any W_82384 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_82388 : bv 32 := 0x00813c23.
Lemma F_82388 : fetch_word AsanUbsan.M.loaded_segments (0x823d8 : word) = Some W_82388.
Proof. vm_refl. Qed.
Lemma D_82388 : decode_any W_82388 = Some (Store SZ8 2 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8238c : bv 32 := 0x6b4020ef.
Lemma F_8238c : fetch_word AsanUbsan.M.loaded_segments (0x823dc : word) = Some W_8238c.
Proof. vm_refl. Qed.
Lemma D_8238c : decode_any W_8238c = Some (Jal 1 9908, 4%Z).
Proof. vm_refl. Qed.

Definition W_82390 : bv 32 := 0x08050263.
Lemma F_82390 : fetch_word AsanUbsan.M.loaded_segments (0x823e0 : word) = Some W_82390.
Proof. vm_refl. Qed.
Lemma D_82390 : decode_any W_82390 = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_82394 : bv 32 := 0x000bb597.
Lemma F_82394 : fetch_word AsanUbsan.M.loaded_segments (0x823e4 : word) = Some W_82394.
Proof. vm_refl. Qed.
Lemma D_82394 : decode_any W_82394 = Some (Auipc 11 187, 4%Z).
Proof. vm_refl. Qed.

Definition W_82398 : bv 32 := 0x4c45b903.
Lemma F_82398 : fetch_word AsanUbsan.M.loaded_segments (0x823e8 : word) = Some W_82398.
Proof. vm_refl. Qed.
Lemma D_82398 : decode_any W_82398 = Some (Load SZ8 true 18 11 1220, 4%Z).
Proof. vm_refl. Qed.

Definition W_8239c : bv 32 := 0x00093403.
Lemma F_8239c : fetch_word AsanUbsan.M.loaded_segments (0x823ec : word) = Some W_8239c.
Proof. vm_refl. Qed.
Lemma D_8239c : decode_any W_8239c = Some (Load SZ8 true 8 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_823a0 : bv 32 := 0x00041c63.
Lemma F_823a0 : fetch_word AsanUbsan.M.loaded_segments (0x823f0 : word) = Some W_823a0.
Proof. vm_refl. Qed.
Lemma D_823a0 : decode_any W_823a0 = Some (Branch BC_NE 8 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_823b8 : bv 32 := 0x04d020ef.
Lemma F_823b8 : fetch_word AsanUbsan.M.loaded_segments (0x82408 : word) = Some W_823b8.
Proof. vm_refl. Qed.
Lemma D_823b8 : decode_any W_823b8 = Some (Jal 1 10316, 4%Z).
Proof. vm_refl. Qed.

Definition W_823bc : bv 32 := 0x00050613.
Lemma F_823bc : fetch_word AsanUbsan.M.loaded_segments (0x8240c : word) = Some W_823bc.
Proof. vm_refl. Qed.
Lemma D_823bc : decode_any W_823bc = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_823c0 : bv 32 := 0x00a13c23.
Lemma F_823c0 : fetch_word AsanUbsan.M.loaded_segments (0x82410 : word) = Some W_823c0.
Proof. vm_refl. Qed.
Lemma D_823c0 : decode_any W_823c0 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_823c4 : bv 32 := 0x01010513.
Lemma F_823c4 : fetch_word AsanUbsan.M.loaded_segments (0x82414 : word) = Some W_823c4.
Proof. vm_refl. Qed.
Lemma D_823c4 : decode_any W_823c4 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_823c8 : bv 32 := 0x40850533.
Lemma F_823c8 : fetch_word AsanUbsan.M.loaded_segments (0x82418 : word) = Some W_823c8.
Proof. vm_refl. Qed.
Lemma D_823c8 : decode_any W_823c8 = Some (Op ALU_SUB 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_823cc : bv 32 := 0x408006b3.
Lemma F_823cc : fetch_word AsanUbsan.M.loaded_segments (0x8241c : word) = Some W_823cc.
Proof. vm_refl. Qed.
Lemma D_823cc : decode_any W_823cc = Some (Op ALU_SUB 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_823d0 : bv 32 := 0x00d576b3.
Lemma F_823d0 : fetch_word AsanUbsan.M.loaded_segments (0x82420 : word) = Some W_823d0.
Proof. vm_refl. Qed.
Lemma D_823d0 : decode_any W_823d0 = Some (Op ALU_AND 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_823d4 : bv 32 := 0x02d13023.
Lemma F_823d4 : fetch_word AsanUbsan.M.loaded_segments (0x82424 : word) = Some W_823d4.
Proof. vm_refl. Qed.
Lemma D_823d4 : decode_any W_823d4 = Some (Store SZ8 2 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_823d8 : bv 32 := 0x40d60733.
Lemma F_823d8 : fetch_word AsanUbsan.M.loaded_segments (0x82428 : word) = Some W_823d8.
Proof. vm_refl. Qed.
Lemma D_823d8 : decode_any W_823d8 = Some (Op ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_823dc : bv 32 := 0x04000537.
Lemma F_823dc : fetch_word AsanUbsan.M.loaded_segments (0x8242c : word) = Some W_823dc.
Proof. vm_refl. Qed.
Lemma D_823dc : decode_any W_823dc = Some (Lui 10 16384, 4%Z).
Proof. vm_refl. Qed.

Definition W_823e0 : bv 32 := 0x0015051b.
Lemma F_823e0 : fetch_word AsanUbsan.M.loaded_segments (0x82430 : word) = Some W_823e0.
Proof. vm_refl. Qed.
Lemma D_823e0 : decode_any W_823e0 = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_823e4 : bv 32 := 0x06a76263.
Lemma F_823e4 : fetch_word AsanUbsan.M.loaded_segments (0x82434 : word) = Some W_823e4.
Proof. vm_refl. Qed.
Lemma D_823e4 : decode_any W_823e4 = Some (Branch BC_LTU 14 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_82448 : bv 32 := 0x00770713.
Lemma F_82448 : fetch_word AsanUbsan.M.loaded_segments (0x82498 : word) = Some W_82448.
Proof. vm_refl. Qed.
Lemma D_82448 : decode_any W_82448 = Some (OpImm ALU_ADD 14 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8244c : bv 32 := 0x10000537.
Lemma F_8244c : fetch_word AsanUbsan.M.loaded_segments (0x8249c : word) = Some W_8244c.
Proof. vm_refl. Qed.
Lemma D_8244c : decode_any W_8244c = Some (Lui 10 65536, 4%Z).
Proof. vm_refl. Qed.

Definition W_82450 : bv 32 := 0xff85051b.
Lemma F_82450 : fetch_word AsanUbsan.M.loaded_segments (0x824a0 : word) = Some W_82450.
Proof. vm_refl. Qed.
Lemma D_82450 : decode_any W_82450 = Some (OpImm32 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_82454 : bv 32 := 0x00a775b3.
Lemma F_82454 : fetch_word AsanUbsan.M.loaded_segments (0x824a4 : word) = Some W_82454.
Proof. vm_refl. Qed.
Lemma D_82454 : decode_any W_82454 = Some (Op ALU_AND 11 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_82458 : bv 32 := 0x00068513.
Lemma F_82458 : fetch_word AsanUbsan.M.loaded_segments (0x824a8 : word) = Some W_82458.
Proof. vm_refl. Qed.
Lemma D_82458 : decode_any W_82458 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8245c : bv 32 := 0x00000613.
Lemma F_8245c : fetch_word AsanUbsan.M.loaded_segments (0x824ac : word) = Some W_8245c.
Proof. vm_refl. Qed.
Lemma D_8245c : decode_any W_8245c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82460 : bv 32 := 0x835f90ef.
Lemma F_82460 : fetch_word AsanUbsan.M.loaded_segments (0x824b0 : word) = Some W_82460.
Proof. vm_refl. Qed.
Lemma D_82460 : decode_any W_82460 = Some (Jal 1 2070580, 4%Z).
Proof. vm_refl. Qed.

Definition W_82464 : bv 32 := 0x5dc020ef.
Lemma F_82464 : fetch_word AsanUbsan.M.loaded_segments (0x824b4 : word) = Some W_82464.
Proof. vm_refl. Qed.
Lemma D_82464 : decode_any W_82464 = Some (Jal 1 9692, 4%Z).
Proof. vm_refl. Qed.

Definition W_82468 : bv 32 := 0x02050263.
Lemma F_82468 : fetch_word AsanUbsan.M.loaded_segments (0x824b8 : word) = Some W_82468.
Proof. vm_refl. Qed.
Lemma D_82468 : decode_any W_82468 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_8246c : bv 32 := 0x02850583.
Lemma F_8246c : fetch_word AsanUbsan.M.loaded_segments (0x824bc : word) = Some W_8246c.
Proof. vm_refl. Qed.
Lemma D_8246c : decode_any W_8246c = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_82470 : bv 32 := 0x00059e63.
Lemma F_82470 : fetch_word AsanUbsan.M.loaded_segments (0x824c0 : word) = Some W_82470.
Proof. vm_refl. Qed.
Lemma D_82470 : decode_any W_82470 = Some (Branch BC_NE 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_82474 : bv 32 := 0x04853503.
Lemma F_82474 : fetch_word AsanUbsan.M.loaded_segments (0x824c4 : word) = Some W_82474.
Proof. vm_refl. Qed.
Lemma D_82474 : decode_any W_82474 = Some (Load SZ8 true 10 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_82478 : bv 32 := 0x00253593.
Lemma F_82478 : fetch_word AsanUbsan.M.loaded_segments (0x824c8 : word) = Some W_82478.
Proof. vm_refl. Qed.
Lemma D_82478 : decode_any W_82478 = Some (OpImm ALU_SLTU 11 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8247c : bv 32 := 0xfff58593.
Lemma F_8247c : fetch_word AsanUbsan.M.loaded_segments (0x824cc : word) = Some W_8247c.
Proof. vm_refl. Qed.
Lemma D_8247c : decode_any W_8247c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82480 : bv 32 := 0x00a5f533.
Lemma F_82480 : fetch_word AsanUbsan.M.loaded_segments (0x824d0 : word) = Some W_82480.
Proof. vm_refl. Qed.
Lemma D_82480 : decode_any W_82480 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_82484 : bv 32 := 0x00050463.
Lemma F_82484 : fetch_word AsanUbsan.M.loaded_segments (0x824d4 : word) = Some W_82484.
Proof. vm_refl. Qed.
Lemma D_82484 : decode_any W_82484 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82488 : bv 32 := 0xe00dc0ef.
Lemma F_82488 : fetch_word AsanUbsan.M.loaded_segments (0x824d8 : word) = Some W_82488.
Proof. vm_refl. Qed.
Lemma D_82488 : decode_any W_82488 = Some (Jal 1 1951232, 4%Z).
Proof. vm_refl. Qed.

Definition W_8248c : bv 32 := 0x04813083.
Lemma F_8248c : fetch_word AsanUbsan.M.loaded_segments (0x824dc : word) = Some W_8248c.
Proof. vm_refl. Qed.
Lemma D_8248c : decode_any W_8248c = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_82490 : bv 32 := 0x04013403.
Lemma F_82490 : fetch_word AsanUbsan.M.loaded_segments (0x824e0 : word) = Some W_82490.
Proof. vm_refl. Qed.
Lemma D_82490 : decode_any W_82490 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_82494 : bv 32 := 0x03813483.
Lemma F_82494 : fetch_word AsanUbsan.M.loaded_segments (0x824e4 : word) = Some W_82494.
Proof. vm_refl. Qed.
Lemma D_82494 : decode_any W_82494 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_82498 : bv 32 := 0x03013903.
Lemma F_82498 : fetch_word AsanUbsan.M.loaded_segments (0x824e8 : word) = Some W_82498.
Proof. vm_refl. Qed.
Lemma D_82498 : decode_any W_82498 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8249c : bv 32 := 0x02813983.
Lemma F_8249c : fetch_word AsanUbsan.M.loaded_segments (0x824ec : word) = Some W_8249c.
Proof. vm_refl. Qed.
Lemma D_8249c : decode_any W_8249c = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_824a0 : bv 32 := 0x05010113.
Lemma F_824a0 : fetch_word AsanUbsan.M.loaded_segments (0x824f0 : word) = Some W_824a0.
Proof. vm_refl. Qed.
Lemma D_824a0 : decode_any W_824a0 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_824a4 : bv 32 := 0x00008067.
Lemma F_824a4 : fetch_word AsanUbsan.M.loaded_segments (0x824f4 : word) = Some W_824a4.
Proof. vm_refl. Qed.
Lemma D_824a4 : decode_any W_824a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
