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

Definition W_67368 : bv 32 := 0xfb010113.
Lemma F_67368 : fetch_word AsanUbsan.M.loaded_segments (0x67368 : word) = Some W_67368.
Proof. vm_refl. Qed.
Lemma D_67368 : decode_any W_67368 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6736c : bv 32 := 0x04113423.
Lemma F_6736c : fetch_word AsanUbsan.M.loaded_segments (0x6736c : word) = Some W_6736c.
Proof. vm_refl. Qed.
Lemma D_6736c : decode_any W_6736c = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_67370 : bv 32 := 0x04813023.
Lemma F_67370 : fetch_word AsanUbsan.M.loaded_segments (0x67370 : word) = Some W_67370.
Proof. vm_refl. Qed.
Lemma D_67370 : decode_any W_67370 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_67374 : bv 32 := 0x02913c23.
Lemma F_67374 : fetch_word AsanUbsan.M.loaded_segments (0x67374 : word) = Some W_67374.
Proof. vm_refl. Qed.
Lemma D_67374 : decode_any W_67374 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_67378 : bv 32 := 0x03213823.
Lemma F_67378 : fetch_word AsanUbsan.M.loaded_segments (0x67378 : word) = Some W_67378.
Proof. vm_refl. Qed.
Lemma D_67378 : decode_any W_67378 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6737c : bv 32 := 0x03313423.
Lemma F_6737c : fetch_word AsanUbsan.M.loaded_segments (0x6737c : word) = Some W_6737c.
Proof. vm_refl. Qed.
Lemma D_6737c : decode_any W_6737c = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_67380 : bv 32 := 0x00078517.
Lemma F_67380 : fetch_word AsanUbsan.M.loaded_segments (0x67380 : word) = Some W_67380.
Proof. vm_refl. Qed.
Lemma D_67380 : decode_any W_67380 = Some (Auipc 10 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_67384 : bv 32 := 0x09850493.
Lemma F_67384 : fetch_word AsanUbsan.M.loaded_segments (0x67384 : word) = Some W_67384.
Proof. vm_refl. Qed.
Lemma D_67384 : decode_any W_67384 = Some (OpImm ALU_ADD 9 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_67388 : bv 32 := 0x00048503.
Lemma F_67388 : fetch_word AsanUbsan.M.loaded_segments (0x67388 : word) = Some W_67388.
Proof. vm_refl. Qed.
Lemma D_67388 : decode_any W_67388 = Some (Load SZ1 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6738c : bv 32 := 0x00100593.
Lemma F_6738c : fetch_word AsanUbsan.M.loaded_segments (0x6738c : word) = Some W_6738c.
Proof. vm_refl. Qed.
Lemma D_6738c : decode_any W_6738c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_67390 : bv 32 := 0x0230000f.
Lemma F_67390 : fetch_word AsanUbsan.M.loaded_segments (0x67390 : word) = Some W_67390.
Proof. vm_refl. Qed.
Lemma D_67390 : decode_any W_67390 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67394 : bv 32 := 0x10b51e63.
Lemma F_67394 : fetch_word AsanUbsan.M.loaded_segments (0x67394 : word) = Some W_67394.
Proof. vm_refl. Qed.
Lemma D_67394 : decode_any W_67394 = Some (Branch BC_NE 10 11 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_67398 : bv 32 := 0xe5dfa0ef.
Lemma F_67398 : fetch_word AsanUbsan.M.loaded_segments (0x67398 : word) = Some W_67398.
Proof. vm_refl. Qed.
Lemma D_67398 : decode_any W_67398 = Some (Jal 1 2076252, 4%Z).
Proof. vm_refl. Qed.

Definition W_6739c : bv 32 := 0x0e051663.
Lemma F_6739c : fetch_word AsanUbsan.M.loaded_segments (0x6739c : word) = Some W_6739c.
Proof. vm_refl. Qed.
Lemma D_6739c : decode_any W_6739c = Some (Branch BC_NE 10 0 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_673a0 : bv 32 := 0xfffa9517.
Lemma F_673a0 : fetch_word AsanUbsan.M.loaded_segments (0x673a0 : word) = Some W_673a0.
Proof. vm_refl. Qed.
Lemma D_673a0 : decode_any W_673a0 = Some (Auipc 10 1048489, 4%Z).
Proof. vm_refl. Qed.

Definition W_673a4 : bv 32 := 0x06853403.
Lemma F_673a4 : fetch_word AsanUbsan.M.loaded_segments (0x673a4 : word) = Some W_673a4.
Proof. vm_refl. Qed.
Lemma D_673a4 : decode_any W_673a4 = Some (Load SZ8 true 8 10 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_673a8 : bv 32 := 0x02813023.
Lemma F_673a8 : fetch_word AsanUbsan.M.loaded_segments (0x673a8 : word) = Some W_673a8.
Proof. vm_refl. Qed.
Lemma D_673a8 : decode_any W_673a8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_673ac : bv 32 := 0x00813c23.
Lemma F_673ac : fetch_word AsanUbsan.M.loaded_segments (0x673ac : word) = Some W_673ac.
Proof. vm_refl. Qed.
Lemma D_673ac : decode_any W_673ac = Some (Store SZ8 2 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_673b0 : bv 32 := 0x6b4020ef.
Lemma F_673b0 : fetch_word AsanUbsan.M.loaded_segments (0x673b0 : word) = Some W_673b0.
Proof. vm_refl. Qed.
Lemma D_673b0 : decode_any W_673b0 = Some (Jal 1 9908, 4%Z).
Proof. vm_refl. Qed.

Definition W_673b4 : bv 32 := 0x08050263.
Lemma F_673b4 : fetch_word AsanUbsan.M.loaded_segments (0x673b4 : word) = Some W_673b4.
Proof. vm_refl. Qed.
Lemma D_673b4 : decode_any W_673b4 = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_673b8 : bv 32 := 0x0006f597.
Lemma F_673b8 : fetch_word AsanUbsan.M.loaded_segments (0x673b8 : word) = Some W_673b8.
Proof. vm_refl. Qed.
Lemma D_673b8 : decode_any W_673b8 = Some (Auipc 11 111, 4%Z).
Proof. vm_refl. Qed.

Definition W_673bc : bv 32 := 0x0f05b903.
Lemma F_673bc : fetch_word AsanUbsan.M.loaded_segments (0x673bc : word) = Some W_673bc.
Proof. vm_refl. Qed.
Lemma D_673bc : decode_any W_673bc = Some (Load SZ8 true 18 11 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_673c0 : bv 32 := 0x00093403.
Lemma F_673c0 : fetch_word AsanUbsan.M.loaded_segments (0x673c0 : word) = Some W_673c0.
Proof. vm_refl. Qed.
Lemma D_673c0 : decode_any W_673c0 = Some (Load SZ8 true 8 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_673c4 : bv 32 := 0x00041c63.
Lemma F_673c4 : fetch_word AsanUbsan.M.loaded_segments (0x673c4 : word) = Some W_673c4.
Proof. vm_refl. Qed.
Lemma D_673c4 : decode_any W_673c4 = Some (Branch BC_NE 8 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_673c8 : bv 32 := 0x00050993.
Lemma F_673c8 : fetch_word AsanUbsan.M.loaded_segments (0x673c8 : word) = Some W_673c8.
Proof. vm_refl. Qed.
Lemma D_673c8 : decode_any W_673c8 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_673cc : bv 32 := 0x1410b0ef.
Lemma F_673cc : fetch_word AsanUbsan.M.loaded_segments (0x673cc : word) = Some W_673cc.
Proof. vm_refl. Qed.
Lemma D_673cc : decode_any W_673cc = Some (Jal 1 47424, 4%Z).
Proof. vm_refl. Qed.

Definition W_673d0 : bv 32 := 0x00050413.
Lemma F_673d0 : fetch_word AsanUbsan.M.loaded_segments (0x673d0 : word) = Some W_673d0.
Proof. vm_refl. Qed.
Lemma D_673d0 : decode_any W_673d0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_673d4 : bv 32 := 0x00098513.
Lemma F_673d4 : fetch_word AsanUbsan.M.loaded_segments (0x673d4 : word) = Some W_673d4.
Proof. vm_refl. Qed.
Lemma D_673d4 : decode_any W_673d4 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_673d8 : bv 32 := 0x00893023.
Lemma F_673d8 : fetch_word AsanUbsan.M.loaded_segments (0x673d8 : word) = Some W_673d8.
Proof. vm_refl. Qed.
Lemma D_673d8 : decode_any W_673d8 = Some (Store SZ8 18 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_673dc : bv 32 := 0x04d020ef.
Lemma F_673dc : fetch_word AsanUbsan.M.loaded_segments (0x673dc : word) = Some W_673dc.
Proof. vm_refl. Qed.
Lemma D_673dc : decode_any W_673dc = Some (Jal 1 10316, 4%Z).
Proof. vm_refl. Qed.

Definition W_673e0 : bv 32 := 0x00050613.
Lemma F_673e0 : fetch_word AsanUbsan.M.loaded_segments (0x673e0 : word) = Some W_673e0.
Proof. vm_refl. Qed.
Lemma D_673e0 : decode_any W_673e0 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_673e4 : bv 32 := 0x00a13c23.
Lemma F_673e4 : fetch_word AsanUbsan.M.loaded_segments (0x673e4 : word) = Some W_673e4.
Proof. vm_refl. Qed.
Lemma D_673e4 : decode_any W_673e4 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_673e8 : bv 32 := 0x01010513.
Lemma F_673e8 : fetch_word AsanUbsan.M.loaded_segments (0x673e8 : word) = Some W_673e8.
Proof. vm_refl. Qed.
Lemma D_673e8 : decode_any W_673e8 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_673ec : bv 32 := 0x40850533.
Lemma F_673ec : fetch_word AsanUbsan.M.loaded_segments (0x673ec : word) = Some W_673ec.
Proof. vm_refl. Qed.
Lemma D_673ec : decode_any W_673ec = Some (Op ALU_SUB 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_673f0 : bv 32 := 0x408006b3.
Lemma F_673f0 : fetch_word AsanUbsan.M.loaded_segments (0x673f0 : word) = Some W_673f0.
Proof. vm_refl. Qed.
Lemma D_673f0 : decode_any W_673f0 = Some (Op ALU_SUB 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_673f4 : bv 32 := 0x00d576b3.
Lemma F_673f4 : fetch_word AsanUbsan.M.loaded_segments (0x673f4 : word) = Some W_673f4.
Proof. vm_refl. Qed.
Lemma D_673f4 : decode_any W_673f4 = Some (Op ALU_AND 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_673f8 : bv 32 := 0x02d13023.
Lemma F_673f8 : fetch_word AsanUbsan.M.loaded_segments (0x673f8 : word) = Some W_673f8.
Proof. vm_refl. Qed.
Lemma D_673f8 : decode_any W_673f8 = Some (Store SZ8 2 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_673fc : bv 32 := 0x40d60733.
Lemma F_673fc : fetch_word AsanUbsan.M.loaded_segments (0x673fc : word) = Some W_673fc.
Proof. vm_refl. Qed.
Lemma D_673fc : decode_any W_673fc = Some (Op ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_67400 : bv 32 := 0x04000537.
Lemma F_67400 : fetch_word AsanUbsan.M.loaded_segments (0x67400 : word) = Some W_67400.
Proof. vm_refl. Qed.
Lemma D_67400 : decode_any W_67400 = Some (Lui 10 16384, 4%Z).
Proof. vm_refl. Qed.

Definition W_67404 : bv 32 := 0x0015051b.
Lemma F_67404 : fetch_word AsanUbsan.M.loaded_segments (0x67404 : word) = Some W_67404.
Proof. vm_refl. Qed.
Lemma D_67404 : decode_any W_67404 = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_67408 : bv 32 := 0x06a76263.
Lemma F_67408 : fetch_word AsanUbsan.M.loaded_segments (0x67408 : word) = Some W_67408.
Proof. vm_refl. Qed.
Lemma D_67408 : decode_any W_67408 = Some (Branch BC_LTU 14 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_6740c : bv 32 := 0x0034c503.
Lemma F_6740c : fetch_word AsanUbsan.M.loaded_segments (0x6740c : word) = Some W_6740c.
Proof. vm_refl. Qed.
Lemma D_6740c : decode_any W_6740c = Some (Load SZ1 false 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_67410 : bv 32 := 0x06051c63.
Lemma F_67410 : fetch_word AsanUbsan.M.loaded_segments (0x67410 : word) = Some W_67410.
Proof. vm_refl. Qed.
Lemma D_67410 : decode_any W_67410 = Some (Branch BC_NE 10 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_67414 : bv 32 := 0x00100513.
Lemma F_67414 : fetch_word AsanUbsan.M.loaded_segments (0x67414 : word) = Some W_67414.
Proof. vm_refl. Qed.
Lemma D_67414 : decode_any W_67414 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_67418 : bv 32 := 0x00a481a3.
Lemma F_67418 : fetch_word AsanUbsan.M.loaded_segments (0x67418 : word) = Some W_67418.
Proof. vm_refl. Qed.
Lemma D_67418 : decode_any W_67418 = Some (Store SZ1 9 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6741c : bv 32 := 0xfffac517.
Lemma F_6741c : fetch_word AsanUbsan.M.loaded_segments (0x6741c : word) = Some W_6741c.
Proof. vm_refl. Qed.
Lemma D_6741c : decode_any W_6741c = Some (Auipc 10 1048492, 4%Z).
Proof. vm_refl. Qed.

Definition W_67420 : bv 32 := 0xfffb3597.
Lemma F_67420 : fetch_word AsanUbsan.M.loaded_segments (0x67420 : word) = Some W_67420.
Proof. vm_refl. Qed.
Lemma D_67420 : decode_any W_67420 = Some (Auipc 11 1048499, 4%Z).
Proof. vm_refl. Qed.

Definition W_67424 : bv 32 := 0x18950513.
Lemma F_67424 : fetch_word AsanUbsan.M.loaded_segments (0x67424 : word) = Some W_67424.
Proof. vm_refl. Qed.
Lemma D_67424 : decode_any W_67424 = Some (OpImm ALU_ADD 10 10 393, 4%Z).
Proof. vm_refl. Qed.

Definition W_67428 : bv 32 := 0x67658593.
Lemma F_67428 : fetch_word AsanUbsan.M.loaded_segments (0x67428 : word) = Some W_67428.
Proof. vm_refl. Qed.
Lemma D_67428 : decode_any W_67428 = Some (OpImm ALU_ADD 11 11 1654, 4%Z).
Proof. vm_refl. Qed.

Definition W_6742c : bv 32 := 0x00070793.
Lemma F_6742c : fetch_word AsanUbsan.M.loaded_segments (0x6742c : word) = Some W_6742c.
Proof. vm_refl. Qed.
Lemma D_6742c : decode_any W_6742c = Some (OpImm ALU_ADD 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67430 : bv 32 := 0x5d80d0ef.
Lemma F_67430 : fetch_word AsanUbsan.M.loaded_segments (0x67430 : word) = Some W_67430.
Proof. vm_refl. Qed.
Lemma D_67430 : decode_any W_67430 = Some (Jal 1 54744, 4%Z).
Proof. vm_refl. Qed.

Definition W_67434 : bv 32 := 0x0540006f.
Lemma F_67434 : fetch_word AsanUbsan.M.loaded_segments (0x67434 : word) = Some W_67434.
Proof. vm_refl. Qed.
Lemma D_67434 : decode_any W_67434 = Some (Jal 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_67438 : bv 32 := 0x00813823.
Lemma F_67438 : fetch_word AsanUbsan.M.loaded_segments (0x67438 : word) = Some W_67438.
Proof. vm_refl. Qed.
Lemma D_67438 : decode_any W_67438 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6743c : bv 32 := 0x00813423.
Lemma F_6743c : fetch_word AsanUbsan.M.loaded_segments (0x6743c : word) = Some W_6743c.
Proof. vm_refl. Qed.
Lemma D_6743c : decode_any W_6743c = Some (Store SZ8 2 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_67440 : bv 32 := 0x02010593.
Lemma F_67440 : fetch_word AsanUbsan.M.loaded_segments (0x67440 : word) = Some W_67440.
Proof. vm_refl. Qed.
Lemma D_67440 : decode_any W_67440 = Some (OpImm ALU_ADD 11 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_67444 : bv 32 := 0x01810613.
Lemma F_67444 : fetch_word AsanUbsan.M.loaded_segments (0x67444 : word) = Some W_67444.
Proof. vm_refl. Qed.
Lemma D_67444 : decode_any W_67444 = Some (OpImm ALU_ADD 12 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_67448 : bv 32 := 0x01010693.
Lemma F_67448 : fetch_word AsanUbsan.M.loaded_segments (0x67448 : word) = Some W_67448.
Proof. vm_refl. Qed.
Lemma D_67448 : decode_any W_67448 = Some (OpImm ALU_ADD 13 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6744c : bv 32 := 0x00810713.
Lemma F_6744c : fetch_word AsanUbsan.M.loaded_segments (0x6744c : word) = Some W_6744c.
Proof. vm_refl. Qed.
Lemma D_6744c : decode_any W_6744c = Some (OpImm ALU_ADD 14 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_67450 : bv 32 := 0x180130ef.
Lemma F_67450 : fetch_word AsanUbsan.M.loaded_segments (0x67450 : word) = Some W_67450.
Proof. vm_refl. Qed.
Lemma D_67450 : decode_any W_67450 = Some (Jal 1 78208, 4%Z).
Proof. vm_refl. Qed.

Definition W_67454 : bv 32 := 0x02013683.
Lemma F_67454 : fetch_word AsanUbsan.M.loaded_segments (0x67454 : word) = Some W_67454.
Proof. vm_refl. Qed.
Lemma D_67454 : decode_any W_67454 = Some (Load SZ8 true 13 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_67458 : bv 32 := 0x01813603.
Lemma F_67458 : fetch_word AsanUbsan.M.loaded_segments (0x67458 : word) = Some W_67458.
Proof. vm_refl. Qed.
Lemma D_67458 : decode_any W_67458 = Some (Load SZ8 true 12 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6745c : bv 32 := 0x40d60733.
Lemma F_6745c : fetch_word AsanUbsan.M.loaded_segments (0x6745c : word) = Some W_6745c.
Proof. vm_refl. Qed.
Lemma D_6745c : decode_any W_6745c = Some (Op ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_67460 : bv 32 := 0x04000537.
Lemma F_67460 : fetch_word AsanUbsan.M.loaded_segments (0x67460 : word) = Some W_67460.
Proof. vm_refl. Qed.
Lemma D_67460 : decode_any W_67460 = Some (Lui 10 16384, 4%Z).
Proof. vm_refl. Qed.

Definition W_67464 : bv 32 := 0x0015051b.
Lemma F_67464 : fetch_word AsanUbsan.M.loaded_segments (0x67464 : word) = Some W_67464.
Proof. vm_refl. Qed.
Lemma D_67464 : decode_any W_67464 = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_67468 : bv 32 := 0xfaa772e3.
Lemma F_67468 : fetch_word AsanUbsan.M.loaded_segments (0x67468 : word) = Some W_67468.
Proof. vm_refl. Qed.
Lemma D_67468 : decode_any W_67468 = Some (Branch BC_GEU 14 10 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_6746c : bv 32 := 0x00770713.
Lemma F_6746c : fetch_word AsanUbsan.M.loaded_segments (0x6746c : word) = Some W_6746c.
Proof. vm_refl. Qed.
Lemma D_6746c : decode_any W_6746c = Some (OpImm ALU_ADD 14 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_67470 : bv 32 := 0x10000537.
Lemma F_67470 : fetch_word AsanUbsan.M.loaded_segments (0x67470 : word) = Some W_67470.
Proof. vm_refl. Qed.
Lemma D_67470 : decode_any W_67470 = Some (Lui 10 65536, 4%Z).
Proof. vm_refl. Qed.

Definition W_67474 : bv 32 := 0xff85051b.
Lemma F_67474 : fetch_word AsanUbsan.M.loaded_segments (0x67474 : word) = Some W_67474.
Proof. vm_refl. Qed.
Lemma D_67474 : decode_any W_67474 = Some (OpImm32 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_67478 : bv 32 := 0x00a775b3.
Lemma F_67478 : fetch_word AsanUbsan.M.loaded_segments (0x67478 : word) = Some W_67478.
Proof. vm_refl. Qed.
Lemma D_67478 : decode_any W_67478 = Some (Op ALU_AND 11 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6747c : bv 32 := 0x00068513.
Lemma F_6747c : fetch_word AsanUbsan.M.loaded_segments (0x6747c : word) = Some W_6747c.
Proof. vm_refl. Qed.
Lemma D_6747c : decode_any W_6747c = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67480 : bv 32 := 0x00000613.
Lemma F_67480 : fetch_word AsanUbsan.M.loaded_segments (0x67480 : word) = Some W_67480.
Proof. vm_refl. Qed.
Lemma D_67480 : decode_any W_67480 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67484 : bv 32 := 0xd75f90ef.
Lemma F_67484 : fetch_word AsanUbsan.M.loaded_segments (0x67484 : word) = Some W_67484.
Proof. vm_refl. Qed.
Lemma D_67484 : decode_any W_67484 = Some (Jal 1 2071924, 4%Z).
Proof. vm_refl. Qed.

Definition W_67488 : bv 32 := 0x5dc020ef.
Lemma F_67488 : fetch_word AsanUbsan.M.loaded_segments (0x67488 : word) = Some W_67488.
Proof. vm_refl. Qed.
Lemma D_67488 : decode_any W_67488 = Some (Jal 1 9692, 4%Z).
Proof. vm_refl. Qed.

Definition W_6748c : bv 32 := 0x02050263.
Lemma F_6748c : fetch_word AsanUbsan.M.loaded_segments (0x6748c : word) = Some W_6748c.
Proof. vm_refl. Qed.
Lemma D_6748c : decode_any W_6748c = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_67490 : bv 32 := 0x02850583.
Lemma F_67490 : fetch_word AsanUbsan.M.loaded_segments (0x67490 : word) = Some W_67490.
Proof. vm_refl. Qed.
Lemma D_67490 : decode_any W_67490 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_67494 : bv 32 := 0x00059e63.
Lemma F_67494 : fetch_word AsanUbsan.M.loaded_segments (0x67494 : word) = Some W_67494.
Proof. vm_refl. Qed.
Lemma D_67494 : decode_any W_67494 = Some (Branch BC_NE 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_67498 : bv 32 := 0x04853503.
Lemma F_67498 : fetch_word AsanUbsan.M.loaded_segments (0x67498 : word) = Some W_67498.
Proof. vm_refl. Qed.
Lemma D_67498 : decode_any W_67498 = Some (Load SZ8 true 10 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_6749c : bv 32 := 0x00253593.
Lemma F_6749c : fetch_word AsanUbsan.M.loaded_segments (0x6749c : word) = Some W_6749c.
Proof. vm_refl. Qed.
Lemma D_6749c : decode_any W_6749c = Some (OpImm ALU_SLTU 11 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_674a0 : bv 32 := 0xfff58593.
Lemma F_674a0 : fetch_word AsanUbsan.M.loaded_segments (0x674a0 : word) = Some W_674a0.
Proof. vm_refl. Qed.
Lemma D_674a0 : decode_any W_674a0 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_674a4 : bv 32 := 0x00a5f533.
Lemma F_674a4 : fetch_word AsanUbsan.M.loaded_segments (0x674a4 : word) = Some W_674a4.
Proof. vm_refl. Qed.
Lemma D_674a4 : decode_any W_674a4 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_674a8 : bv 32 := 0x00050463.
Lemma F_674a8 : fetch_word AsanUbsan.M.loaded_segments (0x674a8 : word) = Some W_674a8.
Proof. vm_refl. Qed.
Lemma D_674a8 : decode_any W_674a8 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_674ac : bv 32 := 0xe28e10ef.
Lemma F_674ac : fetch_word AsanUbsan.M.loaded_segments (0x674ac : word) = Some W_674ac.
Proof. vm_refl. Qed.
Lemma D_674ac : decode_any W_674ac = Some (Jal 1 1971752, 4%Z).
Proof. vm_refl. Qed.

Definition W_674b0 : bv 32 := 0x04813083.
Lemma F_674b0 : fetch_word AsanUbsan.M.loaded_segments (0x674b0 : word) = Some W_674b0.
Proof. vm_refl. Qed.
Lemma D_674b0 : decode_any W_674b0 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_674b4 : bv 32 := 0x04013403.
Lemma F_674b4 : fetch_word AsanUbsan.M.loaded_segments (0x674b4 : word) = Some W_674b4.
Proof. vm_refl. Qed.
Lemma D_674b4 : decode_any W_674b4 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_674b8 : bv 32 := 0x03813483.
Lemma F_674b8 : fetch_word AsanUbsan.M.loaded_segments (0x674b8 : word) = Some W_674b8.
Proof. vm_refl. Qed.
Lemma D_674b8 : decode_any W_674b8 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_674bc : bv 32 := 0x03013903.
Lemma F_674bc : fetch_word AsanUbsan.M.loaded_segments (0x674bc : word) = Some W_674bc.
Proof. vm_refl. Qed.
Lemma D_674bc : decode_any W_674bc = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_674c0 : bv 32 := 0x02813983.
Lemma F_674c0 : fetch_word AsanUbsan.M.loaded_segments (0x674c0 : word) = Some W_674c0.
Proof. vm_refl. Qed.
Lemma D_674c0 : decode_any W_674c0 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_674c4 : bv 32 := 0x05010113.
Lemma F_674c4 : fetch_word AsanUbsan.M.loaded_segments (0x674c4 : word) = Some W_674c4.
Proof. vm_refl. Qed.
Lemma D_674c4 : decode_any W_674c4 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_674c8 : bv 32 := 0x00008067.
Lemma F_674c8 : fetch_word AsanUbsan.M.loaded_segments (0x674c8 : word) = Some W_674c8.
Proof. vm_refl. Qed.
Lemma D_674c8 : decode_any W_674c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
