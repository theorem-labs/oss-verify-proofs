(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_18340 : bv 32 := 0xfd010113.
Lemma F_18340 : fetch_word Ubsan.M.loaded_segments (0x18340 : word) = Some W_18340.
Proof. vm_refl. Qed.
Lemma D_18340 : decode_any W_18340 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_18344 : bv 32 := 0x02113423.
Lemma F_18344 : fetch_word Ubsan.M.loaded_segments (0x18344 : word) = Some W_18344.
Proof. vm_refl. Qed.
Lemma D_18344 : decode_any W_18344 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18348 : bv 32 := 0x02813023.
Lemma F_18348 : fetch_word Ubsan.M.loaded_segments (0x18348 : word) = Some W_18348.
Proof. vm_refl. Qed.
Lemma D_18348 : decode_any W_18348 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1834c : bv 32 := 0x00913c23.
Lemma F_1834c : fetch_word Ubsan.M.loaded_segments (0x1834c : word) = Some W_1834c.
Proof. vm_refl. Qed.
Lemma D_1834c : decode_any W_1834c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18350 : bv 32 := 0x01213823.
Lemma F_18350 : fetch_word Ubsan.M.loaded_segments (0x18350 : word) = Some W_18350.
Proof. vm_refl. Qed.
Lemma D_18350 : decode_any W_18350 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18354 : bv 32 := 0x01313423.
Lemma F_18354 : fetch_word Ubsan.M.loaded_segments (0x18354 : word) = Some W_18354.
Proof. vm_refl. Qed.
Lemma D_18354 : decode_any W_18354 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18358 : bv 32 := 0x08050c63.
Lemma F_18358 : fetch_word Ubsan.M.loaded_segments (0x18358 : word) = Some W_18358.
Proof. vm_refl. Qed.
Lemma D_18358 : decode_any W_18358 = Some (Branch BC_EQ 10 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_1835c : bv 32 := 0x00757593.
Lemma F_1835c : fetch_word Ubsan.M.loaded_segments (0x1835c : word) = Some W_1835c.
Proof. vm_refl. Qed.
Lemma D_1835c : decode_any W_1835c = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_18360 : bv 32 := 0x0e059663.
Lemma F_18360 : fetch_word Ubsan.M.loaded_segments (0x18360 : word) = Some W_18360.
Proof. vm_refl. Qed.
Lemma D_18360 : decode_any W_18360 = Some (Branch BC_NE 11 0 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_18364 : bv 32 := 0x00053403.
Lemma F_18364 : fetch_word Ubsan.M.loaded_segments (0x18364 : word) = Some W_18364.
Proof. vm_refl. Qed.
Lemma D_18364 : decode_any W_18364 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18368 : bv 32 := 0x0c040463.
Lemma F_18368 : fetch_word Ubsan.M.loaded_segments (0x18368 : word) = Some W_18368.
Proof. vm_refl. Qed.
Lemma D_18368 : decode_any W_18368 = Some (Branch BC_EQ 8 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_1836c : bv 32 := 0x00747593.
Lemma F_1836c : fetch_word Ubsan.M.loaded_segments (0x1836c : word) = Some W_1836c.
Proof. vm_refl. Qed.
Lemma D_1836c : decode_any W_1836c = Some (OpImm ALU_AND 11 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_18370 : bv 32 := 0x0c059e63.
Lemma F_18370 : fetch_word Ubsan.M.loaded_segments (0x18370 : word) = Some W_18370.
Proof. vm_refl. Qed.
Lemma D_18370 : decode_any W_18370 = Some (Branch BC_NE 11 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_18374 : bv 32 := 0x00840593.
Lemma F_18374 : fetch_word Ubsan.M.loaded_segments (0x18374 : word) = Some W_18374.
Proof. vm_refl. Qed.
Lemma D_18374 : decode_any W_18374 = Some (OpImm ALU_ADD 11 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18378 : bv 32 := 0xfff00613.
Lemma F_18378 : fetch_word Ubsan.M.loaded_segments (0x18378 : word) = Some W_18378.
Proof. vm_refl. Qed.
Lemma D_18378 : decode_any W_18378 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1837c : bv 32 := 0x06c5a5af.
Lemma F_1837c : fetch_word Ubsan.M.loaded_segments (0x1837c : word) = Some W_1837c.
Proof. vm_refl. Qed.
Lemma D_1837c : decode_any W_1837c = Some (Amo AMO_ADD AW true true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18380 : bv 32 := 0x00100613.
Lemma F_18380 : fetch_word Ubsan.M.loaded_segments (0x18380 : word) = Some W_18380.
Proof. vm_refl. Qed.
Lemma D_18380 : decode_any W_18380 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18384 : bv 32 := 0x06c59263.
Lemma F_18384 : fetch_word Ubsan.M.loaded_segments (0x18384 : word) = Some W_18384.
Proof. vm_refl. Qed.
Lemma D_18384 : decode_any W_18384 = Some (Branch BC_NE 11 12 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_18388 : bv 32 := 0x00050493.
Lemma F_18388 : fetch_word Ubsan.M.loaded_segments (0x18388 : word) = Some W_18388.
Proof. vm_refl. Qed.
Lemma D_18388 : decode_any W_18388 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1838c : bv 32 := 0x00042503.
Lemma F_1838c : fetch_word Ubsan.M.loaded_segments (0x1838c : word) = Some W_1838c.
Proof. vm_refl. Qed.
Lemma D_1838c : decode_any W_1838c = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18390 : bv 32 := 0x02a05e63.
Lemma F_18390 : fetch_word Ubsan.M.loaded_segments (0x18390 : word) = Some W_18390.
Proof. vm_refl. Qed.
Lemma D_18390 : decode_any W_18390 = Some (Branch BC_GE 0 10 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_18394 : bv 32 := 0x00000913.
Lemma F_18394 : fetch_word Ubsan.M.loaded_segments (0x18394 : word) = Some W_18394.
Proof. vm_refl. Qed.
Lemma D_18394 : decode_any W_18394 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18398 : bv 32 := 0x00000993.
Lemma F_18398 : fetch_word Ubsan.M.loaded_segments (0x18398 : word) = Some W_18398.
Proof. vm_refl. Qed.
Lemma D_18398 : decode_any W_18398 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1839c : bv 32 := 0x01043583.
Lemma F_1839c : fetch_word Ubsan.M.loaded_segments (0x1839c : word) = Some W_1839c.
Proof. vm_refl. Qed.
Lemma D_1839c : decode_any W_1839c = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_183a0 : bv 32 := 0x00b90533.
Lemma F_183a0 : fetch_word Ubsan.M.loaded_segments (0x183a0 : word) = Some W_183a0.
Proof. vm_refl. Qed.
Lemma D_183a0 : decode_any W_183a0 = Some (Op ALU_ADD 10 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_183a4 : bv 32 := 0x0ab56463.
Lemma F_183a4 : fetch_word Ubsan.M.loaded_segments (0x183a4 : word) = Some W_183a4.
Proof. vm_refl. Qed.
Lemma D_183a4 : decode_any W_183a4 = Some (Branch BC_LTU 10 11 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_183a8 : bv 32 := 0x00b035b3.
Lemma F_183a8 : fetch_word Ubsan.M.loaded_segments (0x183a8 : word) = Some W_183a8.
Proof. vm_refl. Qed.
Lemma D_183a8 : decode_any W_183a8 = Some (Op ALU_SLTU 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_183ac : bv 32 := 0x00153613.
Lemma F_183ac : fetch_word Ubsan.M.loaded_segments (0x183ac : word) = Some W_183ac.
Proof. vm_refl. Qed.
Lemma D_183ac : decode_any W_183ac = Some (OpImm ALU_SLTU 12 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_183b0 : bv 32 := 0x00c5c5b3.
Lemma F_183b0 : fetch_word Ubsan.M.loaded_segments (0x183b0 : word) = Some W_183b0.
Proof. vm_refl. Qed.
Lemma D_183b0 : decode_any W_183b0 = Some (Op ALU_XOR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_183b4 : bv 32 := 0x08058c63.
Lemma F_183b4 : fetch_word Ubsan.M.loaded_segments (0x183b4 : word) = Some W_183b4.
Proof. vm_refl. Qed.
Lemma D_183b4 : decode_any W_183b4 = Some (Branch BC_EQ 11 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_183b8 : bv 32 := 0x474010ef.
Lemma F_183b8 : fetch_word Ubsan.M.loaded_segments (0x183b8 : word) = Some W_183b8.
Proof. vm_refl. Qed.
Lemma D_183b8 : decode_any W_183b8 = Some (Jal 1 5236, 4%Z).
Proof. vm_refl. Qed.

Definition W_183bc : bv 32 := 0x00042503.
Lemma F_183bc : fetch_word Ubsan.M.loaded_segments (0x183bc : word) = Some W_183bc.
Proof. vm_refl. Qed.
Lemma D_183bc : decode_any W_183bc = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_183c0 : bv 32 := 0x00198993.
Lemma F_183c0 : fetch_word Ubsan.M.loaded_segments (0x183c0 : word) = Some W_183c0.
Proof. vm_refl. Qed.
Lemma D_183c0 : decode_any W_183c0 = Some (OpImm ALU_ADD 19 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_183c4 : bv 32 := 0x00890913.
Lemma F_183c4 : fetch_word Ubsan.M.loaded_segments (0x183c4 : word) = Some W_183c4.
Proof. vm_refl. Qed.
Lemma D_183c4 : decode_any W_183c4 = Some (OpImm ALU_ADD 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_183c8 : bv 32 := 0xfca9cae3.
Lemma F_183c8 : fetch_word Ubsan.M.loaded_segments (0x183c8 : word) = Some W_183c8.
Proof. vm_refl. Qed.
Lemma D_183c8 : decode_any W_183c8 = Some (Branch BC_LT 19 10 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_183cc : bv 32 := 0x01043503.
Lemma F_183cc : fetch_word Ubsan.M.loaded_segments (0x183cc : word) = Some W_183cc.
Proof. vm_refl. Qed.
Lemma D_183cc : decode_any W_183cc = Some (Load SZ8 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_183d0 : bv 32 := 0x661230ef.
Lemma F_183d0 : fetch_word Ubsan.M.loaded_segments (0x183d0 : word) = Some W_183d0.
Proof. vm_refl. Qed.
Lemma D_183d0 : decode_any W_183d0 = Some (Jal 1 147040, 4%Z).
Proof. vm_refl. Qed.

Definition W_183d4 : bv 32 := 0x01840513.
Lemma F_183d4 : fetch_word Ubsan.M.loaded_segments (0x183d4 : word) = Some W_183d4.
Proof. vm_refl. Qed.
Lemma D_183d4 : decode_any W_183d4 = Some (OpImm ALU_ADD 10 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_183d8 : bv 32 := 0x3c9000ef.
Lemma F_183d8 : fetch_word Ubsan.M.loaded_segments (0x183d8 : word) = Some W_183d8.
Proof. vm_refl. Qed.
Lemma D_183d8 : decode_any W_183d8 = Some (Jal 1 3016, 4%Z).
Proof. vm_refl. Qed.

Definition W_183dc : bv 32 := 0x00040513.
Lemma F_183dc : fetch_word Ubsan.M.loaded_segments (0x183dc : word) = Some W_183dc.
Proof. vm_refl. Qed.
Lemma D_183dc : decode_any W_183dc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_183e0 : bv 32 := 0x651230ef.
Lemma F_183e0 : fetch_word Ubsan.M.loaded_segments (0x183e0 : word) = Some W_183e0.
Proof. vm_refl. Qed.
Lemma D_183e0 : decode_any W_183e0 = Some (Jal 1 147024, 4%Z).
Proof. vm_refl. Qed.

Definition W_183e4 : bv 32 := 0x00048513.
Lemma F_183e4 : fetch_word Ubsan.M.loaded_segments (0x183e4 : word) = Some W_183e4.
Proof. vm_refl. Qed.
Lemma D_183e4 : decode_any W_183e4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_183e8 : bv 32 := 0x00053023.
Lemma F_183e8 : fetch_word Ubsan.M.loaded_segments (0x183e8 : word) = Some W_183e8.
Proof. vm_refl. Qed.
Lemma D_183e8 : decode_any W_183e8 = Some (Store SZ8 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_183ec : bv 32 := 0x0440006f.
Lemma F_183ec : fetch_word Ubsan.M.loaded_segments (0x183ec : word) = Some W_183ec.
Proof. vm_refl. Qed.
Lemma D_183ec : decode_any W_183ec = Some (Jal 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_183f0 : bv 32 := 0x0002d517.
Lemma F_183f0 : fetch_word Ubsan.M.loaded_segments (0x183f0 : word) = Some W_183f0.
Proof. vm_refl. Qed.
Lemma D_183f0 : decode_any W_183f0 = Some (Auipc 10 45, 4%Z).
Proof. vm_refl. Qed.

Definition W_183f4 : bv 32 := 0xaa853503.
Lemma F_183f4 : fetch_word Ubsan.M.loaded_segments (0x183f4 : word) = Some W_183f4.
Proof. vm_refl. Qed.
Lemma D_183f4 : decode_any W_183f4 = Some (Load SZ8 true 10 10 2728, 4%Z).
Proof. vm_refl. Qed.

Definition W_183f8 : bv 32 := 0x00052503.
Lemma F_183f8 : fetch_word Ubsan.M.loaded_segments (0x183f8 : word) = Some W_183f8.
Proof. vm_refl. Qed.
Lemma D_183f8 : decode_any W_183f8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_183fc : bv 32 := 0x00400593.
Lemma F_183fc : fetch_word Ubsan.M.loaded_segments (0x183fc : word) = Some W_183fc.
Proof. vm_refl. Qed.
Lemma D_183fc : decode_any W_183fc = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_18400 : bv 32 := 0x02a5c863.
Lemma F_18400 : fetch_word Ubsan.M.loaded_segments (0x18400 : word) = Some W_18400.
Proof. vm_refl. Qed.
Lemma D_18400 : decode_any W_18400 = Some (Branch BC_LT 11 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_18404 : bv 32 := 0xffff8517.
Lemma F_18404 : fetch_word Ubsan.M.loaded_segments (0x18404 : word) = Some W_18404.
Proof. vm_refl. Qed.
Lemma D_18404 : decode_any W_18404 = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_18408 : bv 32 := 0xffffa597.
Lemma F_18408 : fetch_word Ubsan.M.loaded_segments (0x18408 : word) = Some W_18408.
Proof. vm_refl. Qed.
Lemma D_18408 : decode_any W_18408 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

Definition W_1840c : bv 32 := 0x49050513.
Lemma F_1840c : fetch_word Ubsan.M.loaded_segments (0x1840c : word) = Some W_1840c.
Proof. vm_refl. Qed.
Lemma D_1840c : decode_any W_1840c = Some (OpImm ALU_ADD 10 10 1168, 4%Z).
Proof. vm_refl. Qed.

Definition W_18410 : bv 32 := 0xa6f58593.
Lemma F_18410 : fetch_word Ubsan.M.loaded_segments (0x18410 : word) = Some W_18410.
Proof. vm_refl. Qed.
Lemma D_18410 : decode_any W_18410 = Some (OpImm ALU_ADD 11 11 2671, 4%Z).
Proof. vm_refl. Qed.

Definition W_18414 : bv 32 := 0x02813083.
Lemma F_18414 : fetch_word Ubsan.M.loaded_segments (0x18414 : word) = Some W_18414.
Proof. vm_refl. Qed.
Lemma D_18414 : decode_any W_18414 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18418 : bv 32 := 0x02013403.
Lemma F_18418 : fetch_word Ubsan.M.loaded_segments (0x18418 : word) = Some W_18418.
Proof. vm_refl. Qed.
Lemma D_18418 : decode_any W_18418 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1841c : bv 32 := 0x01813483.
Lemma F_1841c : fetch_word Ubsan.M.loaded_segments (0x1841c : word) = Some W_1841c.
Proof. vm_refl. Qed.
Lemma D_1841c : decode_any W_1841c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18420 : bv 32 := 0x01013903.
Lemma F_18420 : fetch_word Ubsan.M.loaded_segments (0x18420 : word) = Some W_18420.
Proof. vm_refl. Qed.
Lemma D_18420 : decode_any W_18420 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18424 : bv 32 := 0x00813983.
Lemma F_18424 : fetch_word Ubsan.M.loaded_segments (0x18424 : word) = Some W_18424.
Proof. vm_refl. Qed.
Lemma D_18424 : decode_any W_18424 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18428 : bv 32 := 0x03010113.
Lemma F_18428 : fetch_word Ubsan.M.loaded_segments (0x18428 : word) = Some W_18428.
Proof. vm_refl. Qed.
Lemma D_18428 : decode_any W_18428 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1842c : bv 32 := 0x9fdff06f.
Lemma F_1842c : fetch_word Ubsan.M.loaded_segments (0x1842c : word) = Some W_1842c.
Proof. vm_refl. Qed.
Lemma D_1842c : decode_any W_1842c = Some (Jal 0 2095612, 4%Z).
Proof. vm_refl. Qed.

Definition W_18430 : bv 32 := 0x02813083.
Lemma F_18430 : fetch_word Ubsan.M.loaded_segments (0x18430 : word) = Some W_18430.
Proof. vm_refl. Qed.
Lemma D_18430 : decode_any W_18430 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18434 : bv 32 := 0x02013403.
Lemma F_18434 : fetch_word Ubsan.M.loaded_segments (0x18434 : word) = Some W_18434.
Proof. vm_refl. Qed.
Lemma D_18434 : decode_any W_18434 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18438 : bv 32 := 0x01813483.
Lemma F_18438 : fetch_word Ubsan.M.loaded_segments (0x18438 : word) = Some W_18438.
Proof. vm_refl. Qed.
Lemma D_18438 : decode_any W_18438 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1843c : bv 32 := 0x01013903.
Lemma F_1843c : fetch_word Ubsan.M.loaded_segments (0x1843c : word) = Some W_1843c.
Proof. vm_refl. Qed.
Lemma D_1843c : decode_any W_1843c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18440 : bv 32 := 0x00813983.
Lemma F_18440 : fetch_word Ubsan.M.loaded_segments (0x18440 : word) = Some W_18440.
Proof. vm_refl. Qed.
Lemma D_18440 : decode_any W_18440 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18444 : bv 32 := 0x03010113.
Lemma F_18444 : fetch_word Ubsan.M.loaded_segments (0x18444 : word) = Some W_18444.
Proof. vm_refl. Qed.
Lemma D_18444 : decode_any W_18444 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_18448 : bv 32 := 0x00008067.
Lemma F_18448 : fetch_word Ubsan.M.loaded_segments (0x18448 : word) = Some W_18448.
Proof. vm_refl. Qed.
Lemma D_18448 : decode_any W_18448 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1844c : bv 32 := 0xc0001073.
Lemma F_1844c : fetch_word Ubsan.M.loaded_segments (0x1844c : word) = Some W_1844c.
Proof. vm_refl. Qed.
Lemma D_1844c : decode_any W_1844c = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
