(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
Unset Nia Cache.
Unset Lia Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_183b0 : bv 32 := 0xffc7c383.
Lemma F_183b0 : fetch_word Plain.M.loaded_segments (0x183b0 : word) = Some W_183b0.
Proof. vm_refl. Qed.
Lemma D_183b0 : decode_any W_183b0 = Some (Load SZ1 false 7 15 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_183b4 : bv 32 := 0x0042d313.
Lemma F_183b4 : fetch_word Plain.M.loaded_segments (0x183b4 : word) = Some W_183b4.
Proof. vm_refl. Qed.
Lemma D_183b4 : decode_any W_183b4 = Some (ShiftImm ALU_SRL 6 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_183b8 : bv 32 := 0x0ff6f893.
Lemma F_183b8 : fetch_word Plain.M.loaded_segments (0x183b8 : word) = Some W_183b8.
Proof. vm_refl. Qed.
Lemma D_183b8 : decode_any W_183b8 = Some (OpImm ALU_AND 17 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_183bc : bv 32 := 0x00038463.
Lemma F_183bc : fetch_word Plain.M.loaded_segments (0x183bc : word) = Some W_183bc.
Proof. vm_refl. Qed.
Lemma D_183bc : decode_any W_183bc = Some (Branch BC_EQ 7 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_183c4 : bv 32 := 0x03137e63.
Lemma F_183c4 : fetch_word Plain.M.loaded_segments (0x183c4 : word) = Some W_183c4.
Proof. vm_refl. Qed.
Lemma D_183c4 : decode_any W_183c4 = Some (Branch BC_GEU 6 17 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_183c8 : bv 32 := 0x0052d693.
Lemma F_183c8 : fetch_word Plain.M.loaded_segments (0x183c8 : word) = Some W_183c8.
Proof. vm_refl. Qed.
Lemma D_183c8 : decode_any W_183c8 = Some (ShiftImm ALU_SRL 13 5 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_183cc : bv 32 := 0x00d366b3.
Lemma F_183cc : fetch_word Plain.M.loaded_segments (0x183cc : word) = Some W_183cc.
Proof. vm_refl. Qed.
Lemma D_183cc : decode_any W_183cc = Some (Op ALU_OR 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_183d0 : bv 32 := 0x0026d293.
Lemma F_183d0 : fetch_word Plain.M.loaded_segments (0x183d0 : word) = Some W_183d0.
Proof. vm_refl. Qed.
Lemma D_183d0 : decode_any W_183d0 = Some (ShiftImm ALU_SRL 5 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_183d4 : bv 32 := 0x00d2e6b3.
Lemma F_183d4 : fetch_word Plain.M.loaded_segments (0x183d4 : word) = Some W_183d4.
Proof. vm_refl. Qed.
Lemma D_183d4 : decode_any W_183d4 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_183d8 : bv 32 := 0x0046d293.
Lemma F_183d8 : fetch_word Plain.M.loaded_segments (0x183d8 : word) = Some W_183d8.
Proof. vm_refl. Qed.
Lemma D_183d8 : decode_any W_183d8 = Some (ShiftImm ALU_SRL 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_183dc : bv 32 := 0x00d2e6b3.
Lemma F_183dc : fetch_word Plain.M.loaded_segments (0x183dc : word) = Some W_183dc.
Proof. vm_refl. Qed.
Lemma D_183dc : decode_any W_183dc = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_183e0 : bv 32 := 0x00d8f6b3.
Lemma F_183e0 : fetch_word Plain.M.loaded_segments (0x183e0 : word) = Some W_183e0.
Proof. vm_refl. Qed.
Lemma D_183e0 : decode_any W_183e0 = Some (Op ALU_AND 13 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_183e4 : bv 32 := 0x00d338b3.
Lemma F_183e4 : fetch_word Plain.M.loaded_segments (0x183e4 : word) = Some W_183e4.
Proof. vm_refl. Qed.
Lemma D_183e4 : decode_any W_183e4 = Some (Op ALU_SLTU 17 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_183e8 : bv 32 := 0xfff34293.
Lemma F_183e8 : fetch_word Plain.M.loaded_segments (0x183e8 : word) = Some W_183e8.
Proof. vm_refl. Qed.
Lemma D_183e8 : decode_any W_183e8 = Some (OpImm ALU_XOR 5 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_183ec : bv 32 := 0x411008bb.
Lemma F_183ec : fetch_word Plain.M.loaded_segments (0x183ec : word) = Some W_183ec.
Proof. vm_refl. Qed.
Lemma D_183ec : decode_any W_183ec = Some (Op32 ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_183f0 : bv 32 := 0x0058f8b3.
Lemma F_183f0 : fetch_word Plain.M.loaded_segments (0x183f0 : word) = Some W_183f0.
Proof. vm_refl. Qed.
Lemma D_183f0 : decode_any W_183f0 = Some (Op ALU_AND 17 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_183f4 : bv 32 := 0x00d888bb.
Lemma F_183f4 : fetch_word Plain.M.loaded_segments (0x183f4 : word) = Some W_183f4.
Proof. vm_refl. Qed.
Lemma D_183f4 : decode_any W_183f4 = Some (Op32 ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_183f8 : bv 32 := 0x01137463.
Lemma F_183f8 : fetch_word Plain.M.loaded_segments (0x183f8 : word) = Some W_183f8.
Proof. vm_refl. Qed.
Lemma D_183f8 : decode_any W_183f8 = Some (Branch BC_GEU 6 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18400 : bv 32 := 0x00078693.
Lemma F_18400 : fetch_word Plain.M.loaded_segments (0x18400 : word) = Some W_18400.
Proof. vm_refl. Qed.
Lemma D_18400 : decode_any W_18400 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18404 : bv 32 := 0x02088063.
Lemma F_18404 : fetch_word Plain.M.loaded_segments (0x18404 : word) = Some W_18404.
Proof. vm_refl. Qed.
Lemma D_18404 : decode_any W_18404 = Some (Branch BC_EQ 17 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18408 : bv 32 := 0xfe000813.
Lemma F_18408 : fetch_word Plain.M.loaded_segments (0x18408 : word) = Some W_18408.
Proof. vm_refl. Qed.
Lemma D_18408 : decode_any W_18408 = Some (OpImm ALU_ADD 16 0 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_1840c : bv 32 := 0x0048969b.
Lemma F_1840c : fetch_word Plain.M.loaded_segments (0x1840c : word) = Some W_1840c.
Proof. vm_refl. Qed.
Lemma D_1840c : decode_any W_1840c = Some (ShiftImm32 ALU_SLL 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_18410 : bv 32 := 0x00d786b3.
Lemma F_18410 : fetch_word Plain.M.loaded_segments (0x18410 : word) = Some W_18410.
Proof. vm_refl. Qed.
Lemma D_18410 : decode_any W_18410 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18414 : bv 32 := 0xff078ea3.
Lemma F_18414 : fetch_word Plain.M.loaded_segments (0x18414 : word) = Some W_18414.
Proof. vm_refl. Qed.
Lemma D_18414 : decode_any W_18414 = Some (Store SZ1 15 16 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_18418 : bv 32 := 0xff179f23.
Lemma F_18418 : fetch_word Plain.M.loaded_segments (0x18418 : word) = Some W_18418.
Proof. vm_refl. Qed.
Lemma D_18418 : decode_any W_18418 = Some (Store SZ2 15 17 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_1841c : bv 32 := 0xfe068e23.
Lemma F_1841c : fetch_word Plain.M.loaded_segments (0x1841c : word) = Some W_1841c.
Proof. vm_refl. Qed.
Lemma D_1841c : decode_any W_1841c = Some (Store SZ1 13 0 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_18420 : bv 32 := 0x01053803.
Lemma F_18420 : fetch_word Plain.M.loaded_segments (0x18420 : word) = Some W_18420.
Proof. vm_refl. Qed.
Lemma D_18420 : decode_any W_18420 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18424 : bv 32 := 0x00e78733.
Lemma F_18424 : fetch_word Plain.M.loaded_segments (0x18424 : word) = Some W_18424.
Proof. vm_refl. Qed.
Lemma D_18424 : decode_any W_18424 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_18428 : bv 32 := 0x410687bb.
Lemma F_18428 : fetch_word Plain.M.loaded_segments (0x18428 : word) = Some W_18428.
Proof. vm_refl. Qed.
Lemma D_18428 : decode_any W_18428 = Some (Op32 ALU_SUB 15 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1842c : bv 32 := 0x00d60633.
Lemma F_1842c : fetch_word Plain.M.loaded_segments (0x1842c : word) = Some W_1842c.
Proof. vm_refl. Qed.
Lemma D_1842c : decode_any W_1842c = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18430 : bv 32 := 0xffc70513.
Lemma F_18430 : fetch_word Plain.M.loaded_segments (0x18430 : word) = Some W_18430.
Proof. vm_refl. Qed.
Lemma D_18430 : decode_any W_18430 = Some (OpImm ALU_ADD 10 14 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_18434 : bv 32 := 0xff078793.
Lemma F_18434 : fetch_word Plain.M.loaded_segments (0x18434 : word) = Some W_18434.
Proof. vm_refl. Qed.
Lemma D_18434 : decode_any W_18434 = Some (OpImm ALU_ADD 15 15 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_18438 : bv 32 := 0x0047d793.
Lemma F_18438 : fetch_word Plain.M.loaded_segments (0x18438 : word) = Some W_18438.
Proof. vm_refl. Qed.
Lemma D_18438 : decode_any W_18438 = Some (ShiftImm ALU_SRL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1843c : bv 32 := 0x40c5083b.
Lemma F_1843c : fetch_word Plain.M.loaded_segments (0x1843c : word) = Some W_1843c.
Proof. vm_refl. Qed.
Lemma D_1843c : decode_any W_1843c = Some (Op32 ALU_SUB 16 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18440 : bv 32 := 0xfeb68ea3.
Lemma F_18440 : fetch_word Plain.M.loaded_segments (0x18440 : word) = Some W_18440.
Proof. vm_refl. Qed.
Lemma D_18440 : decode_any W_18440 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_18444 : bv 32 := 0xfef69f23.
Lemma F_18444 : fetch_word Plain.M.loaded_segments (0x18444 : word) = Some W_18444.
Proof. vm_refl. Qed.
Lemma D_18444 : decode_any W_18444 = Some (Store SZ2 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_18448 : bv 32 := 0x02080463.
Lemma F_18448 : fetch_word Plain.M.loaded_segments (0x18448 : word) = Some W_18448.
Proof. vm_refl. Qed.
Lemma D_18448 : decode_any W_18448 = Some (Branch BC_EQ 16 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1844c : bv 32 := 0x40c505bb.
Lemma F_1844c : fetch_word Plain.M.loaded_segments (0x1844c : word) = Some W_1844c.
Proof. vm_refl. Qed.
Lemma D_1844c : decode_any W_1844c = Some (Op32 ALU_SUB 11 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18450 : bv 32 := 0x40b0063b.
Lemma F_18450 : fetch_word Plain.M.loaded_segments (0x18450 : word) = Some W_18450.
Proof. vm_refl. Qed.
Lemma D_18450 : decode_any W_18450 = Some (Op32 ALU_SUB 12 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_18454 : bv 32 := 0x00c50633.
Lemma F_18454 : fetch_word Plain.M.loaded_segments (0x18454 : word) = Some W_18454.
Proof. vm_refl. Qed.
Lemma D_18454 : decode_any W_18454 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18458 : bv 32 := 0x00500513.
Lemma F_18458 : fetch_word Plain.M.loaded_segments (0x18458 : word) = Some W_18458.
Proof. vm_refl. Qed.
Lemma D_18458 : decode_any W_18458 = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1845c : bv 32 := 0x00060023.
Lemma F_1845c : fetch_word Plain.M.loaded_segments (0x1845c : word) = Some W_1845c.
Proof. vm_refl. Qed.
Lemma D_1845c : decode_any W_1845c = Some (Store SZ1 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18460 : bv 32 := 0x00a5cc63.
Lemma F_18460 : fetch_word Plain.M.loaded_segments (0x18460 : word) = Some W_18460.
Proof. vm_refl. Qed.
Lemma D_18460 : decode_any W_18460 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18464 : bv 32 := 0xfe070ba3.
Lemma F_18464 : fetch_word Plain.M.loaded_segments (0x18464 : word) = Some W_18464.
Proof. vm_refl. Qed.
Lemma D_18464 : decode_any W_18464 = Some (Store SZ1 14 0 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_18468 : bv 32 := 0xfeb72c23.
Lemma F_18468 : fetch_word Plain.M.loaded_segments (0x18468 : word) = Some W_18468.
Proof. vm_refl. Qed.
Lemma D_18468 : decode_any W_18468 = Some (Store SZ4 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_1846c : bv 32 := 0x0100006f.
Lemma F_1846c : fetch_word Plain.M.loaded_segments (0x1846c : word) = Some W_1846c.
Proof. vm_refl. Qed.
Lemma D_1846c : decode_any W_1846c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18470 : bv 32 := 0x00000513.
Lemma F_18470 : fetch_word Plain.M.loaded_segments (0x18470 : word) = Some W_18470.
Proof. vm_refl. Qed.
Lemma D_18470 : decode_any W_18470 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18474 : bv 32 := 0x0080006f.
Lemma F_18474 : fetch_word Plain.M.loaded_segments (0x18474 : word) = Some W_18474.
Proof. vm_refl. Qed.
Lemma D_18474 : decode_any W_18474 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18478 : bv 32 := 0x00058513.
Lemma F_18478 : fetch_word Plain.M.loaded_segments (0x18478 : word) = Some W_18478.
Proof. vm_refl. Qed.
Lemma D_18478 : decode_any W_18478 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1847c : bv 32 := 0xffd6c583.
Lemma F_1847c : fetch_word Plain.M.loaded_segments (0x1847c : word) = Some W_1847c.
Proof. vm_refl. Qed.
Lemma D_1847c : decode_any W_1847c = Some (Load SZ1 false 11 13 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_18480 : bv 32 := 0x01f5f593.
Lemma F_18480 : fetch_word Plain.M.loaded_segments (0x18480 : word) = Some W_18480.
Proof. vm_refl. Qed.
Lemma D_18480 : decode_any W_18480 = Some (OpImm ALU_AND 11 11 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_18484 : bv 32 := 0x00551513.
Lemma F_18484 : fetch_word Plain.M.loaded_segments (0x18484 : word) = Some W_18484.
Proof. vm_refl. Qed.
Lemma D_18484 : decode_any W_18484 = Some (ShiftImm ALU_SLL 10 10 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18488 : bv 32 := 0x00b56533.
Lemma F_18488 : fetch_word Plain.M.loaded_segments (0x18488 : word) = Some W_18488.
Proof. vm_refl. Qed.
Lemma D_18488 : decode_any W_18488 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1848c : bv 32 := 0xfea68ea3.
Lemma F_1848c : fetch_word Plain.M.loaded_segments (0x1848c : word) = Some W_1848c.
Proof. vm_refl. Qed.
Lemma D_1848c : decode_any W_1848c = Some (Store SZ1 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_18490 : bv 32 := 0x00068513.
Lemma F_18490 : fetch_word Plain.M.loaded_segments (0x18490 : word) = Some W_18490.
Proof. vm_refl. Qed.
Lemma D_18490 : decode_any W_18490 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18494 : bv 32 := 0x00008067.
Lemma F_18494 : fetch_word Plain.M.loaded_segments (0x18494 : word) = Some W_18494.
Proof. vm_refl. Qed.
Lemma D_18494 : decode_any W_18494 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dd8 : bv 32 := 0xff010113.
Lemma F_18dd8 : fetch_word Plain.M.loaded_segments (0x18dd8 : word) = Some W_18dd8.
Proof. vm_refl. Qed.
Lemma D_18dd8 : decode_any W_18dd8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ddc : bv 32 := 0x00113423.
Lemma F_18ddc : fetch_word Plain.M.loaded_segments (0x18ddc : word) = Some W_18ddc.
Proof. vm_refl. Qed.
Lemma D_18ddc : decode_any W_18ddc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18de0 : bv 32 := 0x00813023.
Lemma F_18de0 : fetch_word Plain.M.loaded_segments (0x18de0 : word) = Some W_18de0.
Proof. vm_refl. Qed.
Lemma D_18de0 : decode_any W_18de0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18de4 : bv 32 := 0x198000ef.
Lemma F_18de4 : fetch_word Plain.M.loaded_segments (0x18de4 : word) = Some W_18de4.
Proof. vm_refl. Qed.
Lemma D_18de4 : decode_any W_18de4 = Some (Jal 1 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_18de8 : bv 32 := 0x00053403.
Lemma F_18de8 : fetch_word Plain.M.loaded_segments (0x18de8 : word) = Some W_18de8.
Proof. vm_refl. Qed.
Lemma D_18de8 : decode_any W_18de8 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dec : bv 32 := 0x12041663.
Lemma F_18dec : fetch_word Plain.M.loaded_segments (0x18dec : word) = Some W_18dec.
Proof. vm_refl. Qed.
Lemma D_18dec : decode_any W_18dec = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_18df0 : bv 32 := 0x00038517.
Lemma F_18df0 : fetch_word Plain.M.loaded_segments (0x18df0 : word) = Some W_18df0.
Proof. vm_refl. Qed.
Lemma D_18df0 : decode_any W_18df0 = Some (Auipc 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18df4 : bv 32 := 0x2a853403.
Lemma F_18df4 : fetch_word Plain.M.loaded_segments (0x18df4 : word) = Some W_18df4.
Proof. vm_refl. Qed.
Lemma D_18df4 : decode_any W_18df4 = Some (Load SZ8 true 8 10 680, 4%Z).
Proof. vm_refl. Qed.

Definition W_18df8 : bv 32 := 0x04040a63.
Lemma F_18df8 : fetch_word Plain.M.loaded_segments (0x18df8 : word) = Some W_18df8.
Proof. vm_refl. Qed.
Lemma D_18df8 : decode_any W_18df8 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e4c : bv 32 := 0x00008517.
Lemma F_18e4c : fetch_word Plain.M.loaded_segments (0x18e4c : word) = Some W_18e4c.
Proof. vm_refl. Qed.
Lemma D_18e4c : decode_any W_18e4c = Some (Auipc 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e50 : bv 32 := 0xa2c53403.
Lemma F_18e50 : fetch_word Plain.M.loaded_segments (0x18e50 : word) = Some W_18e50.
Proof. vm_refl. Qed.
Lemma D_18e50 : decode_any W_18e50 = Some (Load SZ8 true 8 10 2604, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e54 : bv 32 := 0x04040a63.
Lemma F_18e54 : fetch_word Plain.M.loaded_segments (0x18e54 : word) = Some W_18e54.
Proof. vm_refl. Qed.
Lemma D_18e54 : decode_any W_18e54 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e58 : bv 32 := 0x08c42503.
Lemma F_18e58 : fetch_word Plain.M.loaded_segments (0x18e58 : word) = Some W_18e58.
Proof. vm_refl. Qed.
Lemma D_18e58 : decode_any W_18e58 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e5c : bv 32 := 0x00054663.
Lemma F_18e5c : fetch_word Plain.M.loaded_segments (0x18e5c : word) = Some W_18e5c.
Proof. vm_refl. Qed.
Lemma D_18e5c : decode_any W_18e5c = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e68 : bv 32 := 0x02843503.
Lemma F_18e68 : fetch_word Plain.M.loaded_segments (0x18e68 : word) = Some W_18e68.
Proof. vm_refl. Qed.
Lemma D_18e68 : decode_any W_18e68 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e6c : bv 32 := 0x03843583.
Lemma F_18e6c : fetch_word Plain.M.loaded_segments (0x18e6c : word) = Some W_18e6c.
Proof. vm_refl. Qed.
Lemma D_18e6c : decode_any W_18e6c = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e70 : bv 32 := 0x00b50c63.
Lemma F_18e70 : fetch_word Plain.M.loaded_segments (0x18e70 : word) = Some W_18e70.
Proof. vm_refl. Qed.
Lemma D_18e70 : decode_any W_18e70 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e74 : bv 32 := 0x04843683.
Lemma F_18e74 : fetch_word Plain.M.loaded_segments (0x18e74 : word) = Some W_18e74.
Proof. vm_refl. Qed.
Lemma D_18e74 : decode_any W_18e74 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e78 : bv 32 := 0x00040513.
Lemma F_18e78 : fetch_word Plain.M.loaded_segments (0x18e78 : word) = Some W_18e78.
Proof. vm_refl. Qed.
Lemma D_18e78 : decode_any W_18e78 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e7c : bv 32 := 0x00000593.
Lemma F_18e7c : fetch_word Plain.M.loaded_segments (0x18e7c : word) = Some W_18e7c.
Proof. vm_refl. Qed.
Lemma D_18e7c : decode_any W_18e7c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e80 : bv 32 := 0x00000613.
Lemma F_18e80 : fetch_word Plain.M.loaded_segments (0x18e80 : word) = Some W_18e80.
Proof. vm_refl. Qed.
Lemma D_18e80 : decode_any W_18e80 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e84 : bv 32 := 0x000680e7.
Lemma F_18e84 : fetch_word Plain.M.loaded_segments (0x18e84 : word) = Some W_18e84.
Proof. vm_refl. Qed.
Lemma D_18e84 : decode_any W_18e84 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e88 : bv 32 := 0x00843503.
Lemma F_18e88 : fetch_word Plain.M.loaded_segments (0x18e88 : word) = Some W_18e88.
Proof. vm_refl. Qed.
Lemma D_18e88 : decode_any W_18e88 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e8c : bv 32 := 0x01043583.
Lemma F_18e8c : fetch_word Plain.M.loaded_segments (0x18e8c : word) = Some W_18e8c.
Proof. vm_refl. Qed.
Lemma D_18e8c : decode_any W_18e8c = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e90 : bv 32 := 0x00b50c63.
Lemma F_18e90 : fetch_word Plain.M.loaded_segments (0x18e90 : word) = Some W_18e90.
Proof. vm_refl. Qed.
Lemma D_18e90 : decode_any W_18e90 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ea8 : bv 32 := 0x00008517.
Lemma F_18ea8 : fetch_word Plain.M.loaded_segments (0x18ea8 : word) = Some W_18ea8.
Proof. vm_refl. Qed.
Lemma D_18ea8 : decode_any W_18ea8 = Some (Auipc 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18eac : bv 32 := 0x8e053403.
Lemma F_18eac : fetch_word Plain.M.loaded_segments (0x18eac : word) = Some W_18eac.
Proof. vm_refl. Qed.
Lemma D_18eac : decode_any W_18eac = Some (Load SZ8 true 8 10 2272, 4%Z).
Proof. vm_refl. Qed.

Definition W_18eb0 : bv 32 := 0x0a040e63.
Lemma F_18eb0 : fetch_word Plain.M.loaded_segments (0x18eb0 : word) = Some W_18eb0.
Proof. vm_refl. Qed.
Lemma D_18eb0 : decode_any W_18eb0 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_18eb4 : bv 32 := 0x08c42503.
Lemma F_18eb4 : fetch_word Plain.M.loaded_segments (0x18eb4 : word) = Some W_18eb4.
Proof. vm_refl. Qed.
Lemma D_18eb4 : decode_any W_18eb4 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_18eb8 : bv 32 := 0x00054663.
Lemma F_18eb8 : fetch_word Plain.M.loaded_segments (0x18eb8 : word) = Some W_18eb8.
Proof. vm_refl. Qed.
Lemma D_18eb8 : decode_any W_18eb8 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ec4 : bv 32 := 0x02843503.
Lemma F_18ec4 : fetch_word Plain.M.loaded_segments (0x18ec4 : word) = Some W_18ec4.
Proof. vm_refl. Qed.
Lemma D_18ec4 : decode_any W_18ec4 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ec8 : bv 32 := 0x03843583.
Lemma F_18ec8 : fetch_word Plain.M.loaded_segments (0x18ec8 : word) = Some W_18ec8.
Proof. vm_refl. Qed.
Lemma D_18ec8 : decode_any W_18ec8 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ecc : bv 32 := 0x00b50c63.
Lemma F_18ecc : fetch_word Plain.M.loaded_segments (0x18ecc : word) = Some W_18ecc.
Proof. vm_refl. Qed.
Lemma D_18ecc : decode_any W_18ecc = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ee4 : bv 32 := 0x00843503.
Lemma F_18ee4 : fetch_word Plain.M.loaded_segments (0x18ee4 : word) = Some W_18ee4.
Proof. vm_refl. Qed.
Lemma D_18ee4 : decode_any W_18ee4 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ee8 : bv 32 := 0x01043583.
Lemma F_18ee8 : fetch_word Plain.M.loaded_segments (0x18ee8 : word) = Some W_18ee8.
Proof. vm_refl. Qed.
Lemma D_18ee8 : decode_any W_18ee8 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18eec : bv 32 := 0x08b50063.
Lemma F_18eec : fetch_word Plain.M.loaded_segments (0x18eec : word) = Some W_18eec.
Proof. vm_refl. Qed.
Lemma D_18eec : decode_any W_18eec = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f6c : bv 32 := 0x00813083.
Lemma F_18f6c : fetch_word Plain.M.loaded_segments (0x18f6c : word) = Some W_18f6c.
Proof. vm_refl. Qed.
Lemma D_18f6c : decode_any W_18f6c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f70 : bv 32 := 0x00013403.
Lemma F_18f70 : fetch_word Plain.M.loaded_segments (0x18f70 : word) = Some W_18f70.
Proof. vm_refl. Qed.
Lemma D_18f70 : decode_any W_18f70 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f74 : bv 32 := 0x01010113.
Lemma F_18f74 : fetch_word Plain.M.loaded_segments (0x18f74 : word) = Some W_18f74.
Proof. vm_refl. Qed.
Lemma D_18f74 : decode_any W_18f74 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f78 : bv 32 := 0x00008067.
Lemma F_18f78 : fetch_word Plain.M.loaded_segments (0x18f78 : word) = Some W_18f78.
Proof. vm_refl. Qed.
Lemma D_18f78 : decode_any W_18f78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f7c : bv 32 := 0xff010113.
Lemma F_18f7c : fetch_word Plain.M.loaded_segments (0x18f7c : word) = Some W_18f7c.
Proof. vm_refl. Qed.
Lemma D_18f7c : decode_any W_18f7c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f80 : bv 32 := 0x00113423.
Lemma F_18f80 : fetch_word Plain.M.loaded_segments (0x18f80 : word) = Some W_18f80.
Proof. vm_refl. Qed.
Lemma D_18f80 : decode_any W_18f80 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f84 : bv 32 := 0x00813023.
Lemma F_18f84 : fetch_word Plain.M.loaded_segments (0x18f84 : word) = Some W_18f84.
Proof. vm_refl. Qed.
Lemma D_18f84 : decode_any W_18f84 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f88 : bv 32 := 0x00038517.
Lemma F_18f88 : fetch_word Plain.M.loaded_segments (0x18f88 : word) = Some W_18f88.
Proof. vm_refl. Qed.
Lemma D_18f88 : decode_any W_18f88 = Some (Auipc 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f8c : bv 32 := 0x11850413.
Lemma F_18f8c : fetch_word Plain.M.loaded_segments (0x18f8c : word) = Some W_18f8c.
Proof. vm_refl. Qed.
Lemma D_18f8c : decode_any W_18f8c = Some (OpImm ALU_ADD 8 10 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f90 : bv 32 := 0x00040513.
Lemma F_18f90 : fetch_word Plain.M.loaded_segments (0x18f90 : word) = Some W_18f90.
Proof. vm_refl. Qed.
Lemma D_18f90 : decode_any W_18f90 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f94 : bv 32 := 0x258050ef.
Lemma F_18f94 : fetch_word Plain.M.loaded_segments (0x18f94 : word) = Some W_18f94.
Proof. vm_refl. Qed.
Lemma D_18f94 : decode_any W_18f94 = Some (Jal 1 21080, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f98 : bv 32 := 0x00840513.
Lemma F_18f98 : fetch_word Plain.M.loaded_segments (0x18f98 : word) = Some W_18f98.
Proof. vm_refl. Qed.
Lemma D_18f98 : decode_any W_18f98 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f9c : bv 32 := 0x00813083.
Lemma F_18f9c : fetch_word Plain.M.loaded_segments (0x18f9c : word) = Some W_18f9c.
Proof. vm_refl. Qed.
Lemma D_18f9c : decode_any W_18f9c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fa0 : bv 32 := 0x00013403.
Lemma F_18fa0 : fetch_word Plain.M.loaded_segments (0x18fa0 : word) = Some W_18fa0.
Proof. vm_refl. Qed.
Lemma D_18fa0 : decode_any W_18fa0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fa4 : bv 32 := 0x01010113.
Lemma F_18fa4 : fetch_word Plain.M.loaded_segments (0x18fa4 : word) = Some W_18fa4.
Proof. vm_refl. Qed.
Lemma D_18fa4 : decode_any W_18fa4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fa8 : bv 32 := 0x00008067.
Lemma F_18fa8 : fetch_word Plain.M.loaded_segments (0x18fa8 : word) = Some W_18fa8.
Proof. vm_refl. Qed.
Lemma D_18fa8 : decode_any W_18fa8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fb8 : bv 32 := 0x00008067.
Lemma F_18fb8 : fetch_word Plain.M.loaded_segments (0x18fb8 : word) = Some W_18fb8.
Proof. vm_refl. Qed.
Lemma D_18fb8 : decode_any W_18fb8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fe8 : bv 32 := 0xf9010113.
Lemma F_18fe8 : fetch_word Plain.M.loaded_segments (0x18fe8 : word) = Some W_18fe8.
Proof. vm_refl. Qed.
Lemma D_18fe8 : decode_any W_18fe8 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fec : bv 32 := 0x06113423.
Lemma F_18fec : fetch_word Plain.M.loaded_segments (0x18fec : word) = Some W_18fec.
Proof. vm_refl. Qed.
Lemma D_18fec : decode_any W_18fec = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ff0 : bv 32 := 0x06813023.
Lemma F_18ff0 : fetch_word Plain.M.loaded_segments (0x18ff0 : word) = Some W_18ff0.
Proof. vm_refl. Qed.
Lemma D_18ff0 : decode_any W_18ff0 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ff4 : bv 32 := 0x04913c23.
Lemma F_18ff4 : fetch_word Plain.M.loaded_segments (0x18ff4 : word) = Some W_18ff4.
Proof. vm_refl. Qed.
Lemma D_18ff4 : decode_any W_18ff4 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ff8 : bv 32 := 0x05213823.
Lemma F_18ff8 : fetch_word Plain.M.loaded_segments (0x18ff8 : word) = Some W_18ff8.
Proof. vm_refl. Qed.
Lemma D_18ff8 : decode_any W_18ff8 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ffc : bv 32 := 0x05313423.
Lemma F_18ffc : fetch_word Plain.M.loaded_segments (0x18ffc : word) = Some W_18ffc.
Proof. vm_refl. Qed.
Lemma D_18ffc : decode_any W_18ffc = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_19000 : bv 32 := 0x05413023.
Lemma F_19000 : fetch_word Plain.M.loaded_segments (0x19000 : word) = Some W_19000.
Proof. vm_refl. Qed.
Lemma D_19000 : decode_any W_19000 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_19004 : bv 32 := 0x03513c23.
Lemma F_19004 : fetch_word Plain.M.loaded_segments (0x19004 : word) = Some W_19004.
Proof. vm_refl. Qed.
Lemma D_19004 : decode_any W_19004 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_19008 : bv 32 := 0x03613823.
Lemma F_19008 : fetch_word Plain.M.loaded_segments (0x19008 : word) = Some W_19008.
Proof. vm_refl. Qed.
Lemma D_19008 : decode_any W_19008 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1900c : bv 32 := 0x00060413.
Lemma F_1900c : fetch_word Plain.M.loaded_segments (0x1900c : word) = Some W_1900c.
Proof. vm_refl. Qed.
Lemma D_1900c : decode_any W_1900c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19010 : bv 32 := 0x00050493.
Lemma F_19010 : fetch_word Plain.M.loaded_segments (0x19010 : word) = Some W_19010.
Proof. vm_refl. Qed.
Lemma D_19010 : decode_any W_19010 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19014 : bv 32 := 0x00006517.
Lemma F_19014 : fetch_word Plain.M.loaded_segments (0x19014 : word) = Some W_19014.
Proof. vm_refl. Qed.
Lemma D_19014 : decode_any W_19014 = Some (Auipc 10 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_19018 : bv 32 := 0x64c53a83.
Lemma F_19018 : fetch_word Plain.M.loaded_segments (0x19018 : word) = Some W_19018.
Proof. vm_refl. Qed.
Lemma D_19018 : decode_any W_19018 = Some (Load SZ8 true 21 10 1612, 4%Z).
Proof. vm_refl. Qed.

Definition W_1901c : bv 32 := 0x000ab503.
Lemma F_1901c : fetch_word Plain.M.loaded_segments (0x1901c : word) = Some W_1901c.
Proof. vm_refl. Qed.
Lemma D_1901c : decode_any W_1901c = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19020 : bv 32 := 0x02a13423.
Lemma F_19020 : fetch_word Plain.M.loaded_segments (0x19020 : word) = Some W_19020.
Proof. vm_refl. Qed.
Lemma D_19020 : decode_any W_19020 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19024 : bv 32 := 0x0284b503.
Lemma F_19024 : fetch_word Plain.M.loaded_segments (0x19024 : word) = Some W_19024.
Proof. vm_refl. Qed.
Lemma D_19024 : decode_any W_19024 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19028 : bv 32 := 0x0384b603.
Lemma F_19028 : fetch_word Plain.M.loaded_segments (0x19028 : word) = Some W_19028.
Proof. vm_refl. Qed.
Lemma D_19028 : decode_any W_19028 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1902c : bv 32 := 0x40c50b33.
Lemma F_1902c : fetch_word Plain.M.loaded_segments (0x1902c : word) = Some W_1902c.
Proof. vm_refl. Qed.
Lemma D_1902c : decode_any W_1902c = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19030 : bv 32 := 0x00c546b3.
Lemma F_19030 : fetch_word Plain.M.loaded_segments (0x19030 : word) = Some W_19030.
Proof. vm_refl. Qed.
Lemma D_19030 : decode_any W_19030 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19034 : bv 32 := 0x00c13423.
Lemma F_19034 : fetch_word Plain.M.loaded_segments (0x19034 : word) = Some W_19034.
Proof. vm_refl. Qed.
Lemma D_19034 : decode_any W_19034 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19038 : bv 32 := 0x01613823.
Lemma F_19038 : fetch_word Plain.M.loaded_segments (0x19038 : word) = Some W_19038.
Proof. vm_refl. Qed.
Lemma D_19038 : decode_any W_19038 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1903c : bv 32 := 0x00b13c23.
Lemma F_1903c : fetch_word Plain.M.loaded_segments (0x1903c : word) = Some W_1903c.
Proof. vm_refl. Qed.
Lemma D_1903c : decode_any W_1903c = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19040 : bv 32 := 0x02813023.
Lemma F_19040 : fetch_word Plain.M.loaded_segments (0x19040 : word) = Some W_19040.
Proof. vm_refl. Qed.
Lemma D_19040 : decode_any W_19040 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19044 : bv 32 := 0x008b0b33.
Lemma F_19044 : fetch_word Plain.M.loaded_segments (0x19044 : word) = Some W_19044.
Proof. vm_refl. Qed.
Lemma D_19044 : decode_any W_19044 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19048 : bv 32 := 0x00d03933.
Lemma F_19048 : fetch_word Plain.M.loaded_segments (0x19048 : word) = Some W_19048.
Proof. vm_refl. Qed.
Lemma D_19048 : decode_any W_19048 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1904c : bv 32 := 0x00c50663.
Lemma F_1904c : fetch_word Plain.M.loaded_segments (0x1904c : word) = Some W_1904c.
Proof. vm_refl. Qed.
Lemma D_1904c : decode_any W_1904c = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19050 : bv 32 := 0x00810993.
Lemma F_19050 : fetch_word Plain.M.loaded_segments (0x19050 : word) = Some W_19050.
Proof. vm_refl. Qed.
Lemma D_19050 : decode_any W_19050 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19054 : bv 32 := 0x0080006f.
Lemma F_19054 : fetch_word Plain.M.loaded_segments (0x19054 : word) = Some W_19054.
Proof. vm_refl. Qed.
Lemma D_19054 : decode_any W_19054 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19058 : bv 32 := 0x01810993.
Lemma F_19058 : fetch_word Plain.M.loaded_segments (0x19058 : word) = Some W_19058.
Proof. vm_refl. Qed.
Lemma D_19058 : decode_any W_19058 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1905c : bv 32 := 0x0784a503.
Lemma F_1905c : fetch_word Plain.M.loaded_segments (0x1905c : word) = Some W_1905c.
Proof. vm_refl. Qed.
Lemma D_1905c : decode_any W_1905c = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_19060 : bv 32 := 0x00190913.
Lemma F_19060 : fetch_word Plain.M.loaded_segments (0x19060 : word) = Some W_19060.
Proof. vm_refl. Qed.
Lemma D_19060 : decode_any W_19060 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19064 : bv 32 := 0x04200893.
Lemma F_19064 : fetch_word Plain.M.loaded_segments (0x19064 : word) = Some W_19064.
Proof. vm_refl. Qed.
Lemma D_19064 : decode_any W_19064 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_19068 : bv 32 := 0x00098593.
Lemma F_19068 : fetch_word Plain.M.loaded_segments (0x19068 : word) = Some W_19068.
Proof. vm_refl. Qed.
Lemma D_19068 : decode_any W_19068 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1906c : bv 32 := 0x00090613.
Lemma F_1906c : fetch_word Plain.M.loaded_segments (0x1906c : word) = Some W_1906c.
Proof. vm_refl. Qed.
Lemma D_1906c : decode_any W_1906c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19070 : bv 32 := 0x00000073.
Lemma F_19070 : fetch_word Plain.M.loaded_segments (0x19070 : word) = Some W_19070.
Proof. vm_refl. Qed.
Lemma D_19070 : decode_any W_19070 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_19070 : is_ecall W_19070 = true.
Proof. reflexivity. Qed.

Definition W_19074 : bv 32 := 0xbadfd0ef.
Lemma F_19074 : fetch_word Plain.M.loaded_segments (0x19074 : word) = Some W_19074.
Proof. vm_refl. Qed.
Lemma D_19074 : decode_any W_19074 = Some (Jal 1 2087852, 4%Z).
Proof. vm_refl. Qed.

Definition W_19078 : bv 32 := 0x09651863.
Lemma F_19078 : fetch_word Plain.M.loaded_segments (0x19078 : word) = Some W_19078.
Proof. vm_refl. Qed.
Lemma D_19078 : decode_any W_19078 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_1907c : bv 32 := 0x0584b503.
Lemma F_1907c : fetch_word Plain.M.loaded_segments (0x1907c : word) = Some W_1907c.
Proof. vm_refl. Qed.
Lemma D_1907c : decode_any W_1907c = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_19080 : bv 32 := 0x0604b583.
Lemma F_19080 : fetch_word Plain.M.loaded_segments (0x19080 : word) = Some W_19080.
Proof. vm_refl. Qed.
Lemma D_19080 : decode_any W_19080 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_19084 : bv 32 := 0x00b505b3.
Lemma F_19084 : fetch_word Plain.M.loaded_segments (0x19084 : word) = Some W_19084.
Proof. vm_refl. Qed.
Lemma D_19084 : decode_any W_19084 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_19088 : bv 32 := 0x02b4b023.
Lemma F_19088 : fetch_word Plain.M.loaded_segments (0x19088 : word) = Some W_19088.
Proof. vm_refl. Qed.
Lemma D_19088 : decode_any W_19088 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1908c : bv 32 := 0x02a4b423.
Lemma F_1908c : fetch_word Plain.M.loaded_segments (0x1908c : word) = Some W_1908c.
Proof. vm_refl. Qed.
Lemma D_1908c : decode_any W_1908c = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19090 : bv 32 := 0x02a4bc23.
Lemma F_19090 : fetch_word Plain.M.loaded_segments (0x19090 : word) = Some W_19090.
Proof. vm_refl. Qed.
Lemma D_19090 : decode_any W_19090 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_19094 : bv 32 := 0x00040513.
Lemma F_19094 : fetch_word Plain.M.loaded_segments (0x19094 : word) = Some W_19094.
Proof. vm_refl. Qed.
Lemma D_19094 : decode_any W_19094 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19098 : bv 32 := 0x000ab583.
Lemma F_19098 : fetch_word Plain.M.loaded_segments (0x19098 : word) = Some W_19098.
Proof. vm_refl. Qed.
Lemma D_19098 : decode_any W_19098 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1909c : bv 32 := 0x02813603.
Lemma F_1909c : fetch_word Plain.M.loaded_segments (0x1909c : word) = Some W_1909c.
Proof. vm_refl. Qed.
Lemma D_1909c : decode_any W_1909c = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_190a0 : bv 32 := 0x0cc59a63.
Lemma F_190a0 : fetch_word Plain.M.loaded_segments (0x190a0 : word) = Some W_190a0.
Proof. vm_refl. Qed.
Lemma D_190a0 : decode_any W_190a0 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_190a4 : bv 32 := 0x06813083.
Lemma F_190a4 : fetch_word Plain.M.loaded_segments (0x190a4 : word) = Some W_190a4.
Proof. vm_refl. Qed.
Lemma D_190a4 : decode_any W_190a4 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_190a8 : bv 32 := 0x06013403.
Lemma F_190a8 : fetch_word Plain.M.loaded_segments (0x190a8 : word) = Some W_190a8.
Proof. vm_refl. Qed.
Lemma D_190a8 : decode_any W_190a8 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_190ac : bv 32 := 0x05813483.
Lemma F_190ac : fetch_word Plain.M.loaded_segments (0x190ac : word) = Some W_190ac.
Proof. vm_refl. Qed.
Lemma D_190ac : decode_any W_190ac = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_190b0 : bv 32 := 0x05013903.
Lemma F_190b0 : fetch_word Plain.M.loaded_segments (0x190b0 : word) = Some W_190b0.
Proof. vm_refl. Qed.
Lemma D_190b0 : decode_any W_190b0 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_190b4 : bv 32 := 0x04813983.
Lemma F_190b4 : fetch_word Plain.M.loaded_segments (0x190b4 : word) = Some W_190b4.
Proof. vm_refl. Qed.
Lemma D_190b4 : decode_any W_190b4 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_190b8 : bv 32 := 0x04013a03.
Lemma F_190b8 : fetch_word Plain.M.loaded_segments (0x190b8 : word) = Some W_190b8.
Proof. vm_refl. Qed.
Lemma D_190b8 : decode_any W_190b8 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_190bc : bv 32 := 0x03813a83.
Lemma F_190bc : fetch_word Plain.M.loaded_segments (0x190bc : word) = Some W_190bc.
Proof. vm_refl. Qed.
Lemma D_190bc : decode_any W_190bc = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_190c0 : bv 32 := 0x03013b03.
Lemma F_190c0 : fetch_word Plain.M.loaded_segments (0x190c0 : word) = Some W_190c0.
Proof. vm_refl. Qed.
Lemma D_190c0 : decode_any W_190c0 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_190c4 : bv 32 := 0x07010113.
Lemma F_190c4 : fetch_word Plain.M.loaded_segments (0x190c4 : word) = Some W_190c4.
Proof. vm_refl. Qed.
Lemma D_190c4 : decode_any W_190c4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_190c8 : bv 32 := 0x00008067.
Lemma F_190c8 : fetch_word Plain.M.loaded_segments (0x190c8 : word) = Some W_190c8.
Proof. vm_refl. Qed.
Lemma D_190c8 : decode_any W_190c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_190cc : bv 32 := 0x00800713.
Lemma F_190cc : fetch_word Plain.M.loaded_segments (0x190cc : word) = Some W_190cc.
Proof. vm_refl. Qed.
Lemma D_190cc : decode_any W_190cc = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_190d0 : bv 32 := 0x000a0593.
Lemma F_190d0 : fetch_word Plain.M.loaded_segments (0x190d0 : word) = Some W_190d0.
Proof. vm_refl. Qed.
Lemma D_190d0 : decode_any W_190d0 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_190d4 : bv 32 := 0x00e98733.
Lemma F_190d4 : fetch_word Plain.M.loaded_segments (0x190d4 : word) = Some W_190d4.
Proof. vm_refl. Qed.
Lemma D_190d4 : decode_any W_190d4 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_190d8 : bv 32 := 0x00073783.
Lemma F_190d8 : fetch_word Plain.M.loaded_segments (0x190d8 : word) = Some W_190d8.
Proof. vm_refl. Qed.
Lemma D_190d8 : decode_any W_190d8 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_190dc : bv 32 := 0x40ab0b33.
Lemma F_190dc : fetch_word Plain.M.loaded_segments (0x190dc : word) = Some W_190dc.
Proof. vm_refl. Qed.
Lemma D_190dc : decode_any W_190dc = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_190e0 : bv 32 := 0x0784a503.
Lemma F_190e0 : fetch_word Plain.M.loaded_segments (0x190e0 : word) = Some W_190e0.
Proof. vm_refl. Qed.
Lemma D_190e0 : decode_any W_190e0 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_190e4 : bv 32 := 0x40c9093b.
Lemma F_190e4 : fetch_word Plain.M.loaded_segments (0x190e4 : word) = Some W_190e4.
Proof. vm_refl. Qed.
Lemma D_190e4 : decode_any W_190e4 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_190e8 : bv 32 := 0x40d787b3.
Lemma F_190e8 : fetch_word Plain.M.loaded_segments (0x190e8 : word) = Some W_190e8.
Proof. vm_refl. Qed.
Lemma D_190e8 : decode_any W_190e8 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_190ec : bv 32 := 0x00f73023.
Lemma F_190ec : fetch_word Plain.M.loaded_segments (0x190ec : word) = Some W_190ec.
Proof. vm_refl. Qed.
Lemma D_190ec : decode_any W_190ec = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_190f0 : bv 32 := 0x04200893.
Lemma F_190f0 : fetch_word Plain.M.loaded_segments (0x190f0 : word) = Some W_190f0.
Proof. vm_refl. Qed.
Lemma D_190f0 : decode_any W_190f0 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_190f4 : bv 32 := 0x00090613.
Lemma F_190f4 : fetch_word Plain.M.loaded_segments (0x190f4 : word) = Some W_190f4.
Proof. vm_refl. Qed.
Lemma D_190f4 : decode_any W_190f4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_190f8 : bv 32 := 0x00000073.
Lemma F_190f8 : fetch_word Plain.M.loaded_segments (0x190f8 : word) = Some W_190f8.
Proof. vm_refl. Qed.
Lemma D_190f8 : decode_any W_190f8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_190f8 : is_ecall W_190f8 = true.
Proof. reflexivity. Qed.

Definition W_190fc : bv 32 := 0xb25fd0ef.
Lemma F_190fc : fetch_word Plain.M.loaded_segments (0x190fc : word) = Some W_190fc.
Proof. vm_refl. Qed.
Lemma D_190fc : decode_any W_190fc = Some (Jal 1 2087716, 4%Z).
Proof. vm_refl. Qed.

Definition W_19100 : bv 32 := 0x000a0993.
Lemma F_19100 : fetch_word Plain.M.loaded_segments (0x19100 : word) = Some W_19100.
Proof. vm_refl. Qed.
Lemma D_19100 : decode_any W_19100 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19104 : bv 32 := 0xf7650ce3.
Lemma F_19104 : fetch_word Plain.M.loaded_segments (0x19104 : word) = Some W_19104.
Proof. vm_refl. Qed.
Lemma D_19104 : decode_any W_19104 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_19108 : bv 32 := 0x02054c63.
Lemma F_19108 : fetch_word Plain.M.loaded_segments (0x19108 : word) = Some W_19108.
Proof. vm_refl. Qed.
Lemma D_19108 : decode_any W_19108 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1910c : bv 32 := 0x0089b583.
Lemma F_1910c : fetch_word Plain.M.loaded_segments (0x1910c : word) = Some W_1910c.
Proof. vm_refl. Qed.
Lemma D_1910c : decode_any W_1910c = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19110 : bv 32 := 0x00a5b633.
Lemma F_19110 : fetch_word Plain.M.loaded_segments (0x19110 : word) = Some W_19110.
Proof. vm_refl. Qed.
Lemma D_19110 : decode_any W_19110 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_19114 : bv 32 := 0x00461a13.
Lemma F_19114 : fetch_word Plain.M.loaded_segments (0x19114 : word) = Some W_19114.
Proof. vm_refl. Qed.
Lemma D_19114 : decode_any W_19114 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_19118 : bv 32 := 0x01498a33.
Lemma F_19118 : fetch_word Plain.M.loaded_segments (0x19118 : word) = Some W_19118.
Proof. vm_refl. Qed.
Lemma D_19118 : decode_any W_19118 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1911c : bv 32 := 0x000a3703.
Lemma F_1911c : fetch_word Plain.M.loaded_segments (0x1911c : word) = Some W_1911c.
Proof. vm_refl. Qed.
Lemma D_1911c : decode_any W_1911c = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19120 : bv 32 := 0x40c006b3.
Lemma F_19120 : fetch_word Plain.M.loaded_segments (0x19120 : word) = Some W_19120.
Proof. vm_refl. Qed.
Lemma D_19120 : decode_any W_19120 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19124 : bv 32 := 0x00b6f6b3.
Lemma F_19124 : fetch_word Plain.M.loaded_segments (0x19124 : word) = Some W_19124.
Proof. vm_refl. Qed.
Lemma D_19124 : decode_any W_19124 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_19128 : bv 32 := 0x40d506b3.
Lemma F_19128 : fetch_word Plain.M.loaded_segments (0x19128 : word) = Some W_19128.
Proof. vm_refl. Qed.
Lemma D_19128 : decode_any W_19128 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1912c : bv 32 := 0x00d70733.
Lemma F_1912c : fetch_word Plain.M.loaded_segments (0x1912c : word) = Some W_1912c.
Proof. vm_refl. Qed.
Lemma D_1912c : decode_any W_1912c = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_19130 : bv 32 := 0x00ea3023.
Lemma F_19130 : fetch_word Plain.M.loaded_segments (0x19130 : word) = Some W_19130.
Proof. vm_refl. Qed.
Lemma D_19130 : decode_any W_19130 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19134 : bv 32 := 0xf8a5fce3.
Lemma F_19134 : fetch_word Plain.M.loaded_segments (0x19134 : word) = Some W_19134.
Proof. vm_refl. Qed.
Lemma D_19134 : decode_any W_19134 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_19138 : bv 32 := 0x01800713.
Lemma F_19138 : fetch_word Plain.M.loaded_segments (0x19138 : word) = Some W_19138.
Proof. vm_refl. Qed.
Lemma D_19138 : decode_any W_19138 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1913c : bv 32 := 0xf95ff06f.
Lemma F_1913c : fetch_word Plain.M.loaded_segments (0x1913c : word) = Some W_1913c.
Proof. vm_refl. Qed.
Lemma D_1913c : decode_any W_1913c = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.
