(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_670e8 : bv 32 := 0xfb010113.
Lemma F_670e8 : fetch_word Asan.M.loaded_segments (0x670e8 : word) = Some W_670e8.
Proof. vm_refl. Qed.
Lemma D_670e8 : decode_any W_670e8 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_670ec : bv 32 := 0x04113423.
Lemma F_670ec : fetch_word Asan.M.loaded_segments (0x670ec : word) = Some W_670ec.
Proof. vm_refl. Qed.
Lemma D_670ec : decode_any W_670ec = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_670f0 : bv 32 := 0x04813023.
Lemma F_670f0 : fetch_word Asan.M.loaded_segments (0x670f0 : word) = Some W_670f0.
Proof. vm_refl. Qed.
Lemma D_670f0 : decode_any W_670f0 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_670f4 : bv 32 := 0x02913c23.
Lemma F_670f4 : fetch_word Asan.M.loaded_segments (0x670f4 : word) = Some W_670f4.
Proof. vm_refl. Qed.
Lemma D_670f4 : decode_any W_670f4 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_670f8 : bv 32 := 0x03213823.
Lemma F_670f8 : fetch_word Asan.M.loaded_segments (0x670f8 : word) = Some W_670f8.
Proof. vm_refl. Qed.
Lemma D_670f8 : decode_any W_670f8 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_670fc : bv 32 := 0x03313423.
Lemma F_670fc : fetch_word Asan.M.loaded_segments (0x670fc : word) = Some W_670fc.
Proof. vm_refl. Qed.
Lemma D_670fc : decode_any W_670fc = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_67100 : bv 32 := 0x00077517.
Lemma F_67100 : fetch_word Asan.M.loaded_segments (0x67100 : word) = Some W_67100.
Proof. vm_refl. Qed.
Lemma D_67100 : decode_any W_67100 = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_67104 : bv 32 := 0x71850493.
Lemma F_67104 : fetch_word Asan.M.loaded_segments (0x67104 : word) = Some W_67104.
Proof. vm_refl. Qed.
Lemma D_67104 : decode_any W_67104 = Some (OpImm ALU_ADD 9 10 1816, 4%Z).
Proof. vm_refl. Qed.

Definition W_67108 : bv 32 := 0x00048503.
Lemma F_67108 : fetch_word Asan.M.loaded_segments (0x67108 : word) = Some W_67108.
Proof. vm_refl. Qed.
Lemma D_67108 : decode_any W_67108 = Some (Load SZ1 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6710c : bv 32 := 0x00100593.
Lemma F_6710c : fetch_word Asan.M.loaded_segments (0x6710c : word) = Some W_6710c.
Proof. vm_refl. Qed.
Lemma D_6710c : decode_any W_6710c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_67110 : bv 32 := 0x0230000f.
Lemma F_67110 : fetch_word Asan.M.loaded_segments (0x67110 : word) = Some W_67110.
Proof. vm_refl. Qed.
Lemma D_67110 : decode_any W_67110 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67114 : bv 32 := 0x10b51e63.
Lemma F_67114 : fetch_word Asan.M.loaded_segments (0x67114 : word) = Some W_67114.
Proof. vm_refl. Qed.
Lemma D_67114 : decode_any W_67114 = Some (Branch BC_NE 10 11 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_67118 : bv 32 := 0xe5dfa0ef.
Lemma F_67118 : fetch_word Asan.M.loaded_segments (0x67118 : word) = Some W_67118.
Proof. vm_refl. Qed.
Lemma D_67118 : decode_any W_67118 = Some (Jal 1 2076252, 4%Z).
Proof. vm_refl. Qed.

Definition W_6711c : bv 32 := 0x0e051663.
Lemma F_6711c : fetch_word Asan.M.loaded_segments (0x6711c : word) = Some W_6711c.
Proof. vm_refl. Qed.
Lemma D_6711c : decode_any W_6711c = Some (Branch BC_NE 10 0 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_67120 : bv 32 := 0xfffa9517.
Lemma F_67120 : fetch_word Asan.M.loaded_segments (0x67120 : word) = Some W_67120.
Proof. vm_refl. Qed.
Lemma D_67120 : decode_any W_67120 = Some (Auipc 10 1048489, 4%Z).
Proof. vm_refl. Qed.

Definition W_67124 : bv 32 := 0x2e853403.
Lemma F_67124 : fetch_word Asan.M.loaded_segments (0x67124 : word) = Some W_67124.
Proof. vm_refl. Qed.
Lemma D_67124 : decode_any W_67124 = Some (Load SZ8 true 8 10 744, 4%Z).
Proof. vm_refl. Qed.

Definition W_67128 : bv 32 := 0x02813023.
Lemma F_67128 : fetch_word Asan.M.loaded_segments (0x67128 : word) = Some W_67128.
Proof. vm_refl. Qed.
Lemma D_67128 : decode_any W_67128 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6712c : bv 32 := 0x00813c23.
Lemma F_6712c : fetch_word Asan.M.loaded_segments (0x6712c : word) = Some W_6712c.
Proof. vm_refl. Qed.
Lemma D_6712c : decode_any W_6712c = Some (Store SZ8 2 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_67130 : bv 32 := 0x6b4020ef.
Lemma F_67130 : fetch_word Asan.M.loaded_segments (0x67130 : word) = Some W_67130.
Proof. vm_refl. Qed.
Lemma D_67130 : decode_any W_67130 = Some (Jal 1 9908, 4%Z).
Proof. vm_refl. Qed.

Definition W_67134 : bv 32 := 0x08050263.
Lemma F_67134 : fetch_word Asan.M.loaded_segments (0x67134 : word) = Some W_67134.
Proof. vm_refl. Qed.
Lemma D_67134 : decode_any W_67134 = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_67138 : bv 32 := 0x0006e597.
Lemma F_67138 : fetch_word Asan.M.loaded_segments (0x67138 : word) = Some W_67138.
Proof. vm_refl. Qed.
Lemma D_67138 : decode_any W_67138 = Some (Auipc 11 110, 4%Z).
Proof. vm_refl. Qed.

Definition W_6713c : bv 32 := 0x7605b903.
Lemma F_6713c : fetch_word Asan.M.loaded_segments (0x6713c : word) = Some W_6713c.
Proof. vm_refl. Qed.
Lemma D_6713c : decode_any W_6713c = Some (Load SZ8 true 18 11 1888, 4%Z).
Proof. vm_refl. Qed.

Definition W_67140 : bv 32 := 0x00093403.
Lemma F_67140 : fetch_word Asan.M.loaded_segments (0x67140 : word) = Some W_67140.
Proof. vm_refl. Qed.
Lemma D_67140 : decode_any W_67140 = Some (Load SZ8 true 8 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67144 : bv 32 := 0x00041c63.
Lemma F_67144 : fetch_word Asan.M.loaded_segments (0x67144 : word) = Some W_67144.
Proof. vm_refl. Qed.
Lemma D_67144 : decode_any W_67144 = Some (Branch BC_NE 8 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_67148 : bv 32 := 0x00050993.
Lemma F_67148 : fetch_word Asan.M.loaded_segments (0x67148 : word) = Some W_67148.
Proof. vm_refl. Qed.
Lemma D_67148 : decode_any W_67148 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6714c : bv 32 := 0x1410b0ef.
Lemma F_6714c : fetch_word Asan.M.loaded_segments (0x6714c : word) = Some W_6714c.
Proof. vm_refl. Qed.
Lemma D_6714c : decode_any W_6714c = Some (Jal 1 47424, 4%Z).
Proof. vm_refl. Qed.

Definition W_67150 : bv 32 := 0x00050413.
Lemma F_67150 : fetch_word Asan.M.loaded_segments (0x67150 : word) = Some W_67150.
Proof. vm_refl. Qed.
Lemma D_67150 : decode_any W_67150 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67154 : bv 32 := 0x00098513.
Lemma F_67154 : fetch_word Asan.M.loaded_segments (0x67154 : word) = Some W_67154.
Proof. vm_refl. Qed.
Lemma D_67154 : decode_any W_67154 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67158 : bv 32 := 0x00893023.
Lemma F_67158 : fetch_word Asan.M.loaded_segments (0x67158 : word) = Some W_67158.
Proof. vm_refl. Qed.
Lemma D_67158 : decode_any W_67158 = Some (Store SZ8 18 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6715c : bv 32 := 0x04d020ef.
Lemma F_6715c : fetch_word Asan.M.loaded_segments (0x6715c : word) = Some W_6715c.
Proof. vm_refl. Qed.
Lemma D_6715c : decode_any W_6715c = Some (Jal 1 10316, 4%Z).
Proof. vm_refl. Qed.

Definition W_67160 : bv 32 := 0x00050613.
Lemma F_67160 : fetch_word Asan.M.loaded_segments (0x67160 : word) = Some W_67160.
Proof. vm_refl. Qed.
Lemma D_67160 : decode_any W_67160 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67164 : bv 32 := 0x00a13c23.
Lemma F_67164 : fetch_word Asan.M.loaded_segments (0x67164 : word) = Some W_67164.
Proof. vm_refl. Qed.
Lemma D_67164 : decode_any W_67164 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_67168 : bv 32 := 0x01010513.
Lemma F_67168 : fetch_word Asan.M.loaded_segments (0x67168 : word) = Some W_67168.
Proof. vm_refl. Qed.
Lemma D_67168 : decode_any W_67168 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6716c : bv 32 := 0x40850533.
Lemma F_6716c : fetch_word Asan.M.loaded_segments (0x6716c : word) = Some W_6716c.
Proof. vm_refl. Qed.
Lemma D_6716c : decode_any W_6716c = Some (Op ALU_SUB 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_67170 : bv 32 := 0x408006b3.
Lemma F_67170 : fetch_word Asan.M.loaded_segments (0x67170 : word) = Some W_67170.
Proof. vm_refl. Qed.
Lemma D_67170 : decode_any W_67170 = Some (Op ALU_SUB 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_67174 : bv 32 := 0x00d576b3.
Lemma F_67174 : fetch_word Asan.M.loaded_segments (0x67174 : word) = Some W_67174.
Proof. vm_refl. Qed.
Lemma D_67174 : decode_any W_67174 = Some (Op ALU_AND 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_67178 : bv 32 := 0x02d13023.
Lemma F_67178 : fetch_word Asan.M.loaded_segments (0x67178 : word) = Some W_67178.
Proof. vm_refl. Qed.
Lemma D_67178 : decode_any W_67178 = Some (Store SZ8 2 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6717c : bv 32 := 0x40d60733.
Lemma F_6717c : fetch_word Asan.M.loaded_segments (0x6717c : word) = Some W_6717c.
Proof. vm_refl. Qed.
Lemma D_6717c : decode_any W_6717c = Some (Op ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_67180 : bv 32 := 0x04000537.
Lemma F_67180 : fetch_word Asan.M.loaded_segments (0x67180 : word) = Some W_67180.
Proof. vm_refl. Qed.
Lemma D_67180 : decode_any W_67180 = Some (Lui 10 16384, 4%Z).
Proof. vm_refl. Qed.

Definition W_67184 : bv 32 := 0x0015051b.
Lemma F_67184 : fetch_word Asan.M.loaded_segments (0x67184 : word) = Some W_67184.
Proof. vm_refl. Qed.
Lemma D_67184 : decode_any W_67184 = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_67188 : bv 32 := 0x06a76263.
Lemma F_67188 : fetch_word Asan.M.loaded_segments (0x67188 : word) = Some W_67188.
Proof. vm_refl. Qed.
Lemma D_67188 : decode_any W_67188 = Some (Branch BC_LTU 14 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_6718c : bv 32 := 0x0034c503.
Lemma F_6718c : fetch_word Asan.M.loaded_segments (0x6718c : word) = Some W_6718c.
Proof. vm_refl. Qed.
Lemma D_6718c : decode_any W_6718c = Some (Load SZ1 false 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_67190 : bv 32 := 0x06051c63.
Lemma F_67190 : fetch_word Asan.M.loaded_segments (0x67190 : word) = Some W_67190.
Proof. vm_refl. Qed.
Lemma D_67190 : decode_any W_67190 = Some (Branch BC_NE 10 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_67194 : bv 32 := 0x00100513.
Lemma F_67194 : fetch_word Asan.M.loaded_segments (0x67194 : word) = Some W_67194.
Proof. vm_refl. Qed.
Lemma D_67194 : decode_any W_67194 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_67198 : bv 32 := 0x00a481a3.
Lemma F_67198 : fetch_word Asan.M.loaded_segments (0x67198 : word) = Some W_67198.
Proof. vm_refl. Qed.
Lemma D_67198 : decode_any W_67198 = Some (Store SZ1 9 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6719c : bv 32 := 0xfffac517.
Lemma F_6719c : fetch_word Asan.M.loaded_segments (0x6719c : word) = Some W_6719c.
Proof. vm_refl. Qed.
Lemma D_6719c : decode_any W_6719c = Some (Auipc 10 1048492, 4%Z).
Proof. vm_refl. Qed.

Definition W_671a0 : bv 32 := 0xfffb4597.
Lemma F_671a0 : fetch_word Asan.M.loaded_segments (0x671a0 : word) = Some W_671a0.
Proof. vm_refl. Qed.
Lemma D_671a0 : decode_any W_671a0 = Some (Auipc 11 1048500, 4%Z).
Proof. vm_refl. Qed.

Definition W_671a4 : bv 32 := 0x40150513.
Lemma F_671a4 : fetch_word Asan.M.loaded_segments (0x671a4 : word) = Some W_671a4.
Proof. vm_refl. Qed.
Lemma D_671a4 : decode_any W_671a4 = Some (OpImm ALU_ADD 10 10 1025, 4%Z).
Proof. vm_refl. Qed.

Definition W_671a8 : bv 32 := 0x8f058593.
Lemma F_671a8 : fetch_word Asan.M.loaded_segments (0x671a8 : word) = Some W_671a8.
Proof. vm_refl. Qed.
Lemma D_671a8 : decode_any W_671a8 = Some (OpImm ALU_ADD 11 11 2288, 4%Z).
Proof. vm_refl. Qed.

Definition W_671ac : bv 32 := 0x00070793.
Lemma F_671ac : fetch_word Asan.M.loaded_segments (0x671ac : word) = Some W_671ac.
Proof. vm_refl. Qed.
Lemma D_671ac : decode_any W_671ac = Some (OpImm ALU_ADD 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_671b0 : bv 32 := 0x5d80d0ef.
Lemma F_671b0 : fetch_word Asan.M.loaded_segments (0x671b0 : word) = Some W_671b0.
Proof. vm_refl. Qed.
Lemma D_671b0 : decode_any W_671b0 = Some (Jal 1 54744, 4%Z).
Proof. vm_refl. Qed.

Definition W_671b4 : bv 32 := 0x0540006f.
Lemma F_671b4 : fetch_word Asan.M.loaded_segments (0x671b4 : word) = Some W_671b4.
Proof. vm_refl. Qed.
Lemma D_671b4 : decode_any W_671b4 = Some (Jal 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_671b8 : bv 32 := 0x00813823.
Lemma F_671b8 : fetch_word Asan.M.loaded_segments (0x671b8 : word) = Some W_671b8.
Proof. vm_refl. Qed.
Lemma D_671b8 : decode_any W_671b8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_671bc : bv 32 := 0x00813423.
Lemma F_671bc : fetch_word Asan.M.loaded_segments (0x671bc : word) = Some W_671bc.
Proof. vm_refl. Qed.
Lemma D_671bc : decode_any W_671bc = Some (Store SZ8 2 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_671c0 : bv 32 := 0x02010593.
Lemma F_671c0 : fetch_word Asan.M.loaded_segments (0x671c0 : word) = Some W_671c0.
Proof. vm_refl. Qed.
Lemma D_671c0 : decode_any W_671c0 = Some (OpImm ALU_ADD 11 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_671c4 : bv 32 := 0x01810613.
Lemma F_671c4 : fetch_word Asan.M.loaded_segments (0x671c4 : word) = Some W_671c4.
Proof. vm_refl. Qed.
Lemma D_671c4 : decode_any W_671c4 = Some (OpImm ALU_ADD 12 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_671c8 : bv 32 := 0x01010693.
Lemma F_671c8 : fetch_word Asan.M.loaded_segments (0x671c8 : word) = Some W_671c8.
Proof. vm_refl. Qed.
Lemma D_671c8 : decode_any W_671c8 = Some (OpImm ALU_ADD 13 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_671cc : bv 32 := 0x00810713.
Lemma F_671cc : fetch_word Asan.M.loaded_segments (0x671cc : word) = Some W_671cc.
Proof. vm_refl. Qed.
Lemma D_671cc : decode_any W_671cc = Some (OpImm ALU_ADD 14 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_671d0 : bv 32 := 0x180130ef.
Lemma F_671d0 : fetch_word Asan.M.loaded_segments (0x671d0 : word) = Some W_671d0.
Proof. vm_refl. Qed.
Lemma D_671d0 : decode_any W_671d0 = Some (Jal 1 78208, 4%Z).
Proof. vm_refl. Qed.

Definition W_671d4 : bv 32 := 0x02013683.
Lemma F_671d4 : fetch_word Asan.M.loaded_segments (0x671d4 : word) = Some W_671d4.
Proof. vm_refl. Qed.
Lemma D_671d4 : decode_any W_671d4 = Some (Load SZ8 true 13 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_671d8 : bv 32 := 0x01813603.
Lemma F_671d8 : fetch_word Asan.M.loaded_segments (0x671d8 : word) = Some W_671d8.
Proof. vm_refl. Qed.
Lemma D_671d8 : decode_any W_671d8 = Some (Load SZ8 true 12 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_671dc : bv 32 := 0x40d60733.
Lemma F_671dc : fetch_word Asan.M.loaded_segments (0x671dc : word) = Some W_671dc.
Proof. vm_refl. Qed.
Lemma D_671dc : decode_any W_671dc = Some (Op ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_671e0 : bv 32 := 0x04000537.
Lemma F_671e0 : fetch_word Asan.M.loaded_segments (0x671e0 : word) = Some W_671e0.
Proof. vm_refl. Qed.
Lemma D_671e0 : decode_any W_671e0 = Some (Lui 10 16384, 4%Z).
Proof. vm_refl. Qed.

Definition W_671e4 : bv 32 := 0x0015051b.
Lemma F_671e4 : fetch_word Asan.M.loaded_segments (0x671e4 : word) = Some W_671e4.
Proof. vm_refl. Qed.
Lemma D_671e4 : decode_any W_671e4 = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_671e8 : bv 32 := 0xfaa772e3.
Lemma F_671e8 : fetch_word Asan.M.loaded_segments (0x671e8 : word) = Some W_671e8.
Proof. vm_refl. Qed.
Lemma D_671e8 : decode_any W_671e8 = Some (Branch BC_GEU 14 10 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_671ec : bv 32 := 0x00770713.
Lemma F_671ec : fetch_word Asan.M.loaded_segments (0x671ec : word) = Some W_671ec.
Proof. vm_refl. Qed.
Lemma D_671ec : decode_any W_671ec = Some (OpImm ALU_ADD 14 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_671f0 : bv 32 := 0x10000537.
Lemma F_671f0 : fetch_word Asan.M.loaded_segments (0x671f0 : word) = Some W_671f0.
Proof. vm_refl. Qed.
Lemma D_671f0 : decode_any W_671f0 = Some (Lui 10 65536, 4%Z).
Proof. vm_refl. Qed.

Definition W_671f4 : bv 32 := 0xff85051b.
Lemma F_671f4 : fetch_word Asan.M.loaded_segments (0x671f4 : word) = Some W_671f4.
Proof. vm_refl. Qed.
Lemma D_671f4 : decode_any W_671f4 = Some (OpImm32 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_671f8 : bv 32 := 0x00a775b3.
Lemma F_671f8 : fetch_word Asan.M.loaded_segments (0x671f8 : word) = Some W_671f8.
Proof. vm_refl. Qed.
Lemma D_671f8 : decode_any W_671f8 = Some (Op ALU_AND 11 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_671fc : bv 32 := 0x00068513.
Lemma F_671fc : fetch_word Asan.M.loaded_segments (0x671fc : word) = Some W_671fc.
Proof. vm_refl. Qed.
Lemma D_671fc : decode_any W_671fc = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67200 : bv 32 := 0x00000613.
Lemma F_67200 : fetch_word Asan.M.loaded_segments (0x67200 : word) = Some W_67200.
Proof. vm_refl. Qed.
Lemma D_67200 : decode_any W_67200 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67204 : bv 32 := 0xd75f90ef.
Lemma F_67204 : fetch_word Asan.M.loaded_segments (0x67204 : word) = Some W_67204.
Proof. vm_refl. Qed.
Lemma D_67204 : decode_any W_67204 = Some (Jal 1 2071924, 4%Z).
Proof. vm_refl. Qed.

Definition W_67208 : bv 32 := 0x5dc020ef.
Lemma F_67208 : fetch_word Asan.M.loaded_segments (0x67208 : word) = Some W_67208.
Proof. vm_refl. Qed.
Lemma D_67208 : decode_any W_67208 = Some (Jal 1 9692, 4%Z).
Proof. vm_refl. Qed.

Definition W_6720c : bv 32 := 0x02050263.
Lemma F_6720c : fetch_word Asan.M.loaded_segments (0x6720c : word) = Some W_6720c.
Proof. vm_refl. Qed.
Lemma D_6720c : decode_any W_6720c = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_67210 : bv 32 := 0x02850583.
Lemma F_67210 : fetch_word Asan.M.loaded_segments (0x67210 : word) = Some W_67210.
Proof. vm_refl. Qed.
Lemma D_67210 : decode_any W_67210 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_67214 : bv 32 := 0x00059e63.
Lemma F_67214 : fetch_word Asan.M.loaded_segments (0x67214 : word) = Some W_67214.
Proof. vm_refl. Qed.
Lemma D_67214 : decode_any W_67214 = Some (Branch BC_NE 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_67218 : bv 32 := 0x04853503.
Lemma F_67218 : fetch_word Asan.M.loaded_segments (0x67218 : word) = Some W_67218.
Proof. vm_refl. Qed.
Lemma D_67218 : decode_any W_67218 = Some (Load SZ8 true 10 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_6721c : bv 32 := 0x00253593.
Lemma F_6721c : fetch_word Asan.M.loaded_segments (0x6721c : word) = Some W_6721c.
Proof. vm_refl. Qed.
Lemma D_6721c : decode_any W_6721c = Some (OpImm ALU_SLTU 11 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_67220 : bv 32 := 0xfff58593.
Lemma F_67220 : fetch_word Asan.M.loaded_segments (0x67220 : word) = Some W_67220.
Proof. vm_refl. Qed.
Lemma D_67220 : decode_any W_67220 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_67224 : bv 32 := 0x00a5f533.
Lemma F_67224 : fetch_word Asan.M.loaded_segments (0x67224 : word) = Some W_67224.
Proof. vm_refl. Qed.
Lemma D_67224 : decode_any W_67224 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_67228 : bv 32 := 0x00050463.
Lemma F_67228 : fetch_word Asan.M.loaded_segments (0x67228 : word) = Some W_67228.
Proof. vm_refl. Qed.
Lemma D_67228 : decode_any W_67228 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6722c : bv 32 := 0xe28e10ef.
Lemma F_6722c : fetch_word Asan.M.loaded_segments (0x6722c : word) = Some W_6722c.
Proof. vm_refl. Qed.
Lemma D_6722c : decode_any W_6722c = Some (Jal 1 1971752, 4%Z).
Proof. vm_refl. Qed.

Definition W_67230 : bv 32 := 0x04813083.
Lemma F_67230 : fetch_word Asan.M.loaded_segments (0x67230 : word) = Some W_67230.
Proof. vm_refl. Qed.
Lemma D_67230 : decode_any W_67230 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_67234 : bv 32 := 0x04013403.
Lemma F_67234 : fetch_word Asan.M.loaded_segments (0x67234 : word) = Some W_67234.
Proof. vm_refl. Qed.
Lemma D_67234 : decode_any W_67234 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_67238 : bv 32 := 0x03813483.
Lemma F_67238 : fetch_word Asan.M.loaded_segments (0x67238 : word) = Some W_67238.
Proof. vm_refl. Qed.
Lemma D_67238 : decode_any W_67238 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6723c : bv 32 := 0x03013903.
Lemma F_6723c : fetch_word Asan.M.loaded_segments (0x6723c : word) = Some W_6723c.
Proof. vm_refl. Qed.
Lemma D_6723c : decode_any W_6723c = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_67240 : bv 32 := 0x02813983.
Lemma F_67240 : fetch_word Asan.M.loaded_segments (0x67240 : word) = Some W_67240.
Proof. vm_refl. Qed.
Lemma D_67240 : decode_any W_67240 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_67244 : bv 32 := 0x05010113.
Lemma F_67244 : fetch_word Asan.M.loaded_segments (0x67244 : word) = Some W_67244.
Proof. vm_refl. Qed.
Lemma D_67244 : decode_any W_67244 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_67248 : bv 32 := 0x00008067.
Lemma F_67248 : fetch_word Asan.M.loaded_segments (0x67248 : word) = Some W_67248.
Proof. vm_refl. Qed.
Lemma D_67248 : decode_any W_67248 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
