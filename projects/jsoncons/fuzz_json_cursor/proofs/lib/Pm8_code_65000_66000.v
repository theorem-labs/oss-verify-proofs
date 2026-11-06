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

Definition W_65000 : bv 32 := 0x00160613.
Lemma F_65000 : fetch_word Asan.M.loaded_segments (0x65050 : word) = Some W_65000.
Proof. vm_refl. Qed.
Lemma D_65000 : decode_any W_65000 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65004 : bv 32 := 0x00100513.
Lemma F_65004 : fetch_word Asan.M.loaded_segments (0x65054 : word) = Some W_65004.
Proof. vm_refl. Qed.
Lemma D_65004 : decode_any W_65004 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65008 : bv 32 := 0xffb90693.
Lemma F_65008 : fetch_word Asan.M.loaded_segments (0x65058 : word) = Some W_65008.
Proof. vm_refl. Qed.
Lemma D_65008 : decode_any W_65008 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_6500c : bv 32 := 0x00c4bc23.
Lemma F_6500c : fetch_word Asan.M.loaded_segments (0x6505c : word) = Some W_6500c.
Proof. vm_refl. Qed.
Lemma D_6500c : decode_any W_6500c = Some (Store SZ8 9 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65010 : bv 32 := 0x00a78023.
Lemma F_65010 : fetch_word Asan.M.loaded_segments (0x65060 : word) = Some W_65010.
Proof. vm_refl. Qed.
Lemma D_65010 : decode_any W_65010 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65014 : bv 32 := 0x00d51533.
Lemma F_65014 : fetch_word Asan.M.loaded_segments (0x65064 : word) = Some W_65014.
Proof. vm_refl. Qed.
Lemma D_65014 : decode_any W_65014 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_65018 : bv 32 := 0x00300613.
Lemma F_65018 : fetch_word Asan.M.loaded_segments (0x65068 : word) = Some W_65018.
Proof. vm_refl. Qed.
Lemma D_65018 : decode_any W_65018 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6501c : bv 32 := 0x00989893.
Lemma F_6501c : fetch_word Asan.M.loaded_segments (0x6506c : word) = Some W_6501c.
Proof. vm_refl. Qed.
Lemma D_6501c : decode_any W_6501c = Some (ShiftImm ALU_SLL 17 17 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_65020 : bv 32 := 0x01261633.
Lemma F_65020 : fetch_word Asan.M.loaded_segments (0x65070 : word) = Some W_65020.
Proof. vm_refl. Qed.
Lemma D_65020 : decode_any W_65020 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_65024 : bv 32 := 0x00a58533.
Lemma F_65024 : fetch_word Asan.M.loaded_segments (0x65074 : word) = Some W_65024.
Proof. vm_refl. Qed.
Lemma D_65024 : decode_any W_65024 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_65028 : bv 32 := 0x01160633.
Lemma F_65028 : fetch_word Asan.M.loaded_segments (0x65078 : word) = Some W_65028.
Proof. vm_refl. Qed.
Lemma D_65028 : decode_any W_65028 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_6502c : bv 32 := 0x00c504b3.
Lemma F_6502c : fetch_word Asan.M.loaded_segments (0x6507c : word) = Some W_6502c.
Proof. vm_refl. Qed.
Lemma D_6502c : decode_any W_6502c = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_65030 : bv 32 := 0x0084bc23.
Lemma F_65030 : fetch_word Asan.M.loaded_segments (0x65080 : word) = Some W_65030.
Proof. vm_refl. Qed.
Lemma D_65030 : decode_any W_65030 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65034 : bv 32 := 0x1ef4bc23.
Lemma F_65034 : fetch_word Asan.M.loaded_segments (0x65084 : word) = Some W_65034.
Proof. vm_refl. Qed.
Lemma D_65034 : decode_any W_65034 = Some (Store SZ8 9 15 504, 4%Z).
Proof. vm_refl. Qed.

Definition W_65038 : bv 32 := 0x00048513.
Lemma F_65038 : fetch_word Asan.M.loaded_segments (0x65088 : word) = Some W_65038.
Proof. vm_refl. Qed.
Lemma D_65038 : decode_any W_65038 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6503c : bv 32 := 0x4f0000ef.
Lemma F_6503c : fetch_word Asan.M.loaded_segments (0x6508c : word) = Some W_6503c.
Proof. vm_refl. Qed.
Lemma D_6503c : decode_any W_6503c = Some (Jal 1 1264, 4%Z).
Proof. vm_refl. Qed.

Definition W_65040 : bv 32 := 0x00050593.
Lemma F_65040 : fetch_word Asan.M.loaded_segments (0x65090 : word) = Some W_65040.
Proof. vm_refl. Qed.
Lemma D_65040 : decode_any W_65040 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65044 : bv 32 := 0x00048513.
Lemma F_65044 : fetch_word Asan.M.loaded_segments (0x65094 : word) = Some W_65044.
Proof. vm_refl. Qed.
Lemma D_65044 : decode_any W_65044 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65048 : bv 32 := 0x00000613.
Lemma F_65048 : fetch_word Asan.M.loaded_segments (0x65098 : word) = Some W_65048.
Proof. vm_refl. Qed.
Lemma D_65048 : decode_any W_65048 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6504c : bv 32 := 0x0005b023.
Lemma F_6504c : fetch_word Asan.M.loaded_segments (0x6509c : word) = Some W_6504c.
Proof. vm_refl. Qed.
Lemma D_6504c : decode_any W_6504c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65050 : bv 32 := 0x0005b423.
Lemma F_65050 : fetch_word Asan.M.loaded_segments (0x650a0 : word) = Some W_65050.
Proof. vm_refl. Qed.
Lemma D_65050 : decode_any W_65050 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65054 : bv 32 := 0x0005b823.
Lemma F_65054 : fetch_word Asan.M.loaded_segments (0x650a4 : word) = Some W_65054.
Proof. vm_refl. Qed.
Lemma D_65054 : decode_any W_65054 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65058 : bv 32 := 0x0005bc23.
Lemma F_65058 : fetch_word Asan.M.loaded_segments (0x650a8 : word) = Some W_65058.
Proof. vm_refl. Qed.
Lemma D_65058 : decode_any W_65058 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6505c : bv 32 := 0x0205b023.
Lemma F_6505c : fetch_word Asan.M.loaded_segments (0x650ac : word) = Some W_6505c.
Proof. vm_refl. Qed.
Lemma D_6505c : decode_any W_6505c = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65060 : bv 32 := 0x0205b423.
Lemma F_65060 : fetch_word Asan.M.loaded_segments (0x650b0 : word) = Some W_65060.
Proof. vm_refl. Qed.
Lemma D_65060 : decode_any W_65060 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_65064 : bv 32 := 0x0205b823.
Lemma F_65064 : fetch_word Asan.M.loaded_segments (0x650b4 : word) = Some W_65064.
Proof. vm_refl. Qed.
Lemma D_65064 : decode_any W_65064 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_65068 : bv 32 := 0x0205bc23.
Lemma F_65068 : fetch_word Asan.M.loaded_segments (0x650b8 : word) = Some W_65068.
Proof. vm_refl. Qed.
Lemma D_65068 : decode_any W_65068 = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6506c : bv 32 := 0x01813083.
Lemma F_6506c : fetch_word Asan.M.loaded_segments (0x650bc : word) = Some W_6506c.
Proof. vm_refl. Qed.
Lemma D_6506c : decode_any W_6506c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65070 : bv 32 := 0x01013403.
Lemma F_65070 : fetch_word Asan.M.loaded_segments (0x650c0 : word) = Some W_65070.
Proof. vm_refl. Qed.
Lemma D_65070 : decode_any W_65070 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65074 : bv 32 := 0x00813483.
Lemma F_65074 : fetch_word Asan.M.loaded_segments (0x650c4 : word) = Some W_65074.
Proof. vm_refl. Qed.
Lemma D_65074 : decode_any W_65074 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65078 : bv 32 := 0x00013903.
Lemma F_65078 : fetch_word Asan.M.loaded_segments (0x650c8 : word) = Some W_65078.
Proof. vm_refl. Qed.
Lemma D_65078 : decode_any W_65078 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6507c : bv 32 := 0x02010113.
Lemma F_6507c : fetch_word Asan.M.loaded_segments (0x650cc : word) = Some W_6507c.
Proof. vm_refl. Qed.
Lemma D_6507c : decode_any W_6507c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65080 : bv 32 := 0x00008067.
Lemma F_65080 : fetch_word Asan.M.loaded_segments (0x650d0 : word) = Some W_65080.
Proof. vm_refl. Qed.
Lemma D_65080 : decode_any W_65080 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650a0 : bv 32 := 0xfe010113.
Lemma F_650a0 : fetch_word Asan.M.loaded_segments (0x650f0 : word) = Some W_650a0.
Proof. vm_refl. Qed.
Lemma D_650a0 : decode_any W_650a0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_650a4 : bv 32 := 0x00113c23.
Lemma F_650a4 : fetch_word Asan.M.loaded_segments (0x650f4 : word) = Some W_650a4.
Proof. vm_refl. Qed.
Lemma D_650a4 : decode_any W_650a4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_650a8 : bv 32 := 0x00813823.
Lemma F_650a8 : fetch_word Asan.M.loaded_segments (0x650f8 : word) = Some W_650a8.
Proof. vm_refl. Qed.
Lemma D_650a8 : decode_any W_650a8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_650ac : bv 32 := 0x00913423.
Lemma F_650ac : fetch_word Asan.M.loaded_segments (0x650fc : word) = Some W_650ac.
Proof. vm_refl. Qed.
Lemma D_650ac : decode_any W_650ac = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_650b0 : bv 32 := 0x01213023.
Lemma F_650b0 : fetch_word Asan.M.loaded_segments (0x65100 : word) = Some W_650b0.
Proof. vm_refl. Qed.
Lemma D_650b0 : decode_any W_650b0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650b4 : bv 32 := 0x02010413.
Lemma F_650b4 : fetch_word Asan.M.loaded_segments (0x65104 : word) = Some W_650b4.
Proof. vm_refl. Qed.
Lemma D_650b4 : decode_any W_650b4 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_650b8 : bv 32 := 0x000ef517.
Lemma F_650b8 : fetch_word Asan.M.loaded_segments (0x65108 : word) = Some W_650b8.
Proof. vm_refl. Qed.
Lemma D_650b8 : decode_any W_650b8 = Some (Auipc 10 239, 4%Z).
Proof. vm_refl. Qed.

Definition W_650bc : bv 32 := 0xe4050513.
Lemma F_650bc : fetch_word Asan.M.loaded_segments (0x6510c : word) = Some W_650bc.
Proof. vm_refl. Qed.
Lemma D_650bc : decode_any W_650bc = Some (OpImm ALU_ADD 10 10 3648, 4%Z).
Proof. vm_refl. Qed.

Definition W_650c0 : bv 32 := 0x4c0050ef.
Lemma F_650c0 : fetch_word Asan.M.loaded_segments (0x65110 : word) = Some W_650c0.
Proof. vm_refl. Qed.
Lemma D_650c0 : decode_any W_650c0 = Some (Jal 1 21696, 4%Z).
Proof. vm_refl. Qed.

Definition W_650c4 : bv 32 := 0x00053483.
Lemma F_650c4 : fetch_word Asan.M.loaded_segments (0x65114 : word) = Some W_650c4.
Proof. vm_refl. Qed.
Lemma D_650c4 : decode_any W_650c4 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650c8 : bv 32 := 0x08048863.
Lemma F_650c8 : fetch_word Asan.M.loaded_segments (0x65118 : word) = Some W_650c8.
Proof. vm_refl. Qed.
Lemma D_650c8 : decode_any W_650c8 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_650cc : bv 32 := 0x0604c503.
Lemma F_650cc : fetch_word Asan.M.loaded_segments (0x6511c : word) = Some W_650cc.
Proof. vm_refl. Qed.
Lemma D_650cc : decode_any W_650cc = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_650d0 : bv 32 := 0x0584b903.
Lemma F_650d0 : fetch_word Asan.M.loaded_segments (0x65120 : word) = Some W_650d0.
Proof. vm_refl. Qed.
Lemma D_650d0 : decode_any W_650d0 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_650d4 : bv 32 := 0x00050863.
Lemma F_650d4 : fetch_word Asan.M.loaded_segments (0x65124 : word) = Some W_650d4.
Proof. vm_refl. Qed.
Lemma D_650d4 : decode_any W_650d4 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_650d8 : bv 32 := 0x00048513.
Lemma F_650d8 : fetch_word Asan.M.loaded_segments (0x65128 : word) = Some W_650d8.
Proof. vm_refl. Qed.
Lemma D_650d8 : decode_any W_650d8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650dc : bv 32 := 0x00040593.
Lemma F_650dc : fetch_word Asan.M.loaded_segments (0x6512c : word) = Some W_650dc.
Proof. vm_refl. Qed.
Lemma D_650dc : decode_any W_650dc = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650e0 : bv 32 := 0xd28ff0ef.
Lemma F_650e0 : fetch_word Asan.M.loaded_segments (0x65130 : word) = Some W_650e0.
Proof. vm_refl. Qed.
Lemma D_650e0 : decode_any W_650e0 = Some (Jal 1 2094376, 4%Z).
Proof. vm_refl. Qed.

Definition W_650e4 : bv 32 := 0xff690593.
Lemma F_650e4 : fetch_word Asan.M.loaded_segments (0x65134 : word) = Some W_650e4.
Proof. vm_refl. Qed.
Lemma D_650e4 : decode_any W_650e4 = Some (OpImm ALU_ADD 11 18 4086, 4%Z).
Proof. vm_refl. Qed.

Definition W_650e8 : bv 32 := 0x00100513.
Lemma F_650e8 : fetch_word Asan.M.loaded_segments (0x65138 : word) = Some W_650e8.
Proof. vm_refl. Qed.
Lemma D_650e8 : decode_any W_650e8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_650ec : bv 32 := 0x00b51533.
Lemma F_650ec : fetch_word Asan.M.loaded_segments (0x6513c : word) = Some W_650ec.
Proof. vm_refl. Qed.
Lemma D_650ec : decode_any W_650ec = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_650f0 : bv 32 := 0x0005061b.
Lemma F_650f0 : fetch_word Asan.M.loaded_segments (0x65140 : word) = Some W_650f0.
Proof. vm_refl. Qed.
Lemma D_650f0 : decode_any W_650f0 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650f4 : bv 32 := 0x08c05263.
Lemma F_650f4 : fetch_word Asan.M.loaded_segments (0x65144 : word) = Some W_650f4.
Proof. vm_refl. Qed.
Lemma D_650f4 : decode_any W_650f4 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_650f8 : bv 32 := 0x000016b7.
Lemma F_650f8 : fetch_word Asan.M.loaded_segments (0x65148 : word) = Some W_650f8.
Proof. vm_refl. Qed.
Lemma D_650f8 : decode_any W_650f8 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_650fc : bv 32 := 0xff190613.
Lemma F_650fc : fetch_word Asan.M.loaded_segments (0x6514c : word) = Some W_650fc.
Proof. vm_refl. Qed.
Lemma D_650fc : decode_any W_650fc = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_65100 : bv 32 := 0x3c000713.
Lemma F_65100 : fetch_word Asan.M.loaded_segments (0x65150 : word) = Some W_65100.
Proof. vm_refl. Qed.
Lemma D_65100 : decode_any W_65100 = Some (OpImm ALU_ADD 14 0 960, 4%Z).
Proof. vm_refl. Qed.

Definition W_65104 : bv 32 := 0xfff00793.
Lemma F_65104 : fetch_word Asan.M.loaded_segments (0x65154 : word) = Some W_65104.
Proof. vm_refl. Qed.
Lemma D_65104 : decode_any W_65104 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65108 : bv 32 := 0x00c71733.
Lemma F_65108 : fetch_word Asan.M.loaded_segments (0x65158 : word) = Some W_65108.
Proof. vm_refl. Qed.
Lemma D_65108 : decode_any W_65108 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6510c : bv 32 := 0x0204b603.
Lemma F_6510c : fetch_word Asan.M.loaded_segments (0x6515c : word) = Some W_6510c.
Proof. vm_refl. Qed.
Lemma D_6510c : decode_any W_6510c = Some (Load SZ8 true 12 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65110 : bv 32 := 0x00b797b3.
Lemma F_65110 : fetch_word Asan.M.loaded_segments (0x65160 : word) = Some W_65110.
Proof. vm_refl. Qed.
Lemma D_65110 : decode_any W_65110 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_65114 : bv 32 := 0xfff50813.
Lemma F_65114 : fetch_word Asan.M.loaded_segments (0x65164 : word) = Some W_65114.
Proof. vm_refl. Qed.
Lemma D_65114 : decode_any W_65114 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65118 : bv 32 := 0x00d485b3.
Lemma F_65118 : fetch_word Asan.M.loaded_segments (0x65168 : word) = Some W_65118.
Proof. vm_refl. Qed.
Lemma D_65118 : decode_any W_65118 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6511c : bv 32 := 0x00e586b3.
Lemma F_6511c : fetch_word Asan.M.loaded_segments (0x6516c : word) = Some W_6511c.
Proof. vm_refl. Qed.
Lemma D_6511c : decode_any W_6511c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_65120 : bv 32 := 0xfff7c713.
Lemma F_65120 : fetch_word Asan.M.loaded_segments (0x65170 : word) = Some W_65120.
Proof. vm_refl. Qed.
Lemma D_65120 : decode_any W_65120 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65124 : bv 32 := 0x02081813.
Lemma F_65124 : fetch_word Asan.M.loaded_segments (0x65174 : word) = Some W_65124.
Proof. vm_refl. Qed.
Lemma D_65124 : decode_any W_65124 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65128 : bv 32 := 0x02085793.
Lemma F_65128 : fetch_word Asan.M.loaded_segments (0x65178 : word) = Some W_65128.
Proof. vm_refl. Qed.
Lemma D_65128 : decode_any W_65128 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6512c : bv 32 := 0x00f607b3.
Lemma F_6512c : fetch_word Asan.M.loaded_segments (0x6517c : word) = Some W_6512c.
Proof. vm_refl. Qed.
Lemma D_6512c : decode_any W_6512c = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_65130 : bv 32 := 0x00178813.
Lemma F_65130 : fetch_word Asan.M.loaded_segments (0x65180 : word) = Some W_65130.
Proof. vm_refl. Qed.
Lemma D_65130 : decode_any W_65130 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65134 : bv 32 := 0x00e678b3.
Lemma F_65134 : fetch_word Asan.M.loaded_segments (0x65184 : word) = Some W_65134.
Proof. vm_refl. Qed.
Lemma D_65134 : decode_any W_65134 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_65138 : bv 32 := 0x011687b3.
Lemma F_65138 : fetch_word Asan.M.loaded_segments (0x65188 : word) = Some W_65138.
Proof. vm_refl. Qed.
Lemma D_65138 : decode_any W_65138 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_6513c : bv 32 := 0x0007c283.
Lemma F_6513c : fetch_word Asan.M.loaded_segments (0x6518c : word) = Some W_6513c.
Proof. vm_refl. Qed.
Lemma D_6513c : decode_any W_6513c = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65140 : bv 32 := 0x06028663.
Lemma F_65140 : fetch_word Asan.M.loaded_segments (0x65190 : word) = Some W_65140.
Proof. vm_refl. Qed.
Lemma D_65140 : decode_any W_65140 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_65144 : bv 32 := 0xfff5051b.
Lemma F_65144 : fetch_word Asan.M.loaded_segments (0x65194 : word) = Some W_65144.
Proof. vm_refl. Qed.
Lemma D_65144 : decode_any W_65144 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65148 : bv 32 := 0x00160613.
Lemma F_65148 : fetch_word Asan.M.loaded_segments (0x65198 : word) = Some W_65148.
Proof. vm_refl. Qed.
Lemma D_65148 : decode_any W_65148 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6514c : bv 32 := 0xfe0514e3.
Lemma F_6514c : fetch_word Asan.M.loaded_segments (0x6519c : word) = Some W_6514c.
Proof. vm_refl. Qed.
Lemma D_6514c : decode_any W_6514c = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_651ac : bv 32 := 0x00160613.
Lemma F_651ac : fetch_word Asan.M.loaded_segments (0x651fc : word) = Some W_651ac.
Proof. vm_refl. Qed.
Lemma D_651ac : decode_any W_651ac = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_651b0 : bv 32 := 0x00100513.
Lemma F_651b0 : fetch_word Asan.M.loaded_segments (0x65200 : word) = Some W_651b0.
Proof. vm_refl. Qed.
Lemma D_651b0 : decode_any W_651b0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_651b4 : bv 32 := 0xffb90693.
Lemma F_651b4 : fetch_word Asan.M.loaded_segments (0x65204 : word) = Some W_651b4.
Proof. vm_refl. Qed.
Lemma D_651b4 : decode_any W_651b4 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_651b8 : bv 32 := 0x02c4b023.
Lemma F_651b8 : fetch_word Asan.M.loaded_segments (0x65208 : word) = Some W_651b8.
Proof. vm_refl. Qed.
Lemma D_651b8 : decode_any W_651b8 = Some (Store SZ8 9 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_651bc : bv 32 := 0x00a78023.
Lemma F_651bc : fetch_word Asan.M.loaded_segments (0x6520c : word) = Some W_651bc.
Proof. vm_refl. Qed.
Lemma D_651bc : decode_any W_651bc = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_651c0 : bv 32 := 0x00d51533.
Lemma F_651c0 : fetch_word Asan.M.loaded_segments (0x65210 : word) = Some W_651c0.
Proof. vm_refl. Qed.
Lemma D_651c0 : decode_any W_651c0 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_651c4 : bv 32 := 0x00400613.
Lemma F_651c4 : fetch_word Asan.M.loaded_segments (0x65214 : word) = Some W_651c4.
Proof. vm_refl. Qed.
Lemma D_651c4 : decode_any W_651c4 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_651c8 : bv 32 := 0x00a89893.
Lemma F_651c8 : fetch_word Asan.M.loaded_segments (0x65218 : word) = Some W_651c8.
Proof. vm_refl. Qed.
Lemma D_651c8 : decode_any W_651c8 = Some (ShiftImm ALU_SLL 17 17 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_651cc : bv 32 := 0x01261633.
Lemma F_651cc : fetch_word Asan.M.loaded_segments (0x6521c : word) = Some W_651cc.
Proof. vm_refl. Qed.
Lemma D_651cc : decode_any W_651cc = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_651d0 : bv 32 := 0x00a58533.
Lemma F_651d0 : fetch_word Asan.M.loaded_segments (0x65220 : word) = Some W_651d0.
Proof. vm_refl. Qed.
Lemma D_651d0 : decode_any W_651d0 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_651d4 : bv 32 := 0x01160633.
Lemma F_651d4 : fetch_word Asan.M.loaded_segments (0x65224 : word) = Some W_651d4.
Proof. vm_refl. Qed.
Lemma D_651d4 : decode_any W_651d4 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_651d8 : bv 32 := 0x00c504b3.
Lemma F_651d8 : fetch_word Asan.M.loaded_segments (0x65228 : word) = Some W_651d8.
Proof. vm_refl. Qed.
Lemma D_651d8 : decode_any W_651d8 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_651dc : bv 32 := 0x0084bc23.
Lemma F_651dc : fetch_word Asan.M.loaded_segments (0x6522c : word) = Some W_651dc.
Proof. vm_refl. Qed.
Lemma D_651dc : decode_any W_651dc = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_651e0 : bv 32 := 0x3ef4bc23.
Lemma F_651e0 : fetch_word Asan.M.loaded_segments (0x65230 : word) = Some W_651e0.
Proof. vm_refl. Qed.
Lemma D_651e0 : decode_any W_651e0 = Some (Store SZ8 9 15 1016, 4%Z).
Proof. vm_refl. Qed.

Definition W_651e4 : bv 32 := 0x00048513.
Lemma F_651e4 : fetch_word Asan.M.loaded_segments (0x65234 : word) = Some W_651e4.
Proof. vm_refl. Qed.
Lemma D_651e4 : decode_any W_651e4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_651e8 : bv 32 := 0x344000ef.
Lemma F_651e8 : fetch_word Asan.M.loaded_segments (0x65238 : word) = Some W_651e8.
Proof. vm_refl. Qed.
Lemma D_651e8 : decode_any W_651e8 = Some (Jal 1 836, 4%Z).
Proof. vm_refl. Qed.

Definition W_651ec : bv 32 := 0x00050593.
Lemma F_651ec : fetch_word Asan.M.loaded_segments (0x6523c : word) = Some W_651ec.
Proof. vm_refl. Qed.
Lemma D_651ec : decode_any W_651ec = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_651f0 : bv 32 := 0x00048513.
Lemma F_651f0 : fetch_word Asan.M.loaded_segments (0x65240 : word) = Some W_651f0.
Proof. vm_refl. Qed.
Lemma D_651f0 : decode_any W_651f0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_651f4 : bv 32 := 0x00000613.
Lemma F_651f4 : fetch_word Asan.M.loaded_segments (0x65244 : word) = Some W_651f4.
Proof. vm_refl. Qed.
Lemma D_651f4 : decode_any W_651f4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_651f8 : bv 32 := 0x0005b023.
Lemma F_651f8 : fetch_word Asan.M.loaded_segments (0x65248 : word) = Some W_651f8.
Proof. vm_refl. Qed.
Lemma D_651f8 : decode_any W_651f8 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_651fc : bv 32 := 0x0005b423.
Lemma F_651fc : fetch_word Asan.M.loaded_segments (0x6524c : word) = Some W_651fc.
Proof. vm_refl. Qed.
Lemma D_651fc : decode_any W_651fc = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65200 : bv 32 := 0x0005b823.
Lemma F_65200 : fetch_word Asan.M.loaded_segments (0x65250 : word) = Some W_65200.
Proof. vm_refl. Qed.
Lemma D_65200 : decode_any W_65200 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65204 : bv 32 := 0x0005bc23.
Lemma F_65204 : fetch_word Asan.M.loaded_segments (0x65254 : word) = Some W_65204.
Proof. vm_refl. Qed.
Lemma D_65204 : decode_any W_65204 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65208 : bv 32 := 0x0205b023.
Lemma F_65208 : fetch_word Asan.M.loaded_segments (0x65258 : word) = Some W_65208.
Proof. vm_refl. Qed.
Lemma D_65208 : decode_any W_65208 = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6520c : bv 32 := 0x0205b423.
Lemma F_6520c : fetch_word Asan.M.loaded_segments (0x6525c : word) = Some W_6520c.
Proof. vm_refl. Qed.
Lemma D_6520c : decode_any W_6520c = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_65210 : bv 32 := 0x0205b823.
Lemma F_65210 : fetch_word Asan.M.loaded_segments (0x65260 : word) = Some W_65210.
Proof. vm_refl. Qed.
Lemma D_65210 : decode_any W_65210 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_65214 : bv 32 := 0x0205bc23.
Lemma F_65214 : fetch_word Asan.M.loaded_segments (0x65264 : word) = Some W_65214.
Proof. vm_refl. Qed.
Lemma D_65214 : decode_any W_65214 = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_65218 : bv 32 := 0x0405b023.
Lemma F_65218 : fetch_word Asan.M.loaded_segments (0x65268 : word) = Some W_65218.
Proof. vm_refl. Qed.
Lemma D_65218 : decode_any W_65218 = Some (Store SZ8 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6521c : bv 32 := 0x0405b423.
Lemma F_6521c : fetch_word Asan.M.loaded_segments (0x6526c : word) = Some W_6521c.
Proof. vm_refl. Qed.
Lemma D_6521c : decode_any W_6521c = Some (Store SZ8 11 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_65220 : bv 32 := 0x0405b823.
Lemma F_65220 : fetch_word Asan.M.loaded_segments (0x65270 : word) = Some W_65220.
Proof. vm_refl. Qed.
Lemma D_65220 : decode_any W_65220 = Some (Store SZ8 11 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_65224 : bv 32 := 0x0405bc23.
Lemma F_65224 : fetch_word Asan.M.loaded_segments (0x65274 : word) = Some W_65224.
Proof. vm_refl. Qed.
Lemma D_65224 : decode_any W_65224 = Some (Store SZ8 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_65228 : bv 32 := 0x0605b023.
Lemma F_65228 : fetch_word Asan.M.loaded_segments (0x65278 : word) = Some W_65228.
Proof. vm_refl. Qed.
Lemma D_65228 : decode_any W_65228 = Some (Store SZ8 11 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6522c : bv 32 := 0x0605b423.
Lemma F_6522c : fetch_word Asan.M.loaded_segments (0x6527c : word) = Some W_6522c.
Proof. vm_refl. Qed.
Lemma D_6522c : decode_any W_6522c = Some (Store SZ8 11 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_65230 : bv 32 := 0x0605b823.
Lemma F_65230 : fetch_word Asan.M.loaded_segments (0x65280 : word) = Some W_65230.
Proof. vm_refl. Qed.
Lemma D_65230 : decode_any W_65230 = Some (Store SZ8 11 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_65234 : bv 32 := 0x0605bc23.
Lemma F_65234 : fetch_word Asan.M.loaded_segments (0x65284 : word) = Some W_65234.
Proof. vm_refl. Qed.
Lemma D_65234 : decode_any W_65234 = Some (Store SZ8 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_65238 : bv 32 := 0x01813083.
Lemma F_65238 : fetch_word Asan.M.loaded_segments (0x65288 : word) = Some W_65238.
Proof. vm_refl. Qed.
Lemma D_65238 : decode_any W_65238 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6523c : bv 32 := 0x01013403.
Lemma F_6523c : fetch_word Asan.M.loaded_segments (0x6528c : word) = Some W_6523c.
Proof. vm_refl. Qed.
Lemma D_6523c : decode_any W_6523c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65240 : bv 32 := 0x00813483.
Lemma F_65240 : fetch_word Asan.M.loaded_segments (0x65290 : word) = Some W_65240.
Proof. vm_refl. Qed.
Lemma D_65240 : decode_any W_65240 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65244 : bv 32 := 0x00013903.
Lemma F_65244 : fetch_word Asan.M.loaded_segments (0x65294 : word) = Some W_65244.
Proof. vm_refl. Qed.
Lemma D_65244 : decode_any W_65244 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65248 : bv 32 := 0x02010113.
Lemma F_65248 : fetch_word Asan.M.loaded_segments (0x65298 : word) = Some W_65248.
Proof. vm_refl. Qed.
Lemma D_65248 : decode_any W_65248 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6524c : bv 32 := 0x00008067.
Lemma F_6524c : fetch_word Asan.M.loaded_segments (0x6529c : word) = Some W_6524c.
Proof. vm_refl. Qed.
Lemma D_6524c : decode_any W_6524c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6526c : bv 32 := 0xfe010113.
Lemma F_6526c : fetch_word Asan.M.loaded_segments (0x652bc : word) = Some W_6526c.
Proof. vm_refl. Qed.
Lemma D_6526c : decode_any W_6526c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_65270 : bv 32 := 0x00113c23.
Lemma F_65270 : fetch_word Asan.M.loaded_segments (0x652c0 : word) = Some W_65270.
Proof. vm_refl. Qed.
Lemma D_65270 : decode_any W_65270 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65274 : bv 32 := 0x00813823.
Lemma F_65274 : fetch_word Asan.M.loaded_segments (0x652c4 : word) = Some W_65274.
Proof. vm_refl. Qed.
Lemma D_65274 : decode_any W_65274 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65278 : bv 32 := 0x00913423.
Lemma F_65278 : fetch_word Asan.M.loaded_segments (0x652c8 : word) = Some W_65278.
Proof. vm_refl. Qed.
Lemma D_65278 : decode_any W_65278 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6527c : bv 32 := 0x01213023.
Lemma F_6527c : fetch_word Asan.M.loaded_segments (0x652cc : word) = Some W_6527c.
Proof. vm_refl. Qed.
Lemma D_6527c : decode_any W_6527c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65280 : bv 32 := 0x02010413.
Lemma F_65280 : fetch_word Asan.M.loaded_segments (0x652d0 : word) = Some W_65280.
Proof. vm_refl. Qed.
Lemma D_65280 : decode_any W_65280 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65284 : bv 32 := 0x000ef517.
Lemma F_65284 : fetch_word Asan.M.loaded_segments (0x652d4 : word) = Some W_65284.
Proof. vm_refl. Qed.
Lemma D_65284 : decode_any W_65284 = Some (Auipc 10 239, 4%Z).
Proof. vm_refl. Qed.

Definition W_65288 : bv 32 := 0xc7450513.
Lemma F_65288 : fetch_word Asan.M.loaded_segments (0x652d8 : word) = Some W_65288.
Proof. vm_refl. Qed.
Lemma D_65288 : decode_any W_65288 = Some (OpImm ALU_ADD 10 10 3188, 4%Z).
Proof. vm_refl. Qed.

Definition W_6528c : bv 32 := 0x2f4050ef.
Lemma F_6528c : fetch_word Asan.M.loaded_segments (0x652dc : word) = Some W_6528c.
Proof. vm_refl. Qed.
Lemma D_6528c : decode_any W_6528c = Some (Jal 1 21236, 4%Z).
Proof. vm_refl. Qed.

Definition W_65290 : bv 32 := 0x00053483.
Lemma F_65290 : fetch_word Asan.M.loaded_segments (0x652e0 : word) = Some W_65290.
Proof. vm_refl. Qed.
Lemma D_65290 : decode_any W_65290 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65294 : bv 32 := 0x08048863.
Lemma F_65294 : fetch_word Asan.M.loaded_segments (0x652e4 : word) = Some W_65294.
Proof. vm_refl. Qed.
Lemma D_65294 : decode_any W_65294 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_65298 : bv 32 := 0x0604c503.
Lemma F_65298 : fetch_word Asan.M.loaded_segments (0x652e8 : word) = Some W_65298.
Proof. vm_refl. Qed.
Lemma D_65298 : decode_any W_65298 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6529c : bv 32 := 0x0584b903.
Lemma F_6529c : fetch_word Asan.M.loaded_segments (0x652ec : word) = Some W_6529c.
Proof. vm_refl. Qed.
Lemma D_6529c : decode_any W_6529c = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_652a0 : bv 32 := 0x00050863.
Lemma F_652a0 : fetch_word Asan.M.loaded_segments (0x652f0 : word) = Some W_652a0.
Proof. vm_refl. Qed.
Lemma D_652a0 : decode_any W_652a0 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_652a4 : bv 32 := 0x00048513.
Lemma F_652a4 : fetch_word Asan.M.loaded_segments (0x652f4 : word) = Some W_652a4.
Proof. vm_refl. Qed.
Lemma D_652a4 : decode_any W_652a4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_652a8 : bv 32 := 0x00040593.
Lemma F_652a8 : fetch_word Asan.M.loaded_segments (0x652f8 : word) = Some W_652a8.
Proof. vm_refl. Qed.
Lemma D_652a8 : decode_any W_652a8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_652ac : bv 32 := 0xb5cff0ef.
Lemma F_652ac : fetch_word Asan.M.loaded_segments (0x652fc : word) = Some W_652ac.
Proof. vm_refl. Qed.
Lemma D_652ac : decode_any W_652ac = Some (Jal 1 2093916, 4%Z).
Proof. vm_refl. Qed.

Definition W_652b0 : bv 32 := 0xff590593.
Lemma F_652b0 : fetch_word Asan.M.loaded_segments (0x65300 : word) = Some W_652b0.
Proof. vm_refl. Qed.
Lemma D_652b0 : decode_any W_652b0 = Some (OpImm ALU_ADD 11 18 4085, 4%Z).
Proof. vm_refl. Qed.

Definition W_652b4 : bv 32 := 0x00100513.
Lemma F_652b4 : fetch_word Asan.M.loaded_segments (0x65304 : word) = Some W_652b4.
Proof. vm_refl. Qed.
Lemma D_652b4 : decode_any W_652b4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_652b8 : bv 32 := 0x00b51533.
Lemma F_652b8 : fetch_word Asan.M.loaded_segments (0x65308 : word) = Some W_652b8.
Proof. vm_refl. Qed.
Lemma D_652b8 : decode_any W_652b8 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_652bc : bv 32 := 0x0005061b.
Lemma F_652bc : fetch_word Asan.M.loaded_segments (0x6530c : word) = Some W_652bc.
Proof. vm_refl. Qed.
Lemma D_652bc : decode_any W_652bc = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_652c0 : bv 32 := 0x08c05263.
Lemma F_652c0 : fetch_word Asan.M.loaded_segments (0x65310 : word) = Some W_652c0.
Proof. vm_refl. Qed.
Lemma D_652c0 : decode_any W_652c0 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_652c4 : bv 32 := 0x000016b7.
Lemma F_652c4 : fetch_word Asan.M.loaded_segments (0x65314 : word) = Some W_652c4.
Proof. vm_refl. Qed.
Lemma D_652c4 : decode_any W_652c4 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_652c8 : bv 32 := 0xff190613.
Lemma F_652c8 : fetch_word Asan.M.loaded_segments (0x65318 : word) = Some W_652c8.
Proof. vm_refl. Qed.
Lemma D_652c8 : decode_any W_652c8 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_652cc : bv 32 := 0x3e000713.
Lemma F_652cc : fetch_word Asan.M.loaded_segments (0x6531c : word) = Some W_652cc.
Proof. vm_refl. Qed.
Lemma D_652cc : decode_any W_652cc = Some (OpImm ALU_ADD 14 0 992, 4%Z).
Proof. vm_refl. Qed.

Definition W_652d0 : bv 32 := 0xfff00793.
Lemma F_652d0 : fetch_word Asan.M.loaded_segments (0x65320 : word) = Some W_652d0.
Proof. vm_refl. Qed.
Lemma D_652d0 : decode_any W_652d0 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_652d4 : bv 32 := 0x00c71733.
Lemma F_652d4 : fetch_word Asan.M.loaded_segments (0x65324 : word) = Some W_652d4.
Proof. vm_refl. Qed.
Lemma D_652d4 : decode_any W_652d4 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_652d8 : bv 32 := 0x0284b603.
Lemma F_652d8 : fetch_word Asan.M.loaded_segments (0x65328 : word) = Some W_652d8.
Proof. vm_refl. Qed.
Lemma D_652d8 : decode_any W_652d8 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_652dc : bv 32 := 0x00b797b3.
Lemma F_652dc : fetch_word Asan.M.loaded_segments (0x6532c : word) = Some W_652dc.
Proof. vm_refl. Qed.
Lemma D_652dc : decode_any W_652dc = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_652e0 : bv 32 := 0xfff50813.
Lemma F_652e0 : fetch_word Asan.M.loaded_segments (0x65330 : word) = Some W_652e0.
Proof. vm_refl. Qed.
Lemma D_652e0 : decode_any W_652e0 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_652e4 : bv 32 := 0x00d485b3.
Lemma F_652e4 : fetch_word Asan.M.loaded_segments (0x65334 : word) = Some W_652e4.
Proof. vm_refl. Qed.
Lemma D_652e4 : decode_any W_652e4 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_652e8 : bv 32 := 0x00e586b3.
Lemma F_652e8 : fetch_word Asan.M.loaded_segments (0x65338 : word) = Some W_652e8.
Proof. vm_refl. Qed.
Lemma D_652e8 : decode_any W_652e8 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_652ec : bv 32 := 0xfff7c713.
Lemma F_652ec : fetch_word Asan.M.loaded_segments (0x6533c : word) = Some W_652ec.
Proof. vm_refl. Qed.
Lemma D_652ec : decode_any W_652ec = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_652f0 : bv 32 := 0x02081813.
Lemma F_652f0 : fetch_word Asan.M.loaded_segments (0x65340 : word) = Some W_652f0.
Proof. vm_refl. Qed.
Lemma D_652f0 : decode_any W_652f0 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_652f4 : bv 32 := 0x02085793.
Lemma F_652f4 : fetch_word Asan.M.loaded_segments (0x65344 : word) = Some W_652f4.
Proof. vm_refl. Qed.
Lemma D_652f4 : decode_any W_652f4 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_652f8 : bv 32 := 0x00f607b3.
Lemma F_652f8 : fetch_word Asan.M.loaded_segments (0x65348 : word) = Some W_652f8.
Proof. vm_refl. Qed.
Lemma D_652f8 : decode_any W_652f8 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_652fc : bv 32 := 0x00178813.
Lemma F_652fc : fetch_word Asan.M.loaded_segments (0x6534c : word) = Some W_652fc.
Proof. vm_refl. Qed.
Lemma D_652fc : decode_any W_652fc = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65300 : bv 32 := 0x00e678b3.
Lemma F_65300 : fetch_word Asan.M.loaded_segments (0x65350 : word) = Some W_65300.
Proof. vm_refl. Qed.
Lemma D_65300 : decode_any W_65300 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_65304 : bv 32 := 0x011687b3.
Lemma F_65304 : fetch_word Asan.M.loaded_segments (0x65354 : word) = Some W_65304.
Proof. vm_refl. Qed.
Lemma D_65304 : decode_any W_65304 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_65308 : bv 32 := 0x0007c283.
Lemma F_65308 : fetch_word Asan.M.loaded_segments (0x65358 : word) = Some W_65308.
Proof. vm_refl. Qed.
Lemma D_65308 : decode_any W_65308 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6530c : bv 32 := 0x06028663.
Lemma F_6530c : fetch_word Asan.M.loaded_segments (0x6535c : word) = Some W_6530c.
Proof. vm_refl. Qed.
Lemma D_6530c : decode_any W_6530c = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_65310 : bv 32 := 0xfff5051b.
Lemma F_65310 : fetch_word Asan.M.loaded_segments (0x65360 : word) = Some W_65310.
Proof. vm_refl. Qed.
Lemma D_65310 : decode_any W_65310 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65314 : bv 32 := 0x00160613.
Lemma F_65314 : fetch_word Asan.M.loaded_segments (0x65364 : word) = Some W_65314.
Proof. vm_refl. Qed.
Lemma D_65314 : decode_any W_65314 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65318 : bv 32 := 0xfe0514e3.
Lemma F_65318 : fetch_word Asan.M.loaded_segments (0x65368 : word) = Some W_65318.
Proof. vm_refl. Qed.
Lemma D_65318 : decode_any W_65318 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_65378 : bv 32 := 0x00160613.
Lemma F_65378 : fetch_word Asan.M.loaded_segments (0x653c8 : word) = Some W_65378.
Proof. vm_refl. Qed.
Lemma D_65378 : decode_any W_65378 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6537c : bv 32 := 0x00100513.
Lemma F_6537c : fetch_word Asan.M.loaded_segments (0x653cc : word) = Some W_6537c.
Proof. vm_refl. Qed.
Lemma D_6537c : decode_any W_6537c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65380 : bv 32 := 0xffb90693.
Lemma F_65380 : fetch_word Asan.M.loaded_segments (0x653d0 : word) = Some W_65380.
Proof. vm_refl. Qed.
Lemma D_65380 : decode_any W_65380 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_65384 : bv 32 := 0x02c4b423.
Lemma F_65384 : fetch_word Asan.M.loaded_segments (0x653d4 : word) = Some W_65384.
Proof. vm_refl. Qed.
Lemma D_65384 : decode_any W_65384 = Some (Store SZ8 9 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_65388 : bv 32 := 0x00a78023.
Lemma F_65388 : fetch_word Asan.M.loaded_segments (0x653d8 : word) = Some W_65388.
Proof. vm_refl. Qed.
Lemma D_65388 : decode_any W_65388 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6538c : bv 32 := 0x00d51533.
Lemma F_6538c : fetch_word Asan.M.loaded_segments (0x653dc : word) = Some W_6538c.
Proof. vm_refl. Qed.
Lemma D_6538c : decode_any W_6538c = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_65390 : bv 32 := 0x00500613.
Lemma F_65390 : fetch_word Asan.M.loaded_segments (0x653e0 : word) = Some W_65390.
Proof. vm_refl. Qed.
Lemma D_65390 : decode_any W_65390 = Some (OpImm ALU_ADD 12 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_65394 : bv 32 := 0x00b89893.
Lemma F_65394 : fetch_word Asan.M.loaded_segments (0x653e4 : word) = Some W_65394.
Proof. vm_refl. Qed.
Lemma D_65394 : decode_any W_65394 = Some (ShiftImm ALU_SLL 17 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_65398 : bv 32 := 0x01261633.
Lemma F_65398 : fetch_word Asan.M.loaded_segments (0x653e8 : word) = Some W_65398.
Proof. vm_refl. Qed.
Lemma D_65398 : decode_any W_65398 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_6539c : bv 32 := 0x00a58533.
Lemma F_6539c : fetch_word Asan.M.loaded_segments (0x653ec : word) = Some W_6539c.
Proof. vm_refl. Qed.
Lemma D_6539c : decode_any W_6539c = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_653a0 : bv 32 := 0x01160633.
Lemma F_653a0 : fetch_word Asan.M.loaded_segments (0x653f0 : word) = Some W_653a0.
Proof. vm_refl. Qed.
Lemma D_653a0 : decode_any W_653a0 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_653a4 : bv 32 := 0x00c504b3.
Lemma F_653a4 : fetch_word Asan.M.loaded_segments (0x653f4 : word) = Some W_653a4.
Proof. vm_refl. Qed.
Lemma D_653a4 : decode_any W_653a4 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_653a8 : bv 32 := 0x0084bc23.
Lemma F_653a8 : fetch_word Asan.M.loaded_segments (0x653f8 : word) = Some W_653a8.
Proof. vm_refl. Qed.
Lemma D_653a8 : decode_any W_653a8 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_653ac : bv 32 := 0x7ef4bc23.
Lemma F_653ac : fetch_word Asan.M.loaded_segments (0x653fc : word) = Some W_653ac.
Proof. vm_refl. Qed.
Lemma D_653ac : decode_any W_653ac = Some (Store SZ8 9 15 2040, 4%Z).
Proof. vm_refl. Qed.

Definition W_653b0 : bv 32 := 0x00048513.
Lemma F_653b0 : fetch_word Asan.M.loaded_segments (0x65400 : word) = Some W_653b0.
Proof. vm_refl. Qed.
Lemma D_653b0 : decode_any W_653b0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_653b4 : bv 32 := 0x178000ef.
Lemma F_653b4 : fetch_word Asan.M.loaded_segments (0x65404 : word) = Some W_653b4.
Proof. vm_refl. Qed.
Lemma D_653b4 : decode_any W_653b4 = Some (Jal 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_653b8 : bv 32 := 0x00050593.
Lemma F_653b8 : fetch_word Asan.M.loaded_segments (0x65408 : word) = Some W_653b8.
Proof. vm_refl. Qed.
Lemma D_653b8 : decode_any W_653b8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_653bc : bv 32 := 0x00048513.
Lemma F_653bc : fetch_word Asan.M.loaded_segments (0x6540c : word) = Some W_653bc.
Proof. vm_refl. Qed.
Lemma D_653bc : decode_any W_653bc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_653c0 : bv 32 := 0x00000613.
Lemma F_653c0 : fetch_word Asan.M.loaded_segments (0x65410 : word) = Some W_653c0.
Proof. vm_refl. Qed.
Lemma D_653c0 : decode_any W_653c0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_653c4 : bv 32 := 0x0005b023.
Lemma F_653c4 : fetch_word Asan.M.loaded_segments (0x65414 : word) = Some W_653c4.
Proof. vm_refl. Qed.
Lemma D_653c4 : decode_any W_653c4 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_653c8 : bv 32 := 0x0005b423.
Lemma F_653c8 : fetch_word Asan.M.loaded_segments (0x65418 : word) = Some W_653c8.
Proof. vm_refl. Qed.
Lemma D_653c8 : decode_any W_653c8 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_653cc : bv 32 := 0x0005b823.
Lemma F_653cc : fetch_word Asan.M.loaded_segments (0x6541c : word) = Some W_653cc.
Proof. vm_refl. Qed.
Lemma D_653cc : decode_any W_653cc = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_653d0 : bv 32 := 0x0005bc23.
Lemma F_653d0 : fetch_word Asan.M.loaded_segments (0x65420 : word) = Some W_653d0.
Proof. vm_refl. Qed.
Lemma D_653d0 : decode_any W_653d0 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_653d4 : bv 32 := 0x0205b023.
Lemma F_653d4 : fetch_word Asan.M.loaded_segments (0x65424 : word) = Some W_653d4.
Proof. vm_refl. Qed.
Lemma D_653d4 : decode_any W_653d4 = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_653d8 : bv 32 := 0x0205b423.
Lemma F_653d8 : fetch_word Asan.M.loaded_segments (0x65428 : word) = Some W_653d8.
Proof. vm_refl. Qed.
Lemma D_653d8 : decode_any W_653d8 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_653dc : bv 32 := 0x0205b823.
Lemma F_653dc : fetch_word Asan.M.loaded_segments (0x6542c : word) = Some W_653dc.
Proof. vm_refl. Qed.
Lemma D_653dc : decode_any W_653dc = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_653e0 : bv 32 := 0x0205bc23.
Lemma F_653e0 : fetch_word Asan.M.loaded_segments (0x65430 : word) = Some W_653e0.
Proof. vm_refl. Qed.
Lemma D_653e0 : decode_any W_653e0 = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_653e4 : bv 32 := 0x0405b023.
Lemma F_653e4 : fetch_word Asan.M.loaded_segments (0x65434 : word) = Some W_653e4.
Proof. vm_refl. Qed.
Lemma D_653e4 : decode_any W_653e4 = Some (Store SZ8 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_653e8 : bv 32 := 0x0405b423.
Lemma F_653e8 : fetch_word Asan.M.loaded_segments (0x65438 : word) = Some W_653e8.
Proof. vm_refl. Qed.
Lemma D_653e8 : decode_any W_653e8 = Some (Store SZ8 11 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_653ec : bv 32 := 0x0405b823.
Lemma F_653ec : fetch_word Asan.M.loaded_segments (0x6543c : word) = Some W_653ec.
Proof. vm_refl. Qed.
Lemma D_653ec : decode_any W_653ec = Some (Store SZ8 11 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_653f0 : bv 32 := 0x0405bc23.
Lemma F_653f0 : fetch_word Asan.M.loaded_segments (0x65440 : word) = Some W_653f0.
Proof. vm_refl. Qed.
Lemma D_653f0 : decode_any W_653f0 = Some (Store SZ8 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_653f4 : bv 32 := 0x0605b023.
Lemma F_653f4 : fetch_word Asan.M.loaded_segments (0x65444 : word) = Some W_653f4.
Proof. vm_refl. Qed.
Lemma D_653f4 : decode_any W_653f4 = Some (Store SZ8 11 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_653f8 : bv 32 := 0x0605b423.
Lemma F_653f8 : fetch_word Asan.M.loaded_segments (0x65448 : word) = Some W_653f8.
Proof. vm_refl. Qed.
Lemma D_653f8 : decode_any W_653f8 = Some (Store SZ8 11 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_653fc : bv 32 := 0x0605b823.
Lemma F_653fc : fetch_word Asan.M.loaded_segments (0x6544c : word) = Some W_653fc.
Proof. vm_refl. Qed.
Lemma D_653fc : decode_any W_653fc = Some (Store SZ8 11 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_65400 : bv 32 := 0x0605bc23.
Lemma F_65400 : fetch_word Asan.M.loaded_segments (0x65450 : word) = Some W_65400.
Proof. vm_refl. Qed.
Lemma D_65400 : decode_any W_65400 = Some (Store SZ8 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_65404 : bv 32 := 0x0805b023.
Lemma F_65404 : fetch_word Asan.M.loaded_segments (0x65454 : word) = Some W_65404.
Proof. vm_refl. Qed.
Lemma D_65404 : decode_any W_65404 = Some (Store SZ8 11 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_65408 : bv 32 := 0x0805b423.
Lemma F_65408 : fetch_word Asan.M.loaded_segments (0x65458 : word) = Some W_65408.
Proof. vm_refl. Qed.
Lemma D_65408 : decode_any W_65408 = Some (Store SZ8 11 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_6540c : bv 32 := 0x0805b823.
Lemma F_6540c : fetch_word Asan.M.loaded_segments (0x6545c : word) = Some W_6540c.
Proof. vm_refl. Qed.
Lemma D_6540c : decode_any W_6540c = Some (Store SZ8 11 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_65410 : bv 32 := 0x0805bc23.
Lemma F_65410 : fetch_word Asan.M.loaded_segments (0x65460 : word) = Some W_65410.
Proof. vm_refl. Qed.
Lemma D_65410 : decode_any W_65410 = Some (Store SZ8 11 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_65414 : bv 32 := 0x0a05b023.
Lemma F_65414 : fetch_word Asan.M.loaded_segments (0x65464 : word) = Some W_65414.
Proof. vm_refl. Qed.
Lemma D_65414 : decode_any W_65414 = Some (Store SZ8 11 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_65418 : bv 32 := 0x0a05b423.
Lemma F_65418 : fetch_word Asan.M.loaded_segments (0x65468 : word) = Some W_65418.
Proof. vm_refl. Qed.
Lemma D_65418 : decode_any W_65418 = Some (Store SZ8 11 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_6541c : bv 32 := 0x0a05b823.
Lemma F_6541c : fetch_word Asan.M.loaded_segments (0x6546c : word) = Some W_6541c.
Proof. vm_refl. Qed.
Lemma D_6541c : decode_any W_6541c = Some (Store SZ8 11 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_65420 : bv 32 := 0x0a05bc23.
Lemma F_65420 : fetch_word Asan.M.loaded_segments (0x65470 : word) = Some W_65420.
Proof. vm_refl. Qed.
Lemma D_65420 : decode_any W_65420 = Some (Store SZ8 11 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_65424 : bv 32 := 0x0c05b023.
Lemma F_65424 : fetch_word Asan.M.loaded_segments (0x65474 : word) = Some W_65424.
Proof. vm_refl. Qed.
Lemma D_65424 : decode_any W_65424 = Some (Store SZ8 11 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_65428 : bv 32 := 0x0c05b423.
Lemma F_65428 : fetch_word Asan.M.loaded_segments (0x65478 : word) = Some W_65428.
Proof. vm_refl. Qed.
Lemma D_65428 : decode_any W_65428 = Some (Store SZ8 11 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_6542c : bv 32 := 0x0c05b823.
Lemma F_6542c : fetch_word Asan.M.loaded_segments (0x6547c : word) = Some W_6542c.
Proof. vm_refl. Qed.
Lemma D_6542c : decode_any W_6542c = Some (Store SZ8 11 0 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_65430 : bv 32 := 0x0c05bc23.
Lemma F_65430 : fetch_word Asan.M.loaded_segments (0x65480 : word) = Some W_65430.
Proof. vm_refl. Qed.
Lemma D_65430 : decode_any W_65430 = Some (Store SZ8 11 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_65434 : bv 32 := 0x0e05b023.
Lemma F_65434 : fetch_word Asan.M.loaded_segments (0x65484 : word) = Some W_65434.
Proof. vm_refl. Qed.
Lemma D_65434 : decode_any W_65434 = Some (Store SZ8 11 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_65438 : bv 32 := 0x0e05b423.
Lemma F_65438 : fetch_word Asan.M.loaded_segments (0x65488 : word) = Some W_65438.
Proof. vm_refl. Qed.
Lemma D_65438 : decode_any W_65438 = Some (Store SZ8 11 0 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_6543c : bv 32 := 0x0e05b823.
Lemma F_6543c : fetch_word Asan.M.loaded_segments (0x6548c : word) = Some W_6543c.
Proof. vm_refl. Qed.
Lemma D_6543c : decode_any W_6543c = Some (Store SZ8 11 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_65440 : bv 32 := 0x0e05bc23.
Lemma F_65440 : fetch_word Asan.M.loaded_segments (0x65490 : word) = Some W_65440.
Proof. vm_refl. Qed.
Lemma D_65440 : decode_any W_65440 = Some (Store SZ8 11 0 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_65444 : bv 32 := 0x01813083.
Lemma F_65444 : fetch_word Asan.M.loaded_segments (0x65494 : word) = Some W_65444.
Proof. vm_refl. Qed.
Lemma D_65444 : decode_any W_65444 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65448 : bv 32 := 0x01013403.
Lemma F_65448 : fetch_word Asan.M.loaded_segments (0x65498 : word) = Some W_65448.
Proof. vm_refl. Qed.
Lemma D_65448 : decode_any W_65448 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6544c : bv 32 := 0x00813483.
Lemma F_6544c : fetch_word Asan.M.loaded_segments (0x6549c : word) = Some W_6544c.
Proof. vm_refl. Qed.
Lemma D_6544c : decode_any W_6544c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65450 : bv 32 := 0x00013903.
Lemma F_65450 : fetch_word Asan.M.loaded_segments (0x654a0 : word) = Some W_65450.
Proof. vm_refl. Qed.
Lemma D_65450 : decode_any W_65450 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65454 : bv 32 := 0x02010113.
Lemma F_65454 : fetch_word Asan.M.loaded_segments (0x654a4 : word) = Some W_65454.
Proof. vm_refl. Qed.
Lemma D_65454 : decode_any W_65454 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65458 : bv 32 := 0x00008067.
Lemma F_65458 : fetch_word Asan.M.loaded_segments (0x654a8 : word) = Some W_65458.
Proof. vm_refl. Qed.
Lemma D_65458 : decode_any W_65458 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65478 : bv 32 := 0xff010113.
Lemma F_65478 : fetch_word Asan.M.loaded_segments (0x654c8 : word) = Some W_65478.
Proof. vm_refl. Qed.
Lemma D_65478 : decode_any W_65478 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_6547c : bv 32 := 0x00113423.
Lemma F_6547c : fetch_word Asan.M.loaded_segments (0x654cc : word) = Some W_6547c.
Proof. vm_refl. Qed.
Lemma D_6547c : decode_any W_6547c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65480 : bv 32 := 0x00813023.
Lemma F_65480 : fetch_word Asan.M.loaded_segments (0x654d0 : word) = Some W_65480.
Proof. vm_refl. Qed.
Lemma D_65480 : decode_any W_65480 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65484 : bv 32 := 0x7f853583.
Lemma F_65484 : fetch_word Asan.M.loaded_segments (0x654d4 : word) = Some W_65484.
Proof. vm_refl. Qed.
Lemma D_65484 : decode_any W_65484 = Some (Load SZ8 true 11 10 2040, 4%Z).
Proof. vm_refl. Qed.

Definition W_65488 : bv 32 := 0x00000413.
Lemma F_65488 : fetch_word Asan.M.loaded_segments (0x654d8 : word) = Some W_65488.
Proof. vm_refl. Qed.
Lemma D_65488 : decode_any W_65488 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6548c : bv 32 := 0x00058023.
Lemma F_6548c : fetch_word Asan.M.loaded_segments (0x654dc : word) = Some W_6548c.
Proof. vm_refl. Qed.
Lemma D_6548c : decode_any W_6548c = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65490 : bv 32 := 0x09c000ef.
Lemma F_65490 : fetch_word Asan.M.loaded_segments (0x654e0 : word) = Some W_65490.
Proof. vm_refl. Qed.
Lemma D_65490 : decode_any W_65490 = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_65494 : bv 32 := 0xfffab597.
Lemma F_65494 : fetch_word Asan.M.loaded_segments (0x654e4 : word) = Some W_65494.
Proof. vm_refl. Qed.
Lemma D_65494 : decode_any W_65494 = Some (Auipc 11 1048491, 4%Z).
Proof. vm_refl. Qed.

Definition W_65498 : bv 32 := 0xeb45b583.
Lemma F_65498 : fetch_word Asan.M.loaded_segments (0x654e8 : word) = Some W_65498.
Proof. vm_refl. Qed.
Lemma D_65498 : decode_any W_65498 = Some (Load SZ8 true 11 11 3764, 4%Z).
Proof. vm_refl. Qed.

Definition W_6549c : bv 32 := 0x00b53023.
Lemma F_6549c : fetch_word Asan.M.loaded_segments (0x654ec : word) = Some W_6549c.
Proof. vm_refl. Qed.
Lemma D_6549c : decode_any W_6549c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_654a0 : bv 32 := 0x00b53423.
Lemma F_654a0 : fetch_word Asan.M.loaded_segments (0x654f0 : word) = Some W_654a0.
Proof. vm_refl. Qed.
Lemma D_654a0 : decode_any W_654a0 = Some (Store SZ8 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_654a4 : bv 32 := 0x00b53823.
Lemma F_654a4 : fetch_word Asan.M.loaded_segments (0x654f4 : word) = Some W_654a4.
Proof. vm_refl. Qed.
Lemma D_654a4 : decode_any W_654a4 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_654a8 : bv 32 := 0x00b53c23.
Lemma F_654a8 : fetch_word Asan.M.loaded_segments (0x654f8 : word) = Some W_654a8.
Proof. vm_refl. Qed.
Lemma D_654a8 : decode_any W_654a8 = Some (Store SZ8 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_654ac : bv 32 := 0x02b53023.
Lemma F_654ac : fetch_word Asan.M.loaded_segments (0x654fc : word) = Some W_654ac.
Proof. vm_refl. Qed.
Lemma D_654ac : decode_any W_654ac = Some (Store SZ8 10 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_654b0 : bv 32 := 0x02b53423.
Lemma F_654b0 : fetch_word Asan.M.loaded_segments (0x65500 : word) = Some W_654b0.
Proof. vm_refl. Qed.
Lemma D_654b0 : decode_any W_654b0 = Some (Store SZ8 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_654b4 : bv 32 := 0x02b53823.
Lemma F_654b4 : fetch_word Asan.M.loaded_segments (0x65504 : word) = Some W_654b4.
Proof. vm_refl. Qed.
Lemma D_654b4 : decode_any W_654b4 = Some (Store SZ8 10 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_654b8 : bv 32 := 0x02b53c23.
Lemma F_654b8 : fetch_word Asan.M.loaded_segments (0x65508 : word) = Some W_654b8.
Proof. vm_refl. Qed.
Lemma D_654b8 : decode_any W_654b8 = Some (Store SZ8 10 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_654bc : bv 32 := 0x04b53023.
Lemma F_654bc : fetch_word Asan.M.loaded_segments (0x6550c : word) = Some W_654bc.
Proof. vm_refl. Qed.
Lemma D_654bc : decode_any W_654bc = Some (Store SZ8 10 11 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_654c0 : bv 32 := 0x04b53423.
Lemma F_654c0 : fetch_word Asan.M.loaded_segments (0x65510 : word) = Some W_654c0.
Proof. vm_refl. Qed.
Lemma D_654c0 : decode_any W_654c0 = Some (Store SZ8 10 11 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_654c4 : bv 32 := 0x04b53823.
Lemma F_654c4 : fetch_word Asan.M.loaded_segments (0x65514 : word) = Some W_654c4.
Proof. vm_refl. Qed.
Lemma D_654c4 : decode_any W_654c4 = Some (Store SZ8 10 11 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_654c8 : bv 32 := 0x04b53c23.
Lemma F_654c8 : fetch_word Asan.M.loaded_segments (0x65518 : word) = Some W_654c8.
Proof. vm_refl. Qed.
Lemma D_654c8 : decode_any W_654c8 = Some (Store SZ8 10 11 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_654cc : bv 32 := 0x06b53023.
Lemma F_654cc : fetch_word Asan.M.loaded_segments (0x6551c : word) = Some W_654cc.
Proof. vm_refl. Qed.
Lemma D_654cc : decode_any W_654cc = Some (Store SZ8 10 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_654d0 : bv 32 := 0x06b53423.
Lemma F_654d0 : fetch_word Asan.M.loaded_segments (0x65520 : word) = Some W_654d0.
Proof. vm_refl. Qed.
Lemma D_654d0 : decode_any W_654d0 = Some (Store SZ8 10 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_654d4 : bv 32 := 0x06b53823.
Lemma F_654d4 : fetch_word Asan.M.loaded_segments (0x65524 : word) = Some W_654d4.
Proof. vm_refl. Qed.
Lemma D_654d4 : decode_any W_654d4 = Some (Store SZ8 10 11 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_654d8 : bv 32 := 0x06b53c23.
Lemma F_654d8 : fetch_word Asan.M.loaded_segments (0x65528 : word) = Some W_654d8.
Proof. vm_refl. Qed.
Lemma D_654d8 : decode_any W_654d8 = Some (Store SZ8 10 11 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_654dc : bv 32 := 0x08b53023.
Lemma F_654dc : fetch_word Asan.M.loaded_segments (0x6552c : word) = Some W_654dc.
Proof. vm_refl. Qed.
Lemma D_654dc : decode_any W_654dc = Some (Store SZ8 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_654e0 : bv 32 := 0x08b53423.
Lemma F_654e0 : fetch_word Asan.M.loaded_segments (0x65530 : word) = Some W_654e0.
Proof. vm_refl. Qed.
Lemma D_654e0 : decode_any W_654e0 = Some (Store SZ8 10 11 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_654e4 : bv 32 := 0x08b53823.
Lemma F_654e4 : fetch_word Asan.M.loaded_segments (0x65534 : word) = Some W_654e4.
Proof. vm_refl. Qed.
Lemma D_654e4 : decode_any W_654e4 = Some (Store SZ8 10 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_654e8 : bv 32 := 0x08b53c23.
Lemma F_654e8 : fetch_word Asan.M.loaded_segments (0x65538 : word) = Some W_654e8.
Proof. vm_refl. Qed.
Lemma D_654e8 : decode_any W_654e8 = Some (Store SZ8 10 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_654ec : bv 32 := 0x0ab53023.
Lemma F_654ec : fetch_word Asan.M.loaded_segments (0x6553c : word) = Some W_654ec.
Proof. vm_refl. Qed.
Lemma D_654ec : decode_any W_654ec = Some (Store SZ8 10 11 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_654f0 : bv 32 := 0x0ab53423.
Lemma F_654f0 : fetch_word Asan.M.loaded_segments (0x65540 : word) = Some W_654f0.
Proof. vm_refl. Qed.
Lemma D_654f0 : decode_any W_654f0 = Some (Store SZ8 10 11 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_654f4 : bv 32 := 0x0ab53823.
Lemma F_654f4 : fetch_word Asan.M.loaded_segments (0x65544 : word) = Some W_654f4.
Proof. vm_refl. Qed.
Lemma D_654f4 : decode_any W_654f4 = Some (Store SZ8 10 11 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_654f8 : bv 32 := 0x0ab53c23.
Lemma F_654f8 : fetch_word Asan.M.loaded_segments (0x65548 : word) = Some W_654f8.
Proof. vm_refl. Qed.
Lemma D_654f8 : decode_any W_654f8 = Some (Store SZ8 10 11 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_654fc : bv 32 := 0x0cb53023.
Lemma F_654fc : fetch_word Asan.M.loaded_segments (0x6554c : word) = Some W_654fc.
Proof. vm_refl. Qed.
Lemma D_654fc : decode_any W_654fc = Some (Store SZ8 10 11 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_65500 : bv 32 := 0x0cb53423.
Lemma F_65500 : fetch_word Asan.M.loaded_segments (0x65550 : word) = Some W_65500.
Proof. vm_refl. Qed.
Lemma D_65500 : decode_any W_65500 = Some (Store SZ8 10 11 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_65504 : bv 32 := 0x0cb53823.
Lemma F_65504 : fetch_word Asan.M.loaded_segments (0x65554 : word) = Some W_65504.
Proof. vm_refl. Qed.
Lemma D_65504 : decode_any W_65504 = Some (Store SZ8 10 11 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_65508 : bv 32 := 0x0cb53c23.
Lemma F_65508 : fetch_word Asan.M.loaded_segments (0x65558 : word) = Some W_65508.
Proof. vm_refl. Qed.
Lemma D_65508 : decode_any W_65508 = Some (Store SZ8 10 11 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_6550c : bv 32 := 0x0eb53023.
Lemma F_6550c : fetch_word Asan.M.loaded_segments (0x6555c : word) = Some W_6550c.
Proof. vm_refl. Qed.
Lemma D_6550c : decode_any W_6550c = Some (Store SZ8 10 11 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_65510 : bv 32 := 0x0eb53423.
Lemma F_65510 : fetch_word Asan.M.loaded_segments (0x65560 : word) = Some W_65510.
Proof. vm_refl. Qed.
Lemma D_65510 : decode_any W_65510 = Some (Store SZ8 10 11 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_65514 : bv 32 := 0x0eb53823.
Lemma F_65514 : fetch_word Asan.M.loaded_segments (0x65564 : word) = Some W_65514.
Proof. vm_refl. Qed.
Lemma D_65514 : decode_any W_65514 = Some (Store SZ8 10 11 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_65518 : bv 32 := 0x0eb53c23.
Lemma F_65518 : fetch_word Asan.M.loaded_segments (0x65568 : word) = Some W_65518.
Proof. vm_refl. Qed.
Lemma D_65518 : decode_any W_65518 = Some (Store SZ8 10 11 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_6551c : bv 32 := 0x00813083.
Lemma F_6551c : fetch_word Asan.M.loaded_segments (0x6556c : word) = Some W_6551c.
Proof. vm_refl. Qed.
Lemma D_6551c : decode_any W_6551c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65520 : bv 32 := 0x00013403.
Lemma F_65520 : fetch_word Asan.M.loaded_segments (0x65570 : word) = Some W_65520.
Proof. vm_refl. Qed.
Lemma D_65520 : decode_any W_65520 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65524 : bv 32 := 0x01010113.
Lemma F_65524 : fetch_word Asan.M.loaded_segments (0x65574 : word) = Some W_65524.
Proof. vm_refl. Qed.
Lemma D_65524 : decode_any W_65524 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65528 : bv 32 := 0x00008067.
Lemma F_65528 : fetch_word Asan.M.loaded_segments (0x65578 : word) = Some W_65528.
Proof. vm_refl. Qed.
Lemma D_65528 : decode_any W_65528 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6552c : bv 32 := 0x000ee597.
Lemma F_6552c : fetch_word Asan.M.loaded_segments (0x6557c : word) = Some W_6552c.
Proof. vm_refl. Qed.
Lemma D_6552c : decode_any W_6552c = Some (Auipc 11 238, 4%Z).
Proof. vm_refl. Qed.

Definition W_65530 : bv 32 := 0xbbc5b583.
Lemma F_65530 : fetch_word Asan.M.loaded_segments (0x65580 : word) = Some W_65530.
Proof. vm_refl. Qed.
Lemma D_65530 : decode_any W_65530 = Some (Load SZ8 true 11 11 3004, 4%Z).
Proof. vm_refl. Qed.

Definition W_65534 : bv 32 := 0x0005b583.
Lemma F_65534 : fetch_word Asan.M.loaded_segments (0x65584 : word) = Some W_65534.
Proof. vm_refl. Qed.
Lemma D_65534 : decode_any W_65534 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65538 : bv 32 := 0xfff58613.
Lemma F_65538 : fetch_word Asan.M.loaded_segments (0x65588 : word) = Some W_65538.
Proof. vm_refl. Qed.
Lemma D_65538 : decode_any W_65538 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6553c : bv 32 := 0x00c5b6b3.
Lemma F_6553c : fetch_word Asan.M.loaded_segments (0x6558c : word) = Some W_6553c.
Proof. vm_refl. Qed.
Lemma D_6553c : decode_any W_6553c = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_65540 : bv 32 := 0xfff68693.
Lemma F_65540 : fetch_word Asan.M.loaded_segments (0x65590 : word) = Some W_65540.
Proof. vm_refl. Qed.
Lemma D_65540 : decode_any W_65540 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65544 : bv 32 := 0x00c6f6b3.
Lemma F_65544 : fetch_word Asan.M.loaded_segments (0x65594 : word) = Some W_65544.
Proof. vm_refl. Qed.
Lemma D_65544 : decode_any W_65544 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_65548 : bv 32 := 0x04a6f263.
Lemma F_65548 : fetch_word Asan.M.loaded_segments (0x65598 : word) = Some W_65548.
Proof. vm_refl. Qed.
Lemma D_65548 : decode_any W_65548 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_6554c : bv 32 := 0x000ee697.
Lemma F_6554c : fetch_word Asan.M.loaded_segments (0x6559c : word) = Some W_6554c.
Proof. vm_refl. Qed.
Lemma D_6554c : decode_any W_6554c = Some (Auipc 13 238, 4%Z).
Proof. vm_refl. Qed.

Definition W_65550 : bv 32 := 0xba46b683.
Lemma F_65550 : fetch_word Asan.M.loaded_segments (0x655a0 : word) = Some W_65550.
Proof. vm_refl. Qed.
Lemma D_65550 : decode_any W_65550 = Some (Load SZ8 true 13 13 2980, 4%Z).
Proof. vm_refl. Qed.

Definition W_65554 : bv 32 := 0x000ee717.
Lemma F_65554 : fetch_word Asan.M.loaded_segments (0x655a4 : word) = Some W_65554.
Proof. vm_refl. Qed.
Lemma D_65554 : decode_any W_65554 = Some (Auipc 14 238, 4%Z).
Proof. vm_refl. Qed.

Definition W_65558 : bv 32 := 0xba473703.
Lemma F_65558 : fetch_word Asan.M.loaded_segments (0x655a8 : word) = Some W_65558.
Proof. vm_refl. Qed.
Lemma D_65558 : decode_any W_65558 = Some (Load SZ8 true 14 14 2980, 4%Z).
Proof. vm_refl. Qed.

Definition W_6555c : bv 32 := 0x0006b803.
Lemma F_6555c : fetch_word Asan.M.loaded_segments (0x655ac : word) = Some W_6555c.
Proof. vm_refl. Qed.
Lemma D_6555c : decode_any W_6555c = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65560 : bv 32 := 0x00073683.
Lemma F_65560 : fetch_word Asan.M.loaded_segments (0x655b0 : word) = Some W_65560.
Proof. vm_refl. Qed.
Lemma D_65560 : decode_any W_65560 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65564 : bv 32 := 0xfff80793.
Lemma F_65564 : fetch_word Asan.M.loaded_segments (0x655b4 : word) = Some W_65564.
Proof. vm_refl. Qed.
Lemma D_65564 : decode_any W_65564 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65568 : bv 32 := 0x00a7f463.
Lemma F_65568 : fetch_word Asan.M.loaded_segments (0x655b8 : word) = Some W_65568.
Proof. vm_refl. Qed.
Lemma D_65568 : decode_any W_65568 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65570 : bv 32 := 0x000ee717.
Lemma F_65570 : fetch_word Asan.M.loaded_segments (0x655c0 : word) = Some W_65570.
Proof. vm_refl. Qed.
Lemma D_65570 : decode_any W_65570 = Some (Auipc 14 238, 4%Z).
Proof. vm_refl. Qed.

Definition W_65574 : bv 32 := 0xb9073703.
Lemma F_65574 : fetch_word Asan.M.loaded_segments (0x655c4 : word) = Some W_65574.
Proof. vm_refl. Qed.
Lemma D_65574 : decode_any W_65574 = Some (Load SZ8 true 14 14 2960, 4%Z).
Proof. vm_refl. Qed.

Definition W_65578 : bv 32 := 0x00073283.
Lemma F_65578 : fetch_word Asan.M.loaded_segments (0x655c8 : word) = Some W_65578.
Proof. vm_refl. Qed.
Lemma D_65578 : decode_any W_65578 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6557c : bv 32 := 0x0032d713.
Lemma F_6557c : fetch_word Asan.M.loaded_segments (0x655cc : word) = Some W_6557c.
Proof. vm_refl. Qed.
Lemma D_6557c : decode_any W_6557c = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_65580 : bv 32 := 0x00b708b3.
Lemma F_65580 : fetch_word Asan.M.loaded_segments (0x655d0 : word) = Some W_65580.
Proof. vm_refl. Qed.
Lemma D_65580 : decode_any W_65580 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_65584 : bv 32 := 0x00a2ea63.
Lemma F_65584 : fetch_word Asan.M.loaded_segments (0x655d4 : word) = Some W_65584.
Proof. vm_refl. Qed.
Lemma D_65584 : decode_any W_65584 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_65588 : bv 32 := 0x00a8f863.
Lemma F_65588 : fetch_word Asan.M.loaded_segments (0x655d8 : word) = Some W_65588.
Proof. vm_refl. Qed.
Lemma D_65588 : decode_any W_65588 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6558c : bv 32 := 0x00355513.
Lemma F_6558c : fetch_word Asan.M.loaded_segments (0x655dc : word) = Some W_6558c.
Proof. vm_refl. Qed.
Lemma D_6558c : decode_any W_6558c = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_65590 : bv 32 := 0x00a58533.
Lemma F_65590 : fetch_word Asan.M.loaded_segments (0x655e0 : word) = Some W_65590.
Proof. vm_refl. Qed.
Lemma D_65590 : decode_any W_65590 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_65594 : bv 32 := 0x00008067.
Lemma F_65594 : fetch_word Asan.M.loaded_segments (0x655e4 : word) = Some W_65594.
Proof. vm_refl. Qed.
Lemma D_65594 : decode_any W_65594 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

