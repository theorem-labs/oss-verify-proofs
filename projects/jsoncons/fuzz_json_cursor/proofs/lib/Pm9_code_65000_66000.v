(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_65000 : bv 32 := 0x00b797b3.
Lemma F_65000 : fetch_word AsanUbsan.M.loaded_segments (0x65048 : word) = Some W_65000.
Proof. vm_refl. Qed.
Lemma D_65000 : decode_any W_65000 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_65004 : bv 32 := 0xfff50813.
Lemma F_65004 : fetch_word AsanUbsan.M.loaded_segments (0x6504c : word) = Some W_65004.
Proof. vm_refl. Qed.
Lemma D_65004 : decode_any W_65004 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65008 : bv 32 := 0x00d485b3.
Lemma F_65008 : fetch_word AsanUbsan.M.loaded_segments (0x65050 : word) = Some W_65008.
Proof. vm_refl. Qed.
Lemma D_65008 : decode_any W_65008 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6500c : bv 32 := 0x00e586b3.
Lemma F_6500c : fetch_word AsanUbsan.M.loaded_segments (0x65054 : word) = Some W_6500c.
Proof. vm_refl. Qed.
Lemma D_6500c : decode_any W_6500c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_65010 : bv 32 := 0xfff7c713.
Lemma F_65010 : fetch_word AsanUbsan.M.loaded_segments (0x65058 : word) = Some W_65010.
Proof. vm_refl. Qed.
Lemma D_65010 : decode_any W_65010 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65014 : bv 32 := 0x02081813.
Lemma F_65014 : fetch_word AsanUbsan.M.loaded_segments (0x6505c : word) = Some W_65014.
Proof. vm_refl. Qed.
Lemma D_65014 : decode_any W_65014 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65018 : bv 32 := 0x02085793.
Lemma F_65018 : fetch_word AsanUbsan.M.loaded_segments (0x65060 : word) = Some W_65018.
Proof. vm_refl. Qed.
Lemma D_65018 : decode_any W_65018 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6501c : bv 32 := 0x00f607b3.
Lemma F_6501c : fetch_word AsanUbsan.M.loaded_segments (0x65064 : word) = Some W_6501c.
Proof. vm_refl. Qed.
Lemma D_6501c : decode_any W_6501c = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_65020 : bv 32 := 0x00178813.
Lemma F_65020 : fetch_word AsanUbsan.M.loaded_segments (0x65068 : word) = Some W_65020.
Proof. vm_refl. Qed.
Lemma D_65020 : decode_any W_65020 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65024 : bv 32 := 0x00e678b3.
Lemma F_65024 : fetch_word AsanUbsan.M.loaded_segments (0x6506c : word) = Some W_65024.
Proof. vm_refl. Qed.
Lemma D_65024 : decode_any W_65024 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_65028 : bv 32 := 0x011687b3.
Lemma F_65028 : fetch_word AsanUbsan.M.loaded_segments (0x65070 : word) = Some W_65028.
Proof. vm_refl. Qed.
Lemma D_65028 : decode_any W_65028 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_6502c : bv 32 := 0x0007c283.
Lemma F_6502c : fetch_word AsanUbsan.M.loaded_segments (0x65074 : word) = Some W_6502c.
Proof. vm_refl. Qed.
Lemma D_6502c : decode_any W_6502c = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65030 : bv 32 := 0x06028663.
Lemma F_65030 : fetch_word AsanUbsan.M.loaded_segments (0x65078 : word) = Some W_65030.
Proof. vm_refl. Qed.
Lemma D_65030 : decode_any W_65030 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_65034 : bv 32 := 0xfff5051b.
Lemma F_65034 : fetch_word AsanUbsan.M.loaded_segments (0x6507c : word) = Some W_65034.
Proof. vm_refl. Qed.
Lemma D_65034 : decode_any W_65034 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65038 : bv 32 := 0x00160613.
Lemma F_65038 : fetch_word AsanUbsan.M.loaded_segments (0x65080 : word) = Some W_65038.
Proof. vm_refl. Qed.
Lemma D_65038 : decode_any W_65038 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6503c : bv 32 := 0xfe0514e3.
Lemma F_6503c : fetch_word AsanUbsan.M.loaded_segments (0x65084 : word) = Some W_6503c.
Proof. vm_refl. Qed.
Lemma D_6503c : decode_any W_6503c = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_6509c : bv 32 := 0x00160613.
Lemma F_6509c : fetch_word AsanUbsan.M.loaded_segments (0x650e4 : word) = Some W_6509c.
Proof. vm_refl. Qed.
Lemma D_6509c : decode_any W_6509c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_650a0 : bv 32 := 0x00100513.
Lemma F_650a0 : fetch_word AsanUbsan.M.loaded_segments (0x650e8 : word) = Some W_650a0.
Proof. vm_refl. Qed.
Lemma D_650a0 : decode_any W_650a0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_650a4 : bv 32 := 0xffb90693.
Lemma F_650a4 : fetch_word AsanUbsan.M.loaded_segments (0x650ec : word) = Some W_650a4.
Proof. vm_refl. Qed.
Lemma D_650a4 : decode_any W_650a4 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_650a8 : bv 32 := 0x00789893.
Lemma F_650a8 : fetch_word AsanUbsan.M.loaded_segments (0x650f0 : word) = Some W_650a8.
Proof. vm_refl. Qed.
Lemma D_650a8 : decode_any W_650a8 = Some (ShiftImm ALU_SLL 17 17 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_650ac : bv 32 := 0x00c4b423.
Lemma F_650ac : fetch_word AsanUbsan.M.loaded_segments (0x650f4 : word) = Some W_650ac.
Proof. vm_refl. Qed.
Lemma D_650ac : decode_any W_650ac = Some (Store SZ8 9 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_650b0 : bv 32 := 0x00a78023.
Lemma F_650b0 : fetch_word AsanUbsan.M.loaded_segments (0x650f8 : word) = Some W_650b0.
Proof. vm_refl. Qed.
Lemma D_650b0 : decode_any W_650b0 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650b4 : bv 32 := 0x00d51633.
Lemma F_650b4 : fetch_word AsanUbsan.M.loaded_segments (0x650fc : word) = Some W_650b4.
Proof. vm_refl. Qed.
Lemma D_650b4 : decode_any W_650b4 = Some (Op ALU_SLL 12 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_650b8 : bv 32 := 0x01251533.
Lemma F_650b8 : fetch_word AsanUbsan.M.loaded_segments (0x65100 : word) = Some W_650b8.
Proof. vm_refl. Qed.
Lemma D_650b8 : decode_any W_650b8 = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_650bc : bv 32 := 0x00c585b3.
Lemma F_650bc : fetch_word AsanUbsan.M.loaded_segments (0x65104 : word) = Some W_650bc.
Proof. vm_refl. Qed.
Lemma D_650bc : decode_any W_650bc = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_650c0 : bv 32 := 0x01150533.
Lemma F_650c0 : fetch_word AsanUbsan.M.loaded_segments (0x65108 : word) = Some W_650c0.
Proof. vm_refl. Qed.
Lemma D_650c0 : decode_any W_650c0 = Some (Op ALU_ADD 10 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_650c4 : bv 32 := 0x00a584b3.
Lemma F_650c4 : fetch_word AsanUbsan.M.loaded_segments (0x6510c : word) = Some W_650c4.
Proof. vm_refl. Qed.
Lemma D_650c4 : decode_any W_650c4 = Some (Op ALU_ADD 9 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_650c8 : bv 32 := 0x0084bc23.
Lemma F_650c8 : fetch_word AsanUbsan.M.loaded_segments (0x65110 : word) = Some W_650c8.
Proof. vm_refl. Qed.
Lemma D_650c8 : decode_any W_650c8 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_650cc : bv 32 := 0x06f4bc23.
Lemma F_650cc : fetch_word AsanUbsan.M.loaded_segments (0x65114 : word) = Some W_650cc.
Proof. vm_refl. Qed.
Lemma D_650cc : decode_any W_650cc = Some (Store SZ8 9 15 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_650d0 : bv 32 := 0x00048513.
Lemma F_650d0 : fetch_word AsanUbsan.M.loaded_segments (0x65118 : word) = Some W_650d0.
Proof. vm_refl. Qed.
Lemma D_650d0 : decode_any W_650d0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650d4 : bv 32 := 0x021000ef.
Lemma F_650d4 : fetch_word AsanUbsan.M.loaded_segments (0x6511c : word) = Some W_650d4.
Proof. vm_refl. Qed.
Lemma D_650d4 : decode_any W_650d4 = Some (Jal 1 2080, 4%Z).
Proof. vm_refl. Qed.

Definition W_650d8 : bv 32 := 0x00050593.
Lemma F_650d8 : fetch_word AsanUbsan.M.loaded_segments (0x65120 : word) = Some W_650d8.
Proof. vm_refl. Qed.
Lemma D_650d8 : decode_any W_650d8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650dc : bv 32 := 0x00048513.
Lemma F_650dc : fetch_word AsanUbsan.M.loaded_segments (0x65124 : word) = Some W_650dc.
Proof. vm_refl. Qed.
Lemma D_650dc : decode_any W_650dc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650e0 : bv 32 := 0x00000613.
Lemma F_650e0 : fetch_word AsanUbsan.M.loaded_segments (0x65128 : word) = Some W_650e0.
Proof. vm_refl. Qed.
Lemma D_650e0 : decode_any W_650e0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650e4 : bv 32 := 0x0005b023.
Lemma F_650e4 : fetch_word AsanUbsan.M.loaded_segments (0x6512c : word) = Some W_650e4.
Proof. vm_refl. Qed.
Lemma D_650e4 : decode_any W_650e4 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650e8 : bv 32 := 0x0005b423.
Lemma F_650e8 : fetch_word AsanUbsan.M.loaded_segments (0x65130 : word) = Some W_650e8.
Proof. vm_refl. Qed.
Lemma D_650e8 : decode_any W_650e8 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_650ec : bv 32 := 0x01813083.
Lemma F_650ec : fetch_word AsanUbsan.M.loaded_segments (0x65134 : word) = Some W_650ec.
Proof. vm_refl. Qed.
Lemma D_650ec : decode_any W_650ec = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_650f0 : bv 32 := 0x01013403.
Lemma F_650f0 : fetch_word AsanUbsan.M.loaded_segments (0x65138 : word) = Some W_650f0.
Proof. vm_refl. Qed.
Lemma D_650f0 : decode_any W_650f0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_650f4 : bv 32 := 0x00813483.
Lemma F_650f4 : fetch_word AsanUbsan.M.loaded_segments (0x6513c : word) = Some W_650f4.
Proof. vm_refl. Qed.
Lemma D_650f4 : decode_any W_650f4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_650f8 : bv 32 := 0x00013903.
Lemma F_650f8 : fetch_word AsanUbsan.M.loaded_segments (0x65140 : word) = Some W_650f8.
Proof. vm_refl. Qed.
Lemma D_650f8 : decode_any W_650f8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650fc : bv 32 := 0x02010113.
Lemma F_650fc : fetch_word AsanUbsan.M.loaded_segments (0x65144 : word) = Some W_650fc.
Proof. vm_refl. Qed.
Lemma D_650fc : decode_any W_650fc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65100 : bv 32 := 0x00008067.
Lemma F_65100 : fetch_word AsanUbsan.M.loaded_segments (0x65148 : word) = Some W_65100.
Proof. vm_refl. Qed.
Lemma D_65100 : decode_any W_65100 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65120 : bv 32 := 0xfe010113.
Lemma F_65120 : fetch_word AsanUbsan.M.loaded_segments (0x65168 : word) = Some W_65120.
Proof. vm_refl. Qed.
Lemma D_65120 : decode_any W_65120 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_65124 : bv 32 := 0x00113c23.
Lemma F_65124 : fetch_word AsanUbsan.M.loaded_segments (0x6516c : word) = Some W_65124.
Proof. vm_refl. Qed.
Lemma D_65124 : decode_any W_65124 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65128 : bv 32 := 0x00813823.
Lemma F_65128 : fetch_word AsanUbsan.M.loaded_segments (0x65170 : word) = Some W_65128.
Proof. vm_refl. Qed.
Lemma D_65128 : decode_any W_65128 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6512c : bv 32 := 0x00913423.
Lemma F_6512c : fetch_word AsanUbsan.M.loaded_segments (0x65174 : word) = Some W_6512c.
Proof. vm_refl. Qed.
Lemma D_6512c : decode_any W_6512c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65130 : bv 32 := 0x01213023.
Lemma F_65130 : fetch_word AsanUbsan.M.loaded_segments (0x65178 : word) = Some W_65130.
Proof. vm_refl. Qed.
Lemma D_65130 : decode_any W_65130 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65134 : bv 32 := 0x02010413.
Lemma F_65134 : fetch_word AsanUbsan.M.loaded_segments (0x6517c : word) = Some W_65134.
Proof. vm_refl. Qed.
Lemma D_65134 : decode_any W_65134 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65138 : bv 32 := 0x000f0517.
Lemma F_65138 : fetch_word AsanUbsan.M.loaded_segments (0x65180 : word) = Some W_65138.
Proof. vm_refl. Qed.
Lemma D_65138 : decode_any W_65138 = Some (Auipc 10 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_6513c : bv 32 := 0x19050513.
Lemma F_6513c : fetch_word AsanUbsan.M.loaded_segments (0x65184 : word) = Some W_6513c.
Proof. vm_refl. Qed.
Lemma D_6513c : decode_any W_6513c = Some (OpImm ALU_ADD 10 10 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_65140 : bv 32 := 0x009050ef.
Lemma F_65140 : fetch_word AsanUbsan.M.loaded_segments (0x65188 : word) = Some W_65140.
Proof. vm_refl. Qed.
Lemma D_65140 : decode_any W_65140 = Some (Jal 1 22536, 4%Z).
Proof. vm_refl. Qed.

Definition W_65144 : bv 32 := 0x00053483.
Lemma F_65144 : fetch_word AsanUbsan.M.loaded_segments (0x6518c : word) = Some W_65144.
Proof. vm_refl. Qed.
Lemma D_65144 : decode_any W_65144 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65148 : bv 32 := 0x08048863.
Lemma F_65148 : fetch_word AsanUbsan.M.loaded_segments (0x65190 : word) = Some W_65148.
Proof. vm_refl. Qed.
Lemma D_65148 : decode_any W_65148 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_6514c : bv 32 := 0x0604c503.
Lemma F_6514c : fetch_word AsanUbsan.M.loaded_segments (0x65194 : word) = Some W_6514c.
Proof. vm_refl. Qed.
Lemma D_6514c : decode_any W_6514c = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_65150 : bv 32 := 0x0584b903.
Lemma F_65150 : fetch_word AsanUbsan.M.loaded_segments (0x65198 : word) = Some W_65150.
Proof. vm_refl. Qed.
Lemma D_65150 : decode_any W_65150 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_65154 : bv 32 := 0x00050863.
Lemma F_65154 : fetch_word AsanUbsan.M.loaded_segments (0x6519c : word) = Some W_65154.
Proof. vm_refl. Qed.
Lemma D_65154 : decode_any W_65154 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65158 : bv 32 := 0x00048513.
Lemma F_65158 : fetch_word AsanUbsan.M.loaded_segments (0x651a0 : word) = Some W_65158.
Proof. vm_refl. Qed.
Lemma D_65158 : decode_any W_65158 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6515c : bv 32 := 0x00040593.
Lemma F_6515c : fetch_word AsanUbsan.M.loaded_segments (0x651a4 : word) = Some W_6515c.
Proof. vm_refl. Qed.
Lemma D_6515c : decode_any W_6515c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65160 : bv 32 := 0x871ff0ef.
Lemma F_65160 : fetch_word AsanUbsan.M.loaded_segments (0x651a8 : word) = Some W_65160.
Proof. vm_refl. Qed.
Lemma D_65160 : decode_any W_65160 = Some (Jal 1 2095216, 4%Z).
Proof. vm_refl. Qed.

Definition W_65164 : bv 32 := 0xff890593.
Lemma F_65164 : fetch_word AsanUbsan.M.loaded_segments (0x651ac : word) = Some W_65164.
Proof. vm_refl. Qed.
Lemma D_65164 : decode_any W_65164 = Some (OpImm ALU_ADD 11 18 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_65168 : bv 32 := 0x00100513.
Lemma F_65168 : fetch_word AsanUbsan.M.loaded_segments (0x651b0 : word) = Some W_65168.
Proof. vm_refl. Qed.
Lemma D_65168 : decode_any W_65168 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6516c : bv 32 := 0x00b51533.
Lemma F_6516c : fetch_word AsanUbsan.M.loaded_segments (0x651b4 : word) = Some W_6516c.
Proof. vm_refl. Qed.
Lemma D_6516c : decode_any W_6516c = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_65170 : bv 32 := 0x0005061b.
Lemma F_65170 : fetch_word AsanUbsan.M.loaded_segments (0x651b8 : word) = Some W_65170.
Proof. vm_refl. Qed.
Lemma D_65170 : decode_any W_65170 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65174 : bv 32 := 0x08c05263.
Lemma F_65174 : fetch_word AsanUbsan.M.loaded_segments (0x651bc : word) = Some W_65174.
Proof. vm_refl. Qed.
Lemma D_65174 : decode_any W_65174 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_65178 : bv 32 := 0x000016b7.
Lemma F_65178 : fetch_word AsanUbsan.M.loaded_segments (0x651c0 : word) = Some W_65178.
Proof. vm_refl. Qed.
Lemma D_65178 : decode_any W_65178 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6517c : bv 32 := 0xff190613.
Lemma F_6517c : fetch_word AsanUbsan.M.loaded_segments (0x651c4 : word) = Some W_6517c.
Proof. vm_refl. Qed.
Lemma D_6517c : decode_any W_6517c = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_65180 : bv 32 := 0x30000713.
Lemma F_65180 : fetch_word AsanUbsan.M.loaded_segments (0x651c8 : word) = Some W_65180.
Proof. vm_refl. Qed.
Lemma D_65180 : decode_any W_65180 = Some (OpImm ALU_ADD 14 0 768, 4%Z).
Proof. vm_refl. Qed.

Definition W_65184 : bv 32 := 0xfff00793.
Lemma F_65184 : fetch_word AsanUbsan.M.loaded_segments (0x651cc : word) = Some W_65184.
Proof. vm_refl. Qed.
Lemma D_65184 : decode_any W_65184 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65188 : bv 32 := 0x00c71733.
Lemma F_65188 : fetch_word AsanUbsan.M.loaded_segments (0x651d0 : word) = Some W_65188.
Proof. vm_refl. Qed.
Lemma D_65188 : decode_any W_65188 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6518c : bv 32 := 0x0104b603.
Lemma F_6518c : fetch_word AsanUbsan.M.loaded_segments (0x651d4 : word) = Some W_6518c.
Proof. vm_refl. Qed.
Lemma D_6518c : decode_any W_6518c = Some (Load SZ8 true 12 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65190 : bv 32 := 0x00b797b3.
Lemma F_65190 : fetch_word AsanUbsan.M.loaded_segments (0x651d8 : word) = Some W_65190.
Proof. vm_refl. Qed.
Lemma D_65190 : decode_any W_65190 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_65194 : bv 32 := 0xfff50813.
Lemma F_65194 : fetch_word AsanUbsan.M.loaded_segments (0x651dc : word) = Some W_65194.
Proof. vm_refl. Qed.
Lemma D_65194 : decode_any W_65194 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65198 : bv 32 := 0x00d485b3.
Lemma F_65198 : fetch_word AsanUbsan.M.loaded_segments (0x651e0 : word) = Some W_65198.
Proof. vm_refl. Qed.
Lemma D_65198 : decode_any W_65198 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6519c : bv 32 := 0x00e586b3.
Lemma F_6519c : fetch_word AsanUbsan.M.loaded_segments (0x651e4 : word) = Some W_6519c.
Proof. vm_refl. Qed.
Lemma D_6519c : decode_any W_6519c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_651a0 : bv 32 := 0xfff7c713.
Lemma F_651a0 : fetch_word AsanUbsan.M.loaded_segments (0x651e8 : word) = Some W_651a0.
Proof. vm_refl. Qed.
Lemma D_651a0 : decode_any W_651a0 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_651a4 : bv 32 := 0x02081813.
Lemma F_651a4 : fetch_word AsanUbsan.M.loaded_segments (0x651ec : word) = Some W_651a4.
Proof. vm_refl. Qed.
Lemma D_651a4 : decode_any W_651a4 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_651a8 : bv 32 := 0x02085793.
Lemma F_651a8 : fetch_word AsanUbsan.M.loaded_segments (0x651f0 : word) = Some W_651a8.
Proof. vm_refl. Qed.
Lemma D_651a8 : decode_any W_651a8 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_651ac : bv 32 := 0x00f607b3.
Lemma F_651ac : fetch_word AsanUbsan.M.loaded_segments (0x651f4 : word) = Some W_651ac.
Proof. vm_refl. Qed.
Lemma D_651ac : decode_any W_651ac = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_651b0 : bv 32 := 0x00178813.
Lemma F_651b0 : fetch_word AsanUbsan.M.loaded_segments (0x651f8 : word) = Some W_651b0.
Proof. vm_refl. Qed.
Lemma D_651b0 : decode_any W_651b0 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_651b4 : bv 32 := 0x00e678b3.
Lemma F_651b4 : fetch_word AsanUbsan.M.loaded_segments (0x651fc : word) = Some W_651b4.
Proof. vm_refl. Qed.
Lemma D_651b4 : decode_any W_651b4 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_651b8 : bv 32 := 0x011687b3.
Lemma F_651b8 : fetch_word AsanUbsan.M.loaded_segments (0x65200 : word) = Some W_651b8.
Proof. vm_refl. Qed.
Lemma D_651b8 : decode_any W_651b8 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_651bc : bv 32 := 0x0007c283.
Lemma F_651bc : fetch_word AsanUbsan.M.loaded_segments (0x65204 : word) = Some W_651bc.
Proof. vm_refl. Qed.
Lemma D_651bc : decode_any W_651bc = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_651c0 : bv 32 := 0x06028663.
Lemma F_651c0 : fetch_word AsanUbsan.M.loaded_segments (0x65208 : word) = Some W_651c0.
Proof. vm_refl. Qed.
Lemma D_651c0 : decode_any W_651c0 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_651c4 : bv 32 := 0xfff5051b.
Lemma F_651c4 : fetch_word AsanUbsan.M.loaded_segments (0x6520c : word) = Some W_651c4.
Proof. vm_refl. Qed.
Lemma D_651c4 : decode_any W_651c4 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_651c8 : bv 32 := 0x00160613.
Lemma F_651c8 : fetch_word AsanUbsan.M.loaded_segments (0x65210 : word) = Some W_651c8.
Proof. vm_refl. Qed.
Lemma D_651c8 : decode_any W_651c8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_651cc : bv 32 := 0xfe0514e3.
Lemma F_651cc : fetch_word AsanUbsan.M.loaded_segments (0x65214 : word) = Some W_651cc.
Proof. vm_refl. Qed.
Lemma D_651cc : decode_any W_651cc = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_6522c : bv 32 := 0x00160613.
Lemma F_6522c : fetch_word AsanUbsan.M.loaded_segments (0x65274 : word) = Some W_6522c.
Proof. vm_refl. Qed.
Lemma D_6522c : decode_any W_6522c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65230 : bv 32 := 0x00100513.
Lemma F_65230 : fetch_word AsanUbsan.M.loaded_segments (0x65278 : word) = Some W_65230.
Proof. vm_refl. Qed.
Lemma D_65230 : decode_any W_65230 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65234 : bv 32 := 0xffb90693.
Lemma F_65234 : fetch_word AsanUbsan.M.loaded_segments (0x6527c : word) = Some W_65234.
Proof. vm_refl. Qed.
Lemma D_65234 : decode_any W_65234 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_65238 : bv 32 := 0x00c4b823.
Lemma F_65238 : fetch_word AsanUbsan.M.loaded_segments (0x65280 : word) = Some W_65238.
Proof. vm_refl. Qed.
Lemma D_65238 : decode_any W_65238 = Some (Store SZ8 9 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6523c : bv 32 := 0x00a78023.
Lemma F_6523c : fetch_word AsanUbsan.M.loaded_segments (0x65284 : word) = Some W_6523c.
Proof. vm_refl. Qed.
Lemma D_6523c : decode_any W_6523c = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65240 : bv 32 := 0x00d51533.
Lemma F_65240 : fetch_word AsanUbsan.M.loaded_segments (0x65288 : word) = Some W_65240.
Proof. vm_refl. Qed.
Lemma D_65240 : decode_any W_65240 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_65244 : bv 32 := 0x00200613.
Lemma F_65244 : fetch_word AsanUbsan.M.loaded_segments (0x6528c : word) = Some W_65244.
Proof. vm_refl. Qed.
Lemma D_65244 : decode_any W_65244 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_65248 : bv 32 := 0x00889893.
Lemma F_65248 : fetch_word AsanUbsan.M.loaded_segments (0x65290 : word) = Some W_65248.
Proof. vm_refl. Qed.
Lemma D_65248 : decode_any W_65248 = Some (ShiftImm ALU_SLL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6524c : bv 32 := 0x01261633.
Lemma F_6524c : fetch_word AsanUbsan.M.loaded_segments (0x65294 : word) = Some W_6524c.
Proof. vm_refl. Qed.
Lemma D_6524c : decode_any W_6524c = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_65250 : bv 32 := 0x00a58533.
Lemma F_65250 : fetch_word AsanUbsan.M.loaded_segments (0x65298 : word) = Some W_65250.
Proof. vm_refl. Qed.
Lemma D_65250 : decode_any W_65250 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_65254 : bv 32 := 0x01160633.
Lemma F_65254 : fetch_word AsanUbsan.M.loaded_segments (0x6529c : word) = Some W_65254.
Proof. vm_refl. Qed.
Lemma D_65254 : decode_any W_65254 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_65258 : bv 32 := 0x00c504b3.
Lemma F_65258 : fetch_word AsanUbsan.M.loaded_segments (0x652a0 : word) = Some W_65258.
Proof. vm_refl. Qed.
Lemma D_65258 : decode_any W_65258 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6525c : bv 32 := 0x0084bc23.
Lemma F_6525c : fetch_word AsanUbsan.M.loaded_segments (0x652a4 : word) = Some W_6525c.
Proof. vm_refl. Qed.
Lemma D_6525c : decode_any W_6525c = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65260 : bv 32 := 0x0ef4bc23.
Lemma F_65260 : fetch_word AsanUbsan.M.loaded_segments (0x652a8 : word) = Some W_65260.
Proof. vm_refl. Qed.
Lemma D_65260 : decode_any W_65260 = Some (Store SZ8 9 15 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_65264 : bv 32 := 0x00048513.
Lemma F_65264 : fetch_word AsanUbsan.M.loaded_segments (0x652ac : word) = Some W_65264.
Proof. vm_refl. Qed.
Lemma D_65264 : decode_any W_65264 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65268 : bv 32 := 0x68c000ef.
Lemma F_65268 : fetch_word AsanUbsan.M.loaded_segments (0x652b0 : word) = Some W_65268.
Proof. vm_refl. Qed.
Lemma D_65268 : decode_any W_65268 = Some (Jal 1 1676, 4%Z).
Proof. vm_refl. Qed.

Definition W_6526c : bv 32 := 0x00050593.
Lemma F_6526c : fetch_word AsanUbsan.M.loaded_segments (0x652b4 : word) = Some W_6526c.
Proof. vm_refl. Qed.
Lemma D_6526c : decode_any W_6526c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65270 : bv 32 := 0x00048513.
Lemma F_65270 : fetch_word AsanUbsan.M.loaded_segments (0x652b8 : word) = Some W_65270.
Proof. vm_refl. Qed.
Lemma D_65270 : decode_any W_65270 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65274 : bv 32 := 0x00000613.
Lemma F_65274 : fetch_word AsanUbsan.M.loaded_segments (0x652bc : word) = Some W_65274.
Proof. vm_refl. Qed.
Lemma D_65274 : decode_any W_65274 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65278 : bv 32 := 0x0005b023.
Lemma F_65278 : fetch_word AsanUbsan.M.loaded_segments (0x652c0 : word) = Some W_65278.
Proof. vm_refl. Qed.
Lemma D_65278 : decode_any W_65278 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6527c : bv 32 := 0x0005b423.
Lemma F_6527c : fetch_word AsanUbsan.M.loaded_segments (0x652c4 : word) = Some W_6527c.
Proof. vm_refl. Qed.
Lemma D_6527c : decode_any W_6527c = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65280 : bv 32 := 0x0005b823.
Lemma F_65280 : fetch_word AsanUbsan.M.loaded_segments (0x652c8 : word) = Some W_65280.
Proof. vm_refl. Qed.
Lemma D_65280 : decode_any W_65280 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65284 : bv 32 := 0x0005bc23.
Lemma F_65284 : fetch_word AsanUbsan.M.loaded_segments (0x652cc : word) = Some W_65284.
Proof. vm_refl. Qed.
Lemma D_65284 : decode_any W_65284 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65288 : bv 32 := 0x01813083.
Lemma F_65288 : fetch_word AsanUbsan.M.loaded_segments (0x652d0 : word) = Some W_65288.
Proof. vm_refl. Qed.
Lemma D_65288 : decode_any W_65288 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6528c : bv 32 := 0x01013403.
Lemma F_6528c : fetch_word AsanUbsan.M.loaded_segments (0x652d4 : word) = Some W_6528c.
Proof. vm_refl. Qed.
Lemma D_6528c : decode_any W_6528c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65290 : bv 32 := 0x00813483.
Lemma F_65290 : fetch_word AsanUbsan.M.loaded_segments (0x652d8 : word) = Some W_65290.
Proof. vm_refl. Qed.
Lemma D_65290 : decode_any W_65290 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65294 : bv 32 := 0x00013903.
Lemma F_65294 : fetch_word AsanUbsan.M.loaded_segments (0x652dc : word) = Some W_65294.
Proof. vm_refl. Qed.
Lemma D_65294 : decode_any W_65294 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65298 : bv 32 := 0x02010113.
Lemma F_65298 : fetch_word AsanUbsan.M.loaded_segments (0x652e0 : word) = Some W_65298.
Proof. vm_refl. Qed.
Lemma D_65298 : decode_any W_65298 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6529c : bv 32 := 0x00008067.
Lemma F_6529c : fetch_word AsanUbsan.M.loaded_segments (0x652e4 : word) = Some W_6529c.
Proof. vm_refl. Qed.
Lemma D_6529c : decode_any W_6529c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_652bc : bv 32 := 0xfe010113.
Lemma F_652bc : fetch_word AsanUbsan.M.loaded_segments (0x65304 : word) = Some W_652bc.
Proof. vm_refl. Qed.
Lemma D_652bc : decode_any W_652bc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_652c0 : bv 32 := 0x00113c23.
Lemma F_652c0 : fetch_word AsanUbsan.M.loaded_segments (0x65308 : word) = Some W_652c0.
Proof. vm_refl. Qed.
Lemma D_652c0 : decode_any W_652c0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_652c4 : bv 32 := 0x00813823.
Lemma F_652c4 : fetch_word AsanUbsan.M.loaded_segments (0x6530c : word) = Some W_652c4.
Proof. vm_refl. Qed.
Lemma D_652c4 : decode_any W_652c4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_652c8 : bv 32 := 0x00913423.
Lemma F_652c8 : fetch_word AsanUbsan.M.loaded_segments (0x65310 : word) = Some W_652c8.
Proof. vm_refl. Qed.
Lemma D_652c8 : decode_any W_652c8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_652cc : bv 32 := 0x01213023.
Lemma F_652cc : fetch_word AsanUbsan.M.loaded_segments (0x65314 : word) = Some W_652cc.
Proof. vm_refl. Qed.
Lemma D_652cc : decode_any W_652cc = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_652d0 : bv 32 := 0x02010413.
Lemma F_652d0 : fetch_word AsanUbsan.M.loaded_segments (0x65318 : word) = Some W_652d0.
Proof. vm_refl. Qed.
Lemma D_652d0 : decode_any W_652d0 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_652d4 : bv 32 := 0x000f0517.
Lemma F_652d4 : fetch_word AsanUbsan.M.loaded_segments (0x6531c : word) = Some W_652d4.
Proof. vm_refl. Qed.
Lemma D_652d4 : decode_any W_652d4 = Some (Auipc 10 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_652d8 : bv 32 := 0xff450513.
Lemma F_652d8 : fetch_word AsanUbsan.M.loaded_segments (0x65320 : word) = Some W_652d8.
Proof. vm_refl. Qed.
Lemma D_652d8 : decode_any W_652d8 = Some (OpImm ALU_ADD 10 10 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_652dc : bv 32 := 0x66c050ef.
Lemma F_652dc : fetch_word AsanUbsan.M.loaded_segments (0x65324 : word) = Some W_652dc.
Proof. vm_refl. Qed.
Lemma D_652dc : decode_any W_652dc = Some (Jal 1 22124, 4%Z).
Proof. vm_refl. Qed.

Definition W_652e0 : bv 32 := 0x00053483.
Lemma F_652e0 : fetch_word AsanUbsan.M.loaded_segments (0x65328 : word) = Some W_652e0.
Proof. vm_refl. Qed.
Lemma D_652e0 : decode_any W_652e0 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_652e4 : bv 32 := 0x08048863.
Lemma F_652e4 : fetch_word AsanUbsan.M.loaded_segments (0x6532c : word) = Some W_652e4.
Proof. vm_refl. Qed.
Lemma D_652e4 : decode_any W_652e4 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_652e8 : bv 32 := 0x0604c503.
Lemma F_652e8 : fetch_word AsanUbsan.M.loaded_segments (0x65330 : word) = Some W_652e8.
Proof. vm_refl. Qed.
Lemma D_652e8 : decode_any W_652e8 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_652ec : bv 32 := 0x0584b903.
Lemma F_652ec : fetch_word AsanUbsan.M.loaded_segments (0x65334 : word) = Some W_652ec.
Proof. vm_refl. Qed.
Lemma D_652ec : decode_any W_652ec = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_652f0 : bv 32 := 0x00050863.
Lemma F_652f0 : fetch_word AsanUbsan.M.loaded_segments (0x65338 : word) = Some W_652f0.
Proof. vm_refl. Qed.
Lemma D_652f0 : decode_any W_652f0 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_652f4 : bv 32 := 0x00048513.
Lemma F_652f4 : fetch_word AsanUbsan.M.loaded_segments (0x6533c : word) = Some W_652f4.
Proof. vm_refl. Qed.
Lemma D_652f4 : decode_any W_652f4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_652f8 : bv 32 := 0x00040593.
Lemma F_652f8 : fetch_word AsanUbsan.M.loaded_segments (0x65340 : word) = Some W_652f8.
Proof. vm_refl. Qed.
Lemma D_652f8 : decode_any W_652f8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_652fc : bv 32 := 0xed4ff0ef.
Lemma F_652fc : fetch_word AsanUbsan.M.loaded_segments (0x65344 : word) = Some W_652fc.
Proof. vm_refl. Qed.
Lemma D_652fc : decode_any W_652fc = Some (Jal 1 2094804, 4%Z).
Proof. vm_refl. Qed.

Definition W_65300 : bv 32 := 0xff790593.
Lemma F_65300 : fetch_word AsanUbsan.M.loaded_segments (0x65348 : word) = Some W_65300.
Proof. vm_refl. Qed.
Lemma D_65300 : decode_any W_65300 = Some (OpImm ALU_ADD 11 18 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_65304 : bv 32 := 0x00100513.
Lemma F_65304 : fetch_word AsanUbsan.M.loaded_segments (0x6534c : word) = Some W_65304.
Proof. vm_refl. Qed.
Lemma D_65304 : decode_any W_65304 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65308 : bv 32 := 0x00b51533.
Lemma F_65308 : fetch_word AsanUbsan.M.loaded_segments (0x65350 : word) = Some W_65308.
Proof. vm_refl. Qed.
Lemma D_65308 : decode_any W_65308 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6530c : bv 32 := 0x0005061b.
Lemma F_6530c : fetch_word AsanUbsan.M.loaded_segments (0x65354 : word) = Some W_6530c.
Proof. vm_refl. Qed.
Lemma D_6530c : decode_any W_6530c = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65310 : bv 32 := 0x08c05263.
Lemma F_65310 : fetch_word AsanUbsan.M.loaded_segments (0x65358 : word) = Some W_65310.
Proof. vm_refl. Qed.
Lemma D_65310 : decode_any W_65310 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_65314 : bv 32 := 0x000016b7.
Lemma F_65314 : fetch_word AsanUbsan.M.loaded_segments (0x6535c : word) = Some W_65314.
Proof. vm_refl. Qed.
Lemma D_65314 : decode_any W_65314 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65318 : bv 32 := 0xff190613.
Lemma F_65318 : fetch_word AsanUbsan.M.loaded_segments (0x65360 : word) = Some W_65318.
Proof. vm_refl. Qed.
Lemma D_65318 : decode_any W_65318 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_6531c : bv 32 := 0x38000713.
Lemma F_6531c : fetch_word AsanUbsan.M.loaded_segments (0x65364 : word) = Some W_6531c.
Proof. vm_refl. Qed.
Lemma D_6531c : decode_any W_6531c = Some (OpImm ALU_ADD 14 0 896, 4%Z).
Proof. vm_refl. Qed.

Definition W_65320 : bv 32 := 0xfff00793.
Lemma F_65320 : fetch_word AsanUbsan.M.loaded_segments (0x65368 : word) = Some W_65320.
Proof. vm_refl. Qed.
Lemma D_65320 : decode_any W_65320 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65324 : bv 32 := 0x00c71733.
Lemma F_65324 : fetch_word AsanUbsan.M.loaded_segments (0x6536c : word) = Some W_65324.
Proof. vm_refl. Qed.
Lemma D_65324 : decode_any W_65324 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_65328 : bv 32 := 0x0184b603.
Lemma F_65328 : fetch_word AsanUbsan.M.loaded_segments (0x65370 : word) = Some W_65328.
Proof. vm_refl. Qed.
Lemma D_65328 : decode_any W_65328 = Some (Load SZ8 true 12 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6532c : bv 32 := 0x00b797b3.
Lemma F_6532c : fetch_word AsanUbsan.M.loaded_segments (0x65374 : word) = Some W_6532c.
Proof. vm_refl. Qed.
Lemma D_6532c : decode_any W_6532c = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_65330 : bv 32 := 0xfff50813.
Lemma F_65330 : fetch_word AsanUbsan.M.loaded_segments (0x65378 : word) = Some W_65330.
Proof. vm_refl. Qed.
Lemma D_65330 : decode_any W_65330 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65334 : bv 32 := 0x00d485b3.
Lemma F_65334 : fetch_word AsanUbsan.M.loaded_segments (0x6537c : word) = Some W_65334.
Proof. vm_refl. Qed.
Lemma D_65334 : decode_any W_65334 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_65338 : bv 32 := 0x00e586b3.
Lemma F_65338 : fetch_word AsanUbsan.M.loaded_segments (0x65380 : word) = Some W_65338.
Proof. vm_refl. Qed.
Lemma D_65338 : decode_any W_65338 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6533c : bv 32 := 0xfff7c713.
Lemma F_6533c : fetch_word AsanUbsan.M.loaded_segments (0x65384 : word) = Some W_6533c.
Proof. vm_refl. Qed.
Lemma D_6533c : decode_any W_6533c = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65340 : bv 32 := 0x02081813.
Lemma F_65340 : fetch_word AsanUbsan.M.loaded_segments (0x65388 : word) = Some W_65340.
Proof. vm_refl. Qed.
Lemma D_65340 : decode_any W_65340 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65344 : bv 32 := 0x02085793.
Lemma F_65344 : fetch_word AsanUbsan.M.loaded_segments (0x6538c : word) = Some W_65344.
Proof. vm_refl. Qed.
Lemma D_65344 : decode_any W_65344 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65348 : bv 32 := 0x00f607b3.
Lemma F_65348 : fetch_word AsanUbsan.M.loaded_segments (0x65390 : word) = Some W_65348.
Proof. vm_refl. Qed.
Lemma D_65348 : decode_any W_65348 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6534c : bv 32 := 0x00178813.
Lemma F_6534c : fetch_word AsanUbsan.M.loaded_segments (0x65394 : word) = Some W_6534c.
Proof. vm_refl. Qed.
Lemma D_6534c : decode_any W_6534c = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65350 : bv 32 := 0x00e678b3.
Lemma F_65350 : fetch_word AsanUbsan.M.loaded_segments (0x65398 : word) = Some W_65350.
Proof. vm_refl. Qed.
Lemma D_65350 : decode_any W_65350 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_65354 : bv 32 := 0x011687b3.
Lemma F_65354 : fetch_word AsanUbsan.M.loaded_segments (0x6539c : word) = Some W_65354.
Proof. vm_refl. Qed.
Lemma D_65354 : decode_any W_65354 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_65358 : bv 32 := 0x0007c283.
Lemma F_65358 : fetch_word AsanUbsan.M.loaded_segments (0x653a0 : word) = Some W_65358.
Proof. vm_refl. Qed.
Lemma D_65358 : decode_any W_65358 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6535c : bv 32 := 0x06028663.
Lemma F_6535c : fetch_word AsanUbsan.M.loaded_segments (0x653a4 : word) = Some W_6535c.
Proof. vm_refl. Qed.
Lemma D_6535c : decode_any W_6535c = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_65360 : bv 32 := 0xfff5051b.
Lemma F_65360 : fetch_word AsanUbsan.M.loaded_segments (0x653a8 : word) = Some W_65360.
Proof. vm_refl. Qed.
Lemma D_65360 : decode_any W_65360 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65364 : bv 32 := 0x00160613.
Lemma F_65364 : fetch_word AsanUbsan.M.loaded_segments (0x653ac : word) = Some W_65364.
Proof. vm_refl. Qed.
Lemma D_65364 : decode_any W_65364 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65368 : bv 32 := 0xfe0514e3.
Lemma F_65368 : fetch_word AsanUbsan.M.loaded_segments (0x653b0 : word) = Some W_65368.
Proof. vm_refl. Qed.
Lemma D_65368 : decode_any W_65368 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_653c8 : bv 32 := 0x00160613.
Lemma F_653c8 : fetch_word AsanUbsan.M.loaded_segments (0x65410 : word) = Some W_653c8.
Proof. vm_refl. Qed.
Lemma D_653c8 : decode_any W_653c8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_653cc : bv 32 := 0x00100513.
Lemma F_653cc : fetch_word AsanUbsan.M.loaded_segments (0x65414 : word) = Some W_653cc.
Proof. vm_refl. Qed.
Lemma D_653cc : decode_any W_653cc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_653d0 : bv 32 := 0xffb90693.
Lemma F_653d0 : fetch_word AsanUbsan.M.loaded_segments (0x65418 : word) = Some W_653d0.
Proof. vm_refl. Qed.
Lemma D_653d0 : decode_any W_653d0 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_653d4 : bv 32 := 0x00c4bc23.
Lemma F_653d4 : fetch_word AsanUbsan.M.loaded_segments (0x6541c : word) = Some W_653d4.
Proof. vm_refl. Qed.
Lemma D_653d4 : decode_any W_653d4 = Some (Store SZ8 9 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_653d8 : bv 32 := 0x00a78023.
Lemma F_653d8 : fetch_word AsanUbsan.M.loaded_segments (0x65420 : word) = Some W_653d8.
Proof. vm_refl. Qed.
Lemma D_653d8 : decode_any W_653d8 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_653dc : bv 32 := 0x00d51533.
Lemma F_653dc : fetch_word AsanUbsan.M.loaded_segments (0x65424 : word) = Some W_653dc.
Proof. vm_refl. Qed.
Lemma D_653dc : decode_any W_653dc = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_653e0 : bv 32 := 0x00300613.
Lemma F_653e0 : fetch_word AsanUbsan.M.loaded_segments (0x65428 : word) = Some W_653e0.
Proof. vm_refl. Qed.
Lemma D_653e0 : decode_any W_653e0 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_653e4 : bv 32 := 0x00989893.
Lemma F_653e4 : fetch_word AsanUbsan.M.loaded_segments (0x6542c : word) = Some W_653e4.
Proof. vm_refl. Qed.
Lemma D_653e4 : decode_any W_653e4 = Some (ShiftImm ALU_SLL 17 17 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_653e8 : bv 32 := 0x01261633.
Lemma F_653e8 : fetch_word AsanUbsan.M.loaded_segments (0x65430 : word) = Some W_653e8.
Proof. vm_refl. Qed.
Lemma D_653e8 : decode_any W_653e8 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_653ec : bv 32 := 0x00a58533.
Lemma F_653ec : fetch_word AsanUbsan.M.loaded_segments (0x65434 : word) = Some W_653ec.
Proof. vm_refl. Qed.
Lemma D_653ec : decode_any W_653ec = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_653f0 : bv 32 := 0x01160633.
Lemma F_653f0 : fetch_word AsanUbsan.M.loaded_segments (0x65438 : word) = Some W_653f0.
Proof. vm_refl. Qed.
Lemma D_653f0 : decode_any W_653f0 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_653f4 : bv 32 := 0x00c504b3.
Lemma F_653f4 : fetch_word AsanUbsan.M.loaded_segments (0x6543c : word) = Some W_653f4.
Proof. vm_refl. Qed.
Lemma D_653f4 : decode_any W_653f4 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_653f8 : bv 32 := 0x0084bc23.
Lemma F_653f8 : fetch_word AsanUbsan.M.loaded_segments (0x65440 : word) = Some W_653f8.
Proof. vm_refl. Qed.
Lemma D_653f8 : decode_any W_653f8 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_653fc : bv 32 := 0x1ef4bc23.
Lemma F_653fc : fetch_word AsanUbsan.M.loaded_segments (0x65444 : word) = Some W_653fc.
Proof. vm_refl. Qed.
Lemma D_653fc : decode_any W_653fc = Some (Store SZ8 9 15 504, 4%Z).
Proof. vm_refl. Qed.

Definition W_65400 : bv 32 := 0x00048513.
Lemma F_65400 : fetch_word AsanUbsan.M.loaded_segments (0x65448 : word) = Some W_65400.
Proof. vm_refl. Qed.
Lemma D_65400 : decode_any W_65400 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65404 : bv 32 := 0x4f0000ef.
Lemma F_65404 : fetch_word AsanUbsan.M.loaded_segments (0x6544c : word) = Some W_65404.
Proof. vm_refl. Qed.
Lemma D_65404 : decode_any W_65404 = Some (Jal 1 1264, 4%Z).
Proof. vm_refl. Qed.

Definition W_65408 : bv 32 := 0x00050593.
Lemma F_65408 : fetch_word AsanUbsan.M.loaded_segments (0x65450 : word) = Some W_65408.
Proof. vm_refl. Qed.
Lemma D_65408 : decode_any W_65408 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6540c : bv 32 := 0x00048513.
Lemma F_6540c : fetch_word AsanUbsan.M.loaded_segments (0x65454 : word) = Some W_6540c.
Proof. vm_refl. Qed.
Lemma D_6540c : decode_any W_6540c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65410 : bv 32 := 0x00000613.
Lemma F_65410 : fetch_word AsanUbsan.M.loaded_segments (0x65458 : word) = Some W_65410.
Proof. vm_refl. Qed.
Lemma D_65410 : decode_any W_65410 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65414 : bv 32 := 0x0005b023.
Lemma F_65414 : fetch_word AsanUbsan.M.loaded_segments (0x6545c : word) = Some W_65414.
Proof. vm_refl. Qed.
Lemma D_65414 : decode_any W_65414 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65418 : bv 32 := 0x0005b423.
Lemma F_65418 : fetch_word AsanUbsan.M.loaded_segments (0x65460 : word) = Some W_65418.
Proof. vm_refl. Qed.
Lemma D_65418 : decode_any W_65418 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6541c : bv 32 := 0x0005b823.
Lemma F_6541c : fetch_word AsanUbsan.M.loaded_segments (0x65464 : word) = Some W_6541c.
Proof. vm_refl. Qed.
Lemma D_6541c : decode_any W_6541c = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65420 : bv 32 := 0x0005bc23.
Lemma F_65420 : fetch_word AsanUbsan.M.loaded_segments (0x65468 : word) = Some W_65420.
Proof. vm_refl. Qed.
Lemma D_65420 : decode_any W_65420 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65424 : bv 32 := 0x0205b023.
Lemma F_65424 : fetch_word AsanUbsan.M.loaded_segments (0x6546c : word) = Some W_65424.
Proof. vm_refl. Qed.
Lemma D_65424 : decode_any W_65424 = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65428 : bv 32 := 0x0205b423.
Lemma F_65428 : fetch_word AsanUbsan.M.loaded_segments (0x65470 : word) = Some W_65428.
Proof. vm_refl. Qed.
Lemma D_65428 : decode_any W_65428 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6542c : bv 32 := 0x0205b823.
Lemma F_6542c : fetch_word AsanUbsan.M.loaded_segments (0x65474 : word) = Some W_6542c.
Proof. vm_refl. Qed.
Lemma D_6542c : decode_any W_6542c = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_65430 : bv 32 := 0x0205bc23.
Lemma F_65430 : fetch_word AsanUbsan.M.loaded_segments (0x65478 : word) = Some W_65430.
Proof. vm_refl. Qed.
Lemma D_65430 : decode_any W_65430 = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_65434 : bv 32 := 0x01813083.
Lemma F_65434 : fetch_word AsanUbsan.M.loaded_segments (0x6547c : word) = Some W_65434.
Proof. vm_refl. Qed.
Lemma D_65434 : decode_any W_65434 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65438 : bv 32 := 0x01013403.
Lemma F_65438 : fetch_word AsanUbsan.M.loaded_segments (0x65480 : word) = Some W_65438.
Proof. vm_refl. Qed.
Lemma D_65438 : decode_any W_65438 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6543c : bv 32 := 0x00813483.
Lemma F_6543c : fetch_word AsanUbsan.M.loaded_segments (0x65484 : word) = Some W_6543c.
Proof. vm_refl. Qed.
Lemma D_6543c : decode_any W_6543c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65440 : bv 32 := 0x00013903.
Lemma F_65440 : fetch_word AsanUbsan.M.loaded_segments (0x65488 : word) = Some W_65440.
Proof. vm_refl. Qed.
Lemma D_65440 : decode_any W_65440 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65444 : bv 32 := 0x02010113.
Lemma F_65444 : fetch_word AsanUbsan.M.loaded_segments (0x6548c : word) = Some W_65444.
Proof. vm_refl. Qed.
Lemma D_65444 : decode_any W_65444 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65448 : bv 32 := 0x00008067.
Lemma F_65448 : fetch_word AsanUbsan.M.loaded_segments (0x65490 : word) = Some W_65448.
Proof. vm_refl. Qed.
Lemma D_65448 : decode_any W_65448 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65468 : bv 32 := 0xfe010113.
Lemma F_65468 : fetch_word AsanUbsan.M.loaded_segments (0x654b0 : word) = Some W_65468.
Proof. vm_refl. Qed.
Lemma D_65468 : decode_any W_65468 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6546c : bv 32 := 0x00113c23.
Lemma F_6546c : fetch_word AsanUbsan.M.loaded_segments (0x654b4 : word) = Some W_6546c.
Proof. vm_refl. Qed.
Lemma D_6546c : decode_any W_6546c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65470 : bv 32 := 0x00813823.
Lemma F_65470 : fetch_word AsanUbsan.M.loaded_segments (0x654b8 : word) = Some W_65470.
Proof. vm_refl. Qed.
Lemma D_65470 : decode_any W_65470 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65474 : bv 32 := 0x00913423.
Lemma F_65474 : fetch_word AsanUbsan.M.loaded_segments (0x654bc : word) = Some W_65474.
Proof. vm_refl. Qed.
Lemma D_65474 : decode_any W_65474 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65478 : bv 32 := 0x01213023.
Lemma F_65478 : fetch_word AsanUbsan.M.loaded_segments (0x654c0 : word) = Some W_65478.
Proof. vm_refl. Qed.
Lemma D_65478 : decode_any W_65478 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6547c : bv 32 := 0x02010413.
Lemma F_6547c : fetch_word AsanUbsan.M.loaded_segments (0x654c4 : word) = Some W_6547c.
Proof. vm_refl. Qed.
Lemma D_6547c : decode_any W_6547c = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65480 : bv 32 := 0x000f0517.
Lemma F_65480 : fetch_word AsanUbsan.M.loaded_segments (0x654c8 : word) = Some W_65480.
Proof. vm_refl. Qed.
Lemma D_65480 : decode_any W_65480 = Some (Auipc 10 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_65484 : bv 32 := 0xe4850513.
Lemma F_65484 : fetch_word AsanUbsan.M.loaded_segments (0x654cc : word) = Some W_65484.
Proof. vm_refl. Qed.
Lemma D_65484 : decode_any W_65484 = Some (OpImm ALU_ADD 10 10 3656, 4%Z).
Proof. vm_refl. Qed.

Definition W_65488 : bv 32 := 0x4c0050ef.
Lemma F_65488 : fetch_word AsanUbsan.M.loaded_segments (0x654d0 : word) = Some W_65488.
Proof. vm_refl. Qed.
Lemma D_65488 : decode_any W_65488 = Some (Jal 1 21696, 4%Z).
Proof. vm_refl. Qed.

Definition W_6548c : bv 32 := 0x00053483.
Lemma F_6548c : fetch_word AsanUbsan.M.loaded_segments (0x654d4 : word) = Some W_6548c.
Proof. vm_refl. Qed.
Lemma D_6548c : decode_any W_6548c = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65490 : bv 32 := 0x08048863.
Lemma F_65490 : fetch_word AsanUbsan.M.loaded_segments (0x654d8 : word) = Some W_65490.
Proof. vm_refl. Qed.
Lemma D_65490 : decode_any W_65490 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_65494 : bv 32 := 0x0604c503.
Lemma F_65494 : fetch_word AsanUbsan.M.loaded_segments (0x654dc : word) = Some W_65494.
Proof. vm_refl. Qed.
Lemma D_65494 : decode_any W_65494 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_65498 : bv 32 := 0x0584b903.
Lemma F_65498 : fetch_word AsanUbsan.M.loaded_segments (0x654e0 : word) = Some W_65498.
Proof. vm_refl. Qed.
Lemma D_65498 : decode_any W_65498 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_6549c : bv 32 := 0x00050863.
Lemma F_6549c : fetch_word AsanUbsan.M.loaded_segments (0x654e4 : word) = Some W_6549c.
Proof. vm_refl. Qed.
Lemma D_6549c : decode_any W_6549c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_654a0 : bv 32 := 0x00048513.
Lemma F_654a0 : fetch_word AsanUbsan.M.loaded_segments (0x654e8 : word) = Some W_654a0.
Proof. vm_refl. Qed.
Lemma D_654a0 : decode_any W_654a0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_654a4 : bv 32 := 0x00040593.
Lemma F_654a4 : fetch_word AsanUbsan.M.loaded_segments (0x654ec : word) = Some W_654a4.
Proof. vm_refl. Qed.
Lemma D_654a4 : decode_any W_654a4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_654a8 : bv 32 := 0xd28ff0ef.
Lemma F_654a8 : fetch_word AsanUbsan.M.loaded_segments (0x654f0 : word) = Some W_654a8.
Proof. vm_refl. Qed.
Lemma D_654a8 : decode_any W_654a8 = Some (Jal 1 2094376, 4%Z).
Proof. vm_refl. Qed.

Definition W_654ac : bv 32 := 0xff690593.
Lemma F_654ac : fetch_word AsanUbsan.M.loaded_segments (0x654f4 : word) = Some W_654ac.
Proof. vm_refl. Qed.
Lemma D_654ac : decode_any W_654ac = Some (OpImm ALU_ADD 11 18 4086, 4%Z).
Proof. vm_refl. Qed.

Definition W_654b0 : bv 32 := 0x00100513.
Lemma F_654b0 : fetch_word AsanUbsan.M.loaded_segments (0x654f8 : word) = Some W_654b0.
Proof. vm_refl. Qed.
Lemma D_654b0 : decode_any W_654b0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_654b4 : bv 32 := 0x00b51533.
Lemma F_654b4 : fetch_word AsanUbsan.M.loaded_segments (0x654fc : word) = Some W_654b4.
Proof. vm_refl. Qed.
Lemma D_654b4 : decode_any W_654b4 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_654b8 : bv 32 := 0x0005061b.
Lemma F_654b8 : fetch_word AsanUbsan.M.loaded_segments (0x65500 : word) = Some W_654b8.
Proof. vm_refl. Qed.
Lemma D_654b8 : decode_any W_654b8 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_654bc : bv 32 := 0x08c05263.
Lemma F_654bc : fetch_word AsanUbsan.M.loaded_segments (0x65504 : word) = Some W_654bc.
Proof. vm_refl. Qed.
Lemma D_654bc : decode_any W_654bc = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_654c0 : bv 32 := 0x000016b7.
Lemma F_654c0 : fetch_word AsanUbsan.M.loaded_segments (0x65508 : word) = Some W_654c0.
Proof. vm_refl. Qed.
Lemma D_654c0 : decode_any W_654c0 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_654c4 : bv 32 := 0xff190613.
Lemma F_654c4 : fetch_word AsanUbsan.M.loaded_segments (0x6550c : word) = Some W_654c4.
Proof. vm_refl. Qed.
Lemma D_654c4 : decode_any W_654c4 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_654c8 : bv 32 := 0x3c000713.
Lemma F_654c8 : fetch_word AsanUbsan.M.loaded_segments (0x65510 : word) = Some W_654c8.
Proof. vm_refl. Qed.
Lemma D_654c8 : decode_any W_654c8 = Some (OpImm ALU_ADD 14 0 960, 4%Z).
Proof. vm_refl. Qed.

Definition W_654cc : bv 32 := 0xfff00793.
Lemma F_654cc : fetch_word AsanUbsan.M.loaded_segments (0x65514 : word) = Some W_654cc.
Proof. vm_refl. Qed.
Lemma D_654cc : decode_any W_654cc = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_654d0 : bv 32 := 0x00c71733.
Lemma F_654d0 : fetch_word AsanUbsan.M.loaded_segments (0x65518 : word) = Some W_654d0.
Proof. vm_refl. Qed.
Lemma D_654d0 : decode_any W_654d0 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_654d4 : bv 32 := 0x0204b603.
Lemma F_654d4 : fetch_word AsanUbsan.M.loaded_segments (0x6551c : word) = Some W_654d4.
Proof. vm_refl. Qed.
Lemma D_654d4 : decode_any W_654d4 = Some (Load SZ8 true 12 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_654d8 : bv 32 := 0x00b797b3.
Lemma F_654d8 : fetch_word AsanUbsan.M.loaded_segments (0x65520 : word) = Some W_654d8.
Proof. vm_refl. Qed.
Lemma D_654d8 : decode_any W_654d8 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_654dc : bv 32 := 0xfff50813.
Lemma F_654dc : fetch_word AsanUbsan.M.loaded_segments (0x65524 : word) = Some W_654dc.
Proof. vm_refl. Qed.
Lemma D_654dc : decode_any W_654dc = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_654e0 : bv 32 := 0x00d485b3.
Lemma F_654e0 : fetch_word AsanUbsan.M.loaded_segments (0x65528 : word) = Some W_654e0.
Proof. vm_refl. Qed.
Lemma D_654e0 : decode_any W_654e0 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_654e4 : bv 32 := 0x00e586b3.
Lemma F_654e4 : fetch_word AsanUbsan.M.loaded_segments (0x6552c : word) = Some W_654e4.
Proof. vm_refl. Qed.
Lemma D_654e4 : decode_any W_654e4 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_654e8 : bv 32 := 0xfff7c713.
Lemma F_654e8 : fetch_word AsanUbsan.M.loaded_segments (0x65530 : word) = Some W_654e8.
Proof. vm_refl. Qed.
Lemma D_654e8 : decode_any W_654e8 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_654ec : bv 32 := 0x02081813.
Lemma F_654ec : fetch_word AsanUbsan.M.loaded_segments (0x65534 : word) = Some W_654ec.
Proof. vm_refl. Qed.
Lemma D_654ec : decode_any W_654ec = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_654f0 : bv 32 := 0x02085793.
Lemma F_654f0 : fetch_word AsanUbsan.M.loaded_segments (0x65538 : word) = Some W_654f0.
Proof. vm_refl. Qed.
Lemma D_654f0 : decode_any W_654f0 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_654f4 : bv 32 := 0x00f607b3.
Lemma F_654f4 : fetch_word AsanUbsan.M.loaded_segments (0x6553c : word) = Some W_654f4.
Proof. vm_refl. Qed.
Lemma D_654f4 : decode_any W_654f4 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_654f8 : bv 32 := 0x00178813.
Lemma F_654f8 : fetch_word AsanUbsan.M.loaded_segments (0x65540 : word) = Some W_654f8.
Proof. vm_refl. Qed.
Lemma D_654f8 : decode_any W_654f8 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_654fc : bv 32 := 0x00e678b3.
Lemma F_654fc : fetch_word AsanUbsan.M.loaded_segments (0x65544 : word) = Some W_654fc.
Proof. vm_refl. Qed.
Lemma D_654fc : decode_any W_654fc = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_65500 : bv 32 := 0x011687b3.
Lemma F_65500 : fetch_word AsanUbsan.M.loaded_segments (0x65548 : word) = Some W_65500.
Proof. vm_refl. Qed.
Lemma D_65500 : decode_any W_65500 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_65504 : bv 32 := 0x0007c283.
Lemma F_65504 : fetch_word AsanUbsan.M.loaded_segments (0x6554c : word) = Some W_65504.
Proof. vm_refl. Qed.
Lemma D_65504 : decode_any W_65504 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65508 : bv 32 := 0x06028663.
Lemma F_65508 : fetch_word AsanUbsan.M.loaded_segments (0x65550 : word) = Some W_65508.
Proof. vm_refl. Qed.
Lemma D_65508 : decode_any W_65508 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_6550c : bv 32 := 0xfff5051b.
Lemma F_6550c : fetch_word AsanUbsan.M.loaded_segments (0x65554 : word) = Some W_6550c.
Proof. vm_refl. Qed.
Lemma D_6550c : decode_any W_6550c = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65510 : bv 32 := 0x00160613.
Lemma F_65510 : fetch_word AsanUbsan.M.loaded_segments (0x65558 : word) = Some W_65510.
Proof. vm_refl. Qed.
Lemma D_65510 : decode_any W_65510 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65514 : bv 32 := 0xfe0514e3.
Lemma F_65514 : fetch_word AsanUbsan.M.loaded_segments (0x6555c : word) = Some W_65514.
Proof. vm_refl. Qed.
Lemma D_65514 : decode_any W_65514 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_65574 : bv 32 := 0x00160613.
Lemma F_65574 : fetch_word AsanUbsan.M.loaded_segments (0x655bc : word) = Some W_65574.
Proof. vm_refl. Qed.
Lemma D_65574 : decode_any W_65574 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65578 : bv 32 := 0x00100513.
Lemma F_65578 : fetch_word AsanUbsan.M.loaded_segments (0x655c0 : word) = Some W_65578.
Proof. vm_refl. Qed.
Lemma D_65578 : decode_any W_65578 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6557c : bv 32 := 0xffb90693.
Lemma F_6557c : fetch_word AsanUbsan.M.loaded_segments (0x655c4 : word) = Some W_6557c.
Proof. vm_refl. Qed.
Lemma D_6557c : decode_any W_6557c = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_65580 : bv 32 := 0x02c4b023.
Lemma F_65580 : fetch_word AsanUbsan.M.loaded_segments (0x655c8 : word) = Some W_65580.
Proof. vm_refl. Qed.
Lemma D_65580 : decode_any W_65580 = Some (Store SZ8 9 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65584 : bv 32 := 0x00a78023.
Lemma F_65584 : fetch_word AsanUbsan.M.loaded_segments (0x655cc : word) = Some W_65584.
Proof. vm_refl. Qed.
Lemma D_65584 : decode_any W_65584 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65588 : bv 32 := 0x00d51533.
Lemma F_65588 : fetch_word AsanUbsan.M.loaded_segments (0x655d0 : word) = Some W_65588.
Proof. vm_refl. Qed.
Lemma D_65588 : decode_any W_65588 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6558c : bv 32 := 0x00400613.
Lemma F_6558c : fetch_word AsanUbsan.M.loaded_segments (0x655d4 : word) = Some W_6558c.
Proof. vm_refl. Qed.
Lemma D_6558c : decode_any W_6558c = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_65590 : bv 32 := 0x00a89893.
Lemma F_65590 : fetch_word AsanUbsan.M.loaded_segments (0x655d8 : word) = Some W_65590.
Proof. vm_refl. Qed.
Lemma D_65590 : decode_any W_65590 = Some (ShiftImm ALU_SLL 17 17 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_65594 : bv 32 := 0x01261633.
Lemma F_65594 : fetch_word AsanUbsan.M.loaded_segments (0x655dc : word) = Some W_65594.
Proof. vm_refl. Qed.
Lemma D_65594 : decode_any W_65594 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_65598 : bv 32 := 0x00a58533.
Lemma F_65598 : fetch_word AsanUbsan.M.loaded_segments (0x655e0 : word) = Some W_65598.
Proof. vm_refl. Qed.
Lemma D_65598 : decode_any W_65598 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6559c : bv 32 := 0x01160633.
Lemma F_6559c : fetch_word AsanUbsan.M.loaded_segments (0x655e4 : word) = Some W_6559c.
Proof. vm_refl. Qed.
Lemma D_6559c : decode_any W_6559c = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_655a0 : bv 32 := 0x00c504b3.
Lemma F_655a0 : fetch_word AsanUbsan.M.loaded_segments (0x655e8 : word) = Some W_655a0.
Proof. vm_refl. Qed.
Lemma D_655a0 : decode_any W_655a0 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_655a4 : bv 32 := 0x0084bc23.
Lemma F_655a4 : fetch_word AsanUbsan.M.loaded_segments (0x655ec : word) = Some W_655a4.
Proof. vm_refl. Qed.
Lemma D_655a4 : decode_any W_655a4 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_655a8 : bv 32 := 0x3ef4bc23.
Lemma F_655a8 : fetch_word AsanUbsan.M.loaded_segments (0x655f0 : word) = Some W_655a8.
Proof. vm_refl. Qed.
Lemma D_655a8 : decode_any W_655a8 = Some (Store SZ8 9 15 1016, 4%Z).
Proof. vm_refl. Qed.

Definition W_655ac : bv 32 := 0x00048513.
Lemma F_655ac : fetch_word AsanUbsan.M.loaded_segments (0x655f4 : word) = Some W_655ac.
Proof. vm_refl. Qed.
Lemma D_655ac : decode_any W_655ac = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_655b0 : bv 32 := 0x344000ef.
Lemma F_655b0 : fetch_word AsanUbsan.M.loaded_segments (0x655f8 : word) = Some W_655b0.
Proof. vm_refl. Qed.
Lemma D_655b0 : decode_any W_655b0 = Some (Jal 1 836, 4%Z).
Proof. vm_refl. Qed.

Definition W_655b4 : bv 32 := 0x00050593.
Lemma F_655b4 : fetch_word AsanUbsan.M.loaded_segments (0x655fc : word) = Some W_655b4.
Proof. vm_refl. Qed.
Lemma D_655b4 : decode_any W_655b4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_655b8 : bv 32 := 0x00048513.
Lemma F_655b8 : fetch_word AsanUbsan.M.loaded_segments (0x65600 : word) = Some W_655b8.
Proof. vm_refl. Qed.
Lemma D_655b8 : decode_any W_655b8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_655bc : bv 32 := 0x00000613.
Lemma F_655bc : fetch_word AsanUbsan.M.loaded_segments (0x65604 : word) = Some W_655bc.
Proof. vm_refl. Qed.
Lemma D_655bc : decode_any W_655bc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_655c0 : bv 32 := 0x0005b023.
Lemma F_655c0 : fetch_word AsanUbsan.M.loaded_segments (0x65608 : word) = Some W_655c0.
Proof. vm_refl. Qed.
Lemma D_655c0 : decode_any W_655c0 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_655c4 : bv 32 := 0x0005b423.
Lemma F_655c4 : fetch_word AsanUbsan.M.loaded_segments (0x6560c : word) = Some W_655c4.
Proof. vm_refl. Qed.
Lemma D_655c4 : decode_any W_655c4 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_655c8 : bv 32 := 0x0005b823.
Lemma F_655c8 : fetch_word AsanUbsan.M.loaded_segments (0x65610 : word) = Some W_655c8.
Proof. vm_refl. Qed.
Lemma D_655c8 : decode_any W_655c8 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_655cc : bv 32 := 0x0005bc23.
Lemma F_655cc : fetch_word AsanUbsan.M.loaded_segments (0x65614 : word) = Some W_655cc.
Proof. vm_refl. Qed.
Lemma D_655cc : decode_any W_655cc = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_655d0 : bv 32 := 0x0205b023.
Lemma F_655d0 : fetch_word AsanUbsan.M.loaded_segments (0x65618 : word) = Some W_655d0.
Proof. vm_refl. Qed.
Lemma D_655d0 : decode_any W_655d0 = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_655d4 : bv 32 := 0x0205b423.
Lemma F_655d4 : fetch_word AsanUbsan.M.loaded_segments (0x6561c : word) = Some W_655d4.
Proof. vm_refl. Qed.
Lemma D_655d4 : decode_any W_655d4 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_655d8 : bv 32 := 0x0205b823.
Lemma F_655d8 : fetch_word AsanUbsan.M.loaded_segments (0x65620 : word) = Some W_655d8.
Proof. vm_refl. Qed.
Lemma D_655d8 : decode_any W_655d8 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_655dc : bv 32 := 0x0205bc23.
Lemma F_655dc : fetch_word AsanUbsan.M.loaded_segments (0x65624 : word) = Some W_655dc.
Proof. vm_refl. Qed.
Lemma D_655dc : decode_any W_655dc = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_655e0 : bv 32 := 0x0405b023.
Lemma F_655e0 : fetch_word AsanUbsan.M.loaded_segments (0x65628 : word) = Some W_655e0.
Proof. vm_refl. Qed.
Lemma D_655e0 : decode_any W_655e0 = Some (Store SZ8 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_655e4 : bv 32 := 0x0405b423.
Lemma F_655e4 : fetch_word AsanUbsan.M.loaded_segments (0x6562c : word) = Some W_655e4.
Proof. vm_refl. Qed.
Lemma D_655e4 : decode_any W_655e4 = Some (Store SZ8 11 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_655e8 : bv 32 := 0x0405b823.
Lemma F_655e8 : fetch_word AsanUbsan.M.loaded_segments (0x65630 : word) = Some W_655e8.
Proof. vm_refl. Qed.
Lemma D_655e8 : decode_any W_655e8 = Some (Store SZ8 11 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_655ec : bv 32 := 0x0405bc23.
Lemma F_655ec : fetch_word AsanUbsan.M.loaded_segments (0x65634 : word) = Some W_655ec.
Proof. vm_refl. Qed.
Lemma D_655ec : decode_any W_655ec = Some (Store SZ8 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_655f0 : bv 32 := 0x0605b023.
Lemma F_655f0 : fetch_word AsanUbsan.M.loaded_segments (0x65638 : word) = Some W_655f0.
Proof. vm_refl. Qed.
Lemma D_655f0 : decode_any W_655f0 = Some (Store SZ8 11 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_655f4 : bv 32 := 0x0605b423.
Lemma F_655f4 : fetch_word AsanUbsan.M.loaded_segments (0x6563c : word) = Some W_655f4.
Proof. vm_refl. Qed.
Lemma D_655f4 : decode_any W_655f4 = Some (Store SZ8 11 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_655f8 : bv 32 := 0x0605b823.
Lemma F_655f8 : fetch_word AsanUbsan.M.loaded_segments (0x65640 : word) = Some W_655f8.
Proof. vm_refl. Qed.
Lemma D_655f8 : decode_any W_655f8 = Some (Store SZ8 11 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_655fc : bv 32 := 0x0605bc23.
Lemma F_655fc : fetch_word AsanUbsan.M.loaded_segments (0x65644 : word) = Some W_655fc.
Proof. vm_refl. Qed.
Lemma D_655fc : decode_any W_655fc = Some (Store SZ8 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_65600 : bv 32 := 0x01813083.
Lemma F_65600 : fetch_word AsanUbsan.M.loaded_segments (0x65648 : word) = Some W_65600.
Proof. vm_refl. Qed.
Lemma D_65600 : decode_any W_65600 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65604 : bv 32 := 0x01013403.
Lemma F_65604 : fetch_word AsanUbsan.M.loaded_segments (0x6564c : word) = Some W_65604.
Proof. vm_refl. Qed.
Lemma D_65604 : decode_any W_65604 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65608 : bv 32 := 0x00813483.
Lemma F_65608 : fetch_word AsanUbsan.M.loaded_segments (0x65650 : word) = Some W_65608.
Proof. vm_refl. Qed.
Lemma D_65608 : decode_any W_65608 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6560c : bv 32 := 0x00013903.
Lemma F_6560c : fetch_word AsanUbsan.M.loaded_segments (0x65654 : word) = Some W_6560c.
Proof. vm_refl. Qed.
Lemma D_6560c : decode_any W_6560c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65610 : bv 32 := 0x02010113.
Lemma F_65610 : fetch_word AsanUbsan.M.loaded_segments (0x65658 : word) = Some W_65610.
Proof. vm_refl. Qed.
Lemma D_65610 : decode_any W_65610 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65614 : bv 32 := 0x00008067.
Lemma F_65614 : fetch_word AsanUbsan.M.loaded_segments (0x6565c : word) = Some W_65614.
Proof. vm_refl. Qed.
Lemma D_65614 : decode_any W_65614 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65634 : bv 32 := 0xfe010113.
Lemma F_65634 : fetch_word AsanUbsan.M.loaded_segments (0x6567c : word) = Some W_65634.
Proof. vm_refl. Qed.
Lemma D_65634 : decode_any W_65634 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_65638 : bv 32 := 0x00113c23.
Lemma F_65638 : fetch_word AsanUbsan.M.loaded_segments (0x65680 : word) = Some W_65638.
Proof. vm_refl. Qed.
Lemma D_65638 : decode_any W_65638 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6563c : bv 32 := 0x00813823.
Lemma F_6563c : fetch_word AsanUbsan.M.loaded_segments (0x65684 : word) = Some W_6563c.
Proof. vm_refl. Qed.
Lemma D_6563c : decode_any W_6563c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65640 : bv 32 := 0x00913423.
Lemma F_65640 : fetch_word AsanUbsan.M.loaded_segments (0x65688 : word) = Some W_65640.
Proof. vm_refl. Qed.
Lemma D_65640 : decode_any W_65640 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65644 : bv 32 := 0x01213023.
Lemma F_65644 : fetch_word AsanUbsan.M.loaded_segments (0x6568c : word) = Some W_65644.
Proof. vm_refl. Qed.
Lemma D_65644 : decode_any W_65644 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65648 : bv 32 := 0x02010413.
Lemma F_65648 : fetch_word AsanUbsan.M.loaded_segments (0x65690 : word) = Some W_65648.
Proof. vm_refl. Qed.
Lemma D_65648 : decode_any W_65648 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6564c : bv 32 := 0x000f0517.
Lemma F_6564c : fetch_word AsanUbsan.M.loaded_segments (0x65694 : word) = Some W_6564c.
Proof. vm_refl. Qed.
Lemma D_6564c : decode_any W_6564c = Some (Auipc 10 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_65650 : bv 32 := 0xc7c50513.
Lemma F_65650 : fetch_word AsanUbsan.M.loaded_segments (0x65698 : word) = Some W_65650.
Proof. vm_refl. Qed.
Lemma D_65650 : decode_any W_65650 = Some (OpImm ALU_ADD 10 10 3196, 4%Z).
Proof. vm_refl. Qed.

Definition W_65654 : bv 32 := 0x2f4050ef.
Lemma F_65654 : fetch_word AsanUbsan.M.loaded_segments (0x6569c : word) = Some W_65654.
Proof. vm_refl. Qed.
Lemma D_65654 : decode_any W_65654 = Some (Jal 1 21236, 4%Z).
Proof. vm_refl. Qed.

Definition W_65658 : bv 32 := 0x00053483.
Lemma F_65658 : fetch_word AsanUbsan.M.loaded_segments (0x656a0 : word) = Some W_65658.
Proof. vm_refl. Qed.
Lemma D_65658 : decode_any W_65658 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6565c : bv 32 := 0x08048863.
Lemma F_6565c : fetch_word AsanUbsan.M.loaded_segments (0x656a4 : word) = Some W_6565c.
Proof. vm_refl. Qed.
Lemma D_6565c : decode_any W_6565c = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_65660 : bv 32 := 0x0604c503.
Lemma F_65660 : fetch_word AsanUbsan.M.loaded_segments (0x656a8 : word) = Some W_65660.
Proof. vm_refl. Qed.
Lemma D_65660 : decode_any W_65660 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_65664 : bv 32 := 0x0584b903.
Lemma F_65664 : fetch_word AsanUbsan.M.loaded_segments (0x656ac : word) = Some W_65664.
Proof. vm_refl. Qed.
Lemma D_65664 : decode_any W_65664 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_65668 : bv 32 := 0x00050863.
Lemma F_65668 : fetch_word AsanUbsan.M.loaded_segments (0x656b0 : word) = Some W_65668.
Proof. vm_refl. Qed.
Lemma D_65668 : decode_any W_65668 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6566c : bv 32 := 0x00048513.
Lemma F_6566c : fetch_word AsanUbsan.M.loaded_segments (0x656b4 : word) = Some W_6566c.
Proof. vm_refl. Qed.
Lemma D_6566c : decode_any W_6566c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65670 : bv 32 := 0x00040593.
Lemma F_65670 : fetch_word AsanUbsan.M.loaded_segments (0x656b8 : word) = Some W_65670.
Proof. vm_refl. Qed.
Lemma D_65670 : decode_any W_65670 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65674 : bv 32 := 0xb5cff0ef.
Lemma F_65674 : fetch_word AsanUbsan.M.loaded_segments (0x656bc : word) = Some W_65674.
Proof. vm_refl. Qed.
Lemma D_65674 : decode_any W_65674 = Some (Jal 1 2093916, 4%Z).
Proof. vm_refl. Qed.

Definition W_65678 : bv 32 := 0xff590593.
Lemma F_65678 : fetch_word AsanUbsan.M.loaded_segments (0x656c0 : word) = Some W_65678.
Proof. vm_refl. Qed.
Lemma D_65678 : decode_any W_65678 = Some (OpImm ALU_ADD 11 18 4085, 4%Z).
Proof. vm_refl. Qed.

Definition W_6567c : bv 32 := 0x00100513.
Lemma F_6567c : fetch_word AsanUbsan.M.loaded_segments (0x656c4 : word) = Some W_6567c.
Proof. vm_refl. Qed.
Lemma D_6567c : decode_any W_6567c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65680 : bv 32 := 0x00b51533.
Lemma F_65680 : fetch_word AsanUbsan.M.loaded_segments (0x656c8 : word) = Some W_65680.
Proof. vm_refl. Qed.
Lemma D_65680 : decode_any W_65680 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_65684 : bv 32 := 0x0005061b.
Lemma F_65684 : fetch_word AsanUbsan.M.loaded_segments (0x656cc : word) = Some W_65684.
Proof. vm_refl. Qed.
Lemma D_65684 : decode_any W_65684 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65688 : bv 32 := 0x08c05263.
Lemma F_65688 : fetch_word AsanUbsan.M.loaded_segments (0x656d0 : word) = Some W_65688.
Proof. vm_refl. Qed.
Lemma D_65688 : decode_any W_65688 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_6568c : bv 32 := 0x000016b7.
Lemma F_6568c : fetch_word AsanUbsan.M.loaded_segments (0x656d4 : word) = Some W_6568c.
Proof. vm_refl. Qed.
Lemma D_6568c : decode_any W_6568c = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65690 : bv 32 := 0xff190613.
Lemma F_65690 : fetch_word AsanUbsan.M.loaded_segments (0x656d8 : word) = Some W_65690.
Proof. vm_refl. Qed.
Lemma D_65690 : decode_any W_65690 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_65694 : bv 32 := 0x3e000713.
Lemma F_65694 : fetch_word AsanUbsan.M.loaded_segments (0x656dc : word) = Some W_65694.
Proof. vm_refl. Qed.
Lemma D_65694 : decode_any W_65694 = Some (OpImm ALU_ADD 14 0 992, 4%Z).
Proof. vm_refl. Qed.

Definition W_65698 : bv 32 := 0xfff00793.
Lemma F_65698 : fetch_word AsanUbsan.M.loaded_segments (0x656e0 : word) = Some W_65698.
Proof. vm_refl. Qed.
Lemma D_65698 : decode_any W_65698 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6569c : bv 32 := 0x00c71733.
Lemma F_6569c : fetch_word AsanUbsan.M.loaded_segments (0x656e4 : word) = Some W_6569c.
Proof. vm_refl. Qed.
Lemma D_6569c : decode_any W_6569c = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_656a0 : bv 32 := 0x0284b603.
Lemma F_656a0 : fetch_word AsanUbsan.M.loaded_segments (0x656e8 : word) = Some W_656a0.
Proof. vm_refl. Qed.
Lemma D_656a0 : decode_any W_656a0 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_656a4 : bv 32 := 0x00b797b3.
Lemma F_656a4 : fetch_word AsanUbsan.M.loaded_segments (0x656ec : word) = Some W_656a4.
Proof. vm_refl. Qed.
Lemma D_656a4 : decode_any W_656a4 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_656a8 : bv 32 := 0xfff50813.
Lemma F_656a8 : fetch_word AsanUbsan.M.loaded_segments (0x656f0 : word) = Some W_656a8.
Proof. vm_refl. Qed.
Lemma D_656a8 : decode_any W_656a8 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_656ac : bv 32 := 0x00d485b3.
Lemma F_656ac : fetch_word AsanUbsan.M.loaded_segments (0x656f4 : word) = Some W_656ac.
Proof. vm_refl. Qed.
Lemma D_656ac : decode_any W_656ac = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_656b0 : bv 32 := 0x00e586b3.
Lemma F_656b0 : fetch_word AsanUbsan.M.loaded_segments (0x656f8 : word) = Some W_656b0.
Proof. vm_refl. Qed.
Lemma D_656b0 : decode_any W_656b0 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_656b4 : bv 32 := 0xfff7c713.
Lemma F_656b4 : fetch_word AsanUbsan.M.loaded_segments (0x656fc : word) = Some W_656b4.
Proof. vm_refl. Qed.
Lemma D_656b4 : decode_any W_656b4 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_656b8 : bv 32 := 0x02081813.
Lemma F_656b8 : fetch_word AsanUbsan.M.loaded_segments (0x65700 : word) = Some W_656b8.
Proof. vm_refl. Qed.
Lemma D_656b8 : decode_any W_656b8 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_656bc : bv 32 := 0x02085793.
Lemma F_656bc : fetch_word AsanUbsan.M.loaded_segments (0x65704 : word) = Some W_656bc.
Proof. vm_refl. Qed.
Lemma D_656bc : decode_any W_656bc = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_656c0 : bv 32 := 0x00f607b3.
Lemma F_656c0 : fetch_word AsanUbsan.M.loaded_segments (0x65708 : word) = Some W_656c0.
Proof. vm_refl. Qed.
Lemma D_656c0 : decode_any W_656c0 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_656c4 : bv 32 := 0x00178813.
Lemma F_656c4 : fetch_word AsanUbsan.M.loaded_segments (0x6570c : word) = Some W_656c4.
Proof. vm_refl. Qed.
Lemma D_656c4 : decode_any W_656c4 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_656c8 : bv 32 := 0x00e678b3.
Lemma F_656c8 : fetch_word AsanUbsan.M.loaded_segments (0x65710 : word) = Some W_656c8.
Proof. vm_refl. Qed.
Lemma D_656c8 : decode_any W_656c8 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_656cc : bv 32 := 0x011687b3.
Lemma F_656cc : fetch_word AsanUbsan.M.loaded_segments (0x65714 : word) = Some W_656cc.
Proof. vm_refl. Qed.
Lemma D_656cc : decode_any W_656cc = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_656d0 : bv 32 := 0x0007c283.
Lemma F_656d0 : fetch_word AsanUbsan.M.loaded_segments (0x65718 : word) = Some W_656d0.
Proof. vm_refl. Qed.
Lemma D_656d0 : decode_any W_656d0 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_656d4 : bv 32 := 0x06028663.
Lemma F_656d4 : fetch_word AsanUbsan.M.loaded_segments (0x6571c : word) = Some W_656d4.
Proof. vm_refl. Qed.
Lemma D_656d4 : decode_any W_656d4 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_656d8 : bv 32 := 0xfff5051b.
Lemma F_656d8 : fetch_word AsanUbsan.M.loaded_segments (0x65720 : word) = Some W_656d8.
Proof. vm_refl. Qed.
Lemma D_656d8 : decode_any W_656d8 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_656dc : bv 32 := 0x00160613.
Lemma F_656dc : fetch_word AsanUbsan.M.loaded_segments (0x65724 : word) = Some W_656dc.
Proof. vm_refl. Qed.
Lemma D_656dc : decode_any W_656dc = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_656e0 : bv 32 := 0xfe0514e3.
Lemma F_656e0 : fetch_word AsanUbsan.M.loaded_segments (0x65728 : word) = Some W_656e0.
Proof. vm_refl. Qed.
Lemma D_656e0 : decode_any W_656e0 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_65740 : bv 32 := 0x00160613.
Lemma F_65740 : fetch_word AsanUbsan.M.loaded_segments (0x65788 : word) = Some W_65740.
Proof. vm_refl. Qed.
Lemma D_65740 : decode_any W_65740 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65744 : bv 32 := 0x00100513.
Lemma F_65744 : fetch_word AsanUbsan.M.loaded_segments (0x6578c : word) = Some W_65744.
Proof. vm_refl. Qed.
Lemma D_65744 : decode_any W_65744 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65748 : bv 32 := 0xffb90693.
Lemma F_65748 : fetch_word AsanUbsan.M.loaded_segments (0x65790 : word) = Some W_65748.
Proof. vm_refl. Qed.
Lemma D_65748 : decode_any W_65748 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_6574c : bv 32 := 0x02c4b423.
Lemma F_6574c : fetch_word AsanUbsan.M.loaded_segments (0x65794 : word) = Some W_6574c.
Proof. vm_refl. Qed.
Lemma D_6574c : decode_any W_6574c = Some (Store SZ8 9 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_65750 : bv 32 := 0x00a78023.
Lemma F_65750 : fetch_word AsanUbsan.M.loaded_segments (0x65798 : word) = Some W_65750.
Proof. vm_refl. Qed.
Lemma D_65750 : decode_any W_65750 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65754 : bv 32 := 0x00d51533.
Lemma F_65754 : fetch_word AsanUbsan.M.loaded_segments (0x6579c : word) = Some W_65754.
Proof. vm_refl. Qed.
Lemma D_65754 : decode_any W_65754 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_65758 : bv 32 := 0x00500613.
Lemma F_65758 : fetch_word AsanUbsan.M.loaded_segments (0x657a0 : word) = Some W_65758.
Proof. vm_refl. Qed.
Lemma D_65758 : decode_any W_65758 = Some (OpImm ALU_ADD 12 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6575c : bv 32 := 0x00b89893.
Lemma F_6575c : fetch_word AsanUbsan.M.loaded_segments (0x657a4 : word) = Some W_6575c.
Proof. vm_refl. Qed.
Lemma D_6575c : decode_any W_6575c = Some (ShiftImm ALU_SLL 17 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_65760 : bv 32 := 0x01261633.
Lemma F_65760 : fetch_word AsanUbsan.M.loaded_segments (0x657a8 : word) = Some W_65760.
Proof. vm_refl. Qed.
Lemma D_65760 : decode_any W_65760 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_65764 : bv 32 := 0x00a58533.
Lemma F_65764 : fetch_word AsanUbsan.M.loaded_segments (0x657ac : word) = Some W_65764.
Proof. vm_refl. Qed.
Lemma D_65764 : decode_any W_65764 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_65768 : bv 32 := 0x01160633.
Lemma F_65768 : fetch_word AsanUbsan.M.loaded_segments (0x657b0 : word) = Some W_65768.
Proof. vm_refl. Qed.
Lemma D_65768 : decode_any W_65768 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_6576c : bv 32 := 0x00c504b3.
Lemma F_6576c : fetch_word AsanUbsan.M.loaded_segments (0x657b4 : word) = Some W_6576c.
Proof. vm_refl. Qed.
Lemma D_6576c : decode_any W_6576c = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_65770 : bv 32 := 0x0084bc23.
Lemma F_65770 : fetch_word AsanUbsan.M.loaded_segments (0x657b8 : word) = Some W_65770.
Proof. vm_refl. Qed.
Lemma D_65770 : decode_any W_65770 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65774 : bv 32 := 0x7ef4bc23.
Lemma F_65774 : fetch_word AsanUbsan.M.loaded_segments (0x657bc : word) = Some W_65774.
Proof. vm_refl. Qed.
Lemma D_65774 : decode_any W_65774 = Some (Store SZ8 9 15 2040, 4%Z).
Proof. vm_refl. Qed.

Definition W_65778 : bv 32 := 0x00048513.
Lemma F_65778 : fetch_word AsanUbsan.M.loaded_segments (0x657c0 : word) = Some W_65778.
Proof. vm_refl. Qed.
Lemma D_65778 : decode_any W_65778 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6577c : bv 32 := 0x178000ef.
Lemma F_6577c : fetch_word AsanUbsan.M.loaded_segments (0x657c4 : word) = Some W_6577c.
Proof. vm_refl. Qed.
Lemma D_6577c : decode_any W_6577c = Some (Jal 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_65780 : bv 32 := 0x00050593.
Lemma F_65780 : fetch_word AsanUbsan.M.loaded_segments (0x657c8 : word) = Some W_65780.
Proof. vm_refl. Qed.
Lemma D_65780 : decode_any W_65780 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65784 : bv 32 := 0x00048513.
Lemma F_65784 : fetch_word AsanUbsan.M.loaded_segments (0x657cc : word) = Some W_65784.
Proof. vm_refl. Qed.
Lemma D_65784 : decode_any W_65784 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65788 : bv 32 := 0x00000613.
Lemma F_65788 : fetch_word AsanUbsan.M.loaded_segments (0x657d0 : word) = Some W_65788.
Proof. vm_refl. Qed.
Lemma D_65788 : decode_any W_65788 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6578c : bv 32 := 0x0005b023.
Lemma F_6578c : fetch_word AsanUbsan.M.loaded_segments (0x657d4 : word) = Some W_6578c.
Proof. vm_refl. Qed.
Lemma D_6578c : decode_any W_6578c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65790 : bv 32 := 0x0005b423.
Lemma F_65790 : fetch_word AsanUbsan.M.loaded_segments (0x657d8 : word) = Some W_65790.
Proof. vm_refl. Qed.
Lemma D_65790 : decode_any W_65790 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65794 : bv 32 := 0x0005b823.
Lemma F_65794 : fetch_word AsanUbsan.M.loaded_segments (0x657dc : word) = Some W_65794.
Proof. vm_refl. Qed.
Lemma D_65794 : decode_any W_65794 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65798 : bv 32 := 0x0005bc23.
Lemma F_65798 : fetch_word AsanUbsan.M.loaded_segments (0x657e0 : word) = Some W_65798.
Proof. vm_refl. Qed.
Lemma D_65798 : decode_any W_65798 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6579c : bv 32 := 0x0205b023.
Lemma F_6579c : fetch_word AsanUbsan.M.loaded_segments (0x657e4 : word) = Some W_6579c.
Proof. vm_refl. Qed.
Lemma D_6579c : decode_any W_6579c = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_657a0 : bv 32 := 0x0205b423.
Lemma F_657a0 : fetch_word AsanUbsan.M.loaded_segments (0x657e8 : word) = Some W_657a0.
Proof. vm_refl. Qed.
Lemma D_657a0 : decode_any W_657a0 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_657a4 : bv 32 := 0x0205b823.
Lemma F_657a4 : fetch_word AsanUbsan.M.loaded_segments (0x657ec : word) = Some W_657a4.
Proof. vm_refl. Qed.
Lemma D_657a4 : decode_any W_657a4 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_657a8 : bv 32 := 0x0205bc23.
Lemma F_657a8 : fetch_word AsanUbsan.M.loaded_segments (0x657f0 : word) = Some W_657a8.
Proof. vm_refl. Qed.
Lemma D_657a8 : decode_any W_657a8 = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_657ac : bv 32 := 0x0405b023.
Lemma F_657ac : fetch_word AsanUbsan.M.loaded_segments (0x657f4 : word) = Some W_657ac.
Proof. vm_refl. Qed.
Lemma D_657ac : decode_any W_657ac = Some (Store SZ8 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_657b0 : bv 32 := 0x0405b423.
Lemma F_657b0 : fetch_word AsanUbsan.M.loaded_segments (0x657f8 : word) = Some W_657b0.
Proof. vm_refl. Qed.
Lemma D_657b0 : decode_any W_657b0 = Some (Store SZ8 11 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_657b4 : bv 32 := 0x0405b823.
Lemma F_657b4 : fetch_word AsanUbsan.M.loaded_segments (0x657fc : word) = Some W_657b4.
Proof. vm_refl. Qed.
Lemma D_657b4 : decode_any W_657b4 = Some (Store SZ8 11 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_657b8 : bv 32 := 0x0405bc23.
Lemma F_657b8 : fetch_word AsanUbsan.M.loaded_segments (0x65800 : word) = Some W_657b8.
Proof. vm_refl. Qed.
Lemma D_657b8 : decode_any W_657b8 = Some (Store SZ8 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_657bc : bv 32 := 0x0605b023.
Lemma F_657bc : fetch_word AsanUbsan.M.loaded_segments (0x65804 : word) = Some W_657bc.
Proof. vm_refl. Qed.
Lemma D_657bc : decode_any W_657bc = Some (Store SZ8 11 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_657c0 : bv 32 := 0x0605b423.
Lemma F_657c0 : fetch_word AsanUbsan.M.loaded_segments (0x65808 : word) = Some W_657c0.
Proof. vm_refl. Qed.
Lemma D_657c0 : decode_any W_657c0 = Some (Store SZ8 11 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_657c4 : bv 32 := 0x0605b823.
Lemma F_657c4 : fetch_word AsanUbsan.M.loaded_segments (0x6580c : word) = Some W_657c4.
Proof. vm_refl. Qed.
Lemma D_657c4 : decode_any W_657c4 = Some (Store SZ8 11 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_657c8 : bv 32 := 0x0605bc23.
Lemma F_657c8 : fetch_word AsanUbsan.M.loaded_segments (0x65810 : word) = Some W_657c8.
Proof. vm_refl. Qed.
Lemma D_657c8 : decode_any W_657c8 = Some (Store SZ8 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_657cc : bv 32 := 0x0805b023.
Lemma F_657cc : fetch_word AsanUbsan.M.loaded_segments (0x65814 : word) = Some W_657cc.
Proof. vm_refl. Qed.
Lemma D_657cc : decode_any W_657cc = Some (Store SZ8 11 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_657d0 : bv 32 := 0x0805b423.
Lemma F_657d0 : fetch_word AsanUbsan.M.loaded_segments (0x65818 : word) = Some W_657d0.
Proof. vm_refl. Qed.
Lemma D_657d0 : decode_any W_657d0 = Some (Store SZ8 11 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_657d4 : bv 32 := 0x0805b823.
Lemma F_657d4 : fetch_word AsanUbsan.M.loaded_segments (0x6581c : word) = Some W_657d4.
Proof. vm_refl. Qed.
Lemma D_657d4 : decode_any W_657d4 = Some (Store SZ8 11 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_657d8 : bv 32 := 0x0805bc23.
Lemma F_657d8 : fetch_word AsanUbsan.M.loaded_segments (0x65820 : word) = Some W_657d8.
Proof. vm_refl. Qed.
Lemma D_657d8 : decode_any W_657d8 = Some (Store SZ8 11 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_657dc : bv 32 := 0x0a05b023.
Lemma F_657dc : fetch_word AsanUbsan.M.loaded_segments (0x65824 : word) = Some W_657dc.
Proof. vm_refl. Qed.
Lemma D_657dc : decode_any W_657dc = Some (Store SZ8 11 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_657e0 : bv 32 := 0x0a05b423.
Lemma F_657e0 : fetch_word AsanUbsan.M.loaded_segments (0x65828 : word) = Some W_657e0.
Proof. vm_refl. Qed.
Lemma D_657e0 : decode_any W_657e0 = Some (Store SZ8 11 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_657e4 : bv 32 := 0x0a05b823.
Lemma F_657e4 : fetch_word AsanUbsan.M.loaded_segments (0x6582c : word) = Some W_657e4.
Proof. vm_refl. Qed.
Lemma D_657e4 : decode_any W_657e4 = Some (Store SZ8 11 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_657e8 : bv 32 := 0x0a05bc23.
Lemma F_657e8 : fetch_word AsanUbsan.M.loaded_segments (0x65830 : word) = Some W_657e8.
Proof. vm_refl. Qed.
Lemma D_657e8 : decode_any W_657e8 = Some (Store SZ8 11 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_657ec : bv 32 := 0x0c05b023.
Lemma F_657ec : fetch_word AsanUbsan.M.loaded_segments (0x65834 : word) = Some W_657ec.
Proof. vm_refl. Qed.
Lemma D_657ec : decode_any W_657ec = Some (Store SZ8 11 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_657f0 : bv 32 := 0x0c05b423.
Lemma F_657f0 : fetch_word AsanUbsan.M.loaded_segments (0x65838 : word) = Some W_657f0.
Proof. vm_refl. Qed.
Lemma D_657f0 : decode_any W_657f0 = Some (Store SZ8 11 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_657f4 : bv 32 := 0x0c05b823.
Lemma F_657f4 : fetch_word AsanUbsan.M.loaded_segments (0x6583c : word) = Some W_657f4.
Proof. vm_refl. Qed.
Lemma D_657f4 : decode_any W_657f4 = Some (Store SZ8 11 0 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_657f8 : bv 32 := 0x0c05bc23.
Lemma F_657f8 : fetch_word AsanUbsan.M.loaded_segments (0x65840 : word) = Some W_657f8.
Proof. vm_refl. Qed.
Lemma D_657f8 : decode_any W_657f8 = Some (Store SZ8 11 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_657fc : bv 32 := 0x0e05b023.
Lemma F_657fc : fetch_word AsanUbsan.M.loaded_segments (0x65844 : word) = Some W_657fc.
Proof. vm_refl. Qed.
Lemma D_657fc : decode_any W_657fc = Some (Store SZ8 11 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_65800 : bv 32 := 0x0e05b423.
Lemma F_65800 : fetch_word AsanUbsan.M.loaded_segments (0x65848 : word) = Some W_65800.
Proof. vm_refl. Qed.
Lemma D_65800 : decode_any W_65800 = Some (Store SZ8 11 0 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_65804 : bv 32 := 0x0e05b823.
Lemma F_65804 : fetch_word AsanUbsan.M.loaded_segments (0x6584c : word) = Some W_65804.
Proof. vm_refl. Qed.
Lemma D_65804 : decode_any W_65804 = Some (Store SZ8 11 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_65808 : bv 32 := 0x0e05bc23.
Lemma F_65808 : fetch_word AsanUbsan.M.loaded_segments (0x65850 : word) = Some W_65808.
Proof. vm_refl. Qed.
Lemma D_65808 : decode_any W_65808 = Some (Store SZ8 11 0 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_6580c : bv 32 := 0x01813083.
Lemma F_6580c : fetch_word AsanUbsan.M.loaded_segments (0x65854 : word) = Some W_6580c.
Proof. vm_refl. Qed.
Lemma D_6580c : decode_any W_6580c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65810 : bv 32 := 0x01013403.
Lemma F_65810 : fetch_word AsanUbsan.M.loaded_segments (0x65858 : word) = Some W_65810.
Proof. vm_refl. Qed.
Lemma D_65810 : decode_any W_65810 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65814 : bv 32 := 0x00813483.
Lemma F_65814 : fetch_word AsanUbsan.M.loaded_segments (0x6585c : word) = Some W_65814.
Proof. vm_refl. Qed.
Lemma D_65814 : decode_any W_65814 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65818 : bv 32 := 0x00013903.
Lemma F_65818 : fetch_word AsanUbsan.M.loaded_segments (0x65860 : word) = Some W_65818.
Proof. vm_refl. Qed.
Lemma D_65818 : decode_any W_65818 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6581c : bv 32 := 0x02010113.
Lemma F_6581c : fetch_word AsanUbsan.M.loaded_segments (0x65864 : word) = Some W_6581c.
Proof. vm_refl. Qed.
Lemma D_6581c : decode_any W_6581c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65820 : bv 32 := 0x00008067.
Lemma F_65820 : fetch_word AsanUbsan.M.loaded_segments (0x65868 : word) = Some W_65820.
Proof. vm_refl. Qed.
Lemma D_65820 : decode_any W_65820 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65840 : bv 32 := 0xff010113.
Lemma F_65840 : fetch_word AsanUbsan.M.loaded_segments (0x65888 : word) = Some W_65840.
Proof. vm_refl. Qed.
Lemma D_65840 : decode_any W_65840 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_65844 : bv 32 := 0x00113423.
Lemma F_65844 : fetch_word AsanUbsan.M.loaded_segments (0x6588c : word) = Some W_65844.
Proof. vm_refl. Qed.
Lemma D_65844 : decode_any W_65844 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65848 : bv 32 := 0x00813023.
Lemma F_65848 : fetch_word AsanUbsan.M.loaded_segments (0x65890 : word) = Some W_65848.
Proof. vm_refl. Qed.
Lemma D_65848 : decode_any W_65848 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6584c : bv 32 := 0x7f853583.
Lemma F_6584c : fetch_word AsanUbsan.M.loaded_segments (0x65894 : word) = Some W_6584c.
Proof. vm_refl. Qed.
Lemma D_6584c : decode_any W_6584c = Some (Load SZ8 true 11 10 2040, 4%Z).
Proof. vm_refl. Qed.

Definition W_65850 : bv 32 := 0x00000413.
Lemma F_65850 : fetch_word AsanUbsan.M.loaded_segments (0x65898 : word) = Some W_65850.
Proof. vm_refl. Qed.
Lemma D_65850 : decode_any W_65850 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65854 : bv 32 := 0x00058023.
Lemma F_65854 : fetch_word AsanUbsan.M.loaded_segments (0x6589c : word) = Some W_65854.
Proof. vm_refl. Qed.
Lemma D_65854 : decode_any W_65854 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65858 : bv 32 := 0x09c000ef.
Lemma F_65858 : fetch_word AsanUbsan.M.loaded_segments (0x658a0 : word) = Some W_65858.
Proof. vm_refl. Qed.
Lemma D_65858 : decode_any W_65858 = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_6585c : bv 32 := 0xfffab597.
Lemma F_6585c : fetch_word AsanUbsan.M.loaded_segments (0x658a4 : word) = Some W_6585c.
Proof. vm_refl. Qed.
Lemma D_6585c : decode_any W_6585c = Some (Auipc 11 1048491, 4%Z).
Proof. vm_refl. Qed.

Definition W_65860 : bv 32 := 0xb045b583.
Lemma F_65860 : fetch_word AsanUbsan.M.loaded_segments (0x658a8 : word) = Some W_65860.
Proof. vm_refl. Qed.
Lemma D_65860 : decode_any W_65860 = Some (Load SZ8 true 11 11 2820, 4%Z).
Proof. vm_refl. Qed.

Definition W_65864 : bv 32 := 0x00b53023.
Lemma F_65864 : fetch_word AsanUbsan.M.loaded_segments (0x658ac : word) = Some W_65864.
Proof. vm_refl. Qed.
Lemma D_65864 : decode_any W_65864 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65868 : bv 32 := 0x00b53423.
Lemma F_65868 : fetch_word AsanUbsan.M.loaded_segments (0x658b0 : word) = Some W_65868.
Proof. vm_refl. Qed.
Lemma D_65868 : decode_any W_65868 = Some (Store SZ8 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6586c : bv 32 := 0x00b53823.
Lemma F_6586c : fetch_word AsanUbsan.M.loaded_segments (0x658b4 : word) = Some W_6586c.
Proof. vm_refl. Qed.
Lemma D_6586c : decode_any W_6586c = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65870 : bv 32 := 0x00b53c23.
Lemma F_65870 : fetch_word AsanUbsan.M.loaded_segments (0x658b8 : word) = Some W_65870.
Proof. vm_refl. Qed.
Lemma D_65870 : decode_any W_65870 = Some (Store SZ8 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65874 : bv 32 := 0x02b53023.
Lemma F_65874 : fetch_word AsanUbsan.M.loaded_segments (0x658bc : word) = Some W_65874.
Proof. vm_refl. Qed.
Lemma D_65874 : decode_any W_65874 = Some (Store SZ8 10 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65878 : bv 32 := 0x02b53423.
Lemma F_65878 : fetch_word AsanUbsan.M.loaded_segments (0x658c0 : word) = Some W_65878.
Proof. vm_refl. Qed.
Lemma D_65878 : decode_any W_65878 = Some (Store SZ8 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6587c : bv 32 := 0x02b53823.
Lemma F_6587c : fetch_word AsanUbsan.M.loaded_segments (0x658c4 : word) = Some W_6587c.
Proof. vm_refl. Qed.
Lemma D_6587c : decode_any W_6587c = Some (Store SZ8 10 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_65880 : bv 32 := 0x02b53c23.
Lemma F_65880 : fetch_word AsanUbsan.M.loaded_segments (0x658c8 : word) = Some W_65880.
Proof. vm_refl. Qed.
Lemma D_65880 : decode_any W_65880 = Some (Store SZ8 10 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_65884 : bv 32 := 0x04b53023.
Lemma F_65884 : fetch_word AsanUbsan.M.loaded_segments (0x658cc : word) = Some W_65884.
Proof. vm_refl. Qed.
Lemma D_65884 : decode_any W_65884 = Some (Store SZ8 10 11 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_65888 : bv 32 := 0x04b53423.
Lemma F_65888 : fetch_word AsanUbsan.M.loaded_segments (0x658d0 : word) = Some W_65888.
Proof. vm_refl. Qed.
Lemma D_65888 : decode_any W_65888 = Some (Store SZ8 10 11 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_6588c : bv 32 := 0x04b53823.
Lemma F_6588c : fetch_word AsanUbsan.M.loaded_segments (0x658d4 : word) = Some W_6588c.
Proof. vm_refl. Qed.
Lemma D_6588c : decode_any W_6588c = Some (Store SZ8 10 11 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_65890 : bv 32 := 0x04b53c23.
Lemma F_65890 : fetch_word AsanUbsan.M.loaded_segments (0x658d8 : word) = Some W_65890.
Proof. vm_refl. Qed.
Lemma D_65890 : decode_any W_65890 = Some (Store SZ8 10 11 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_65894 : bv 32 := 0x06b53023.
Lemma F_65894 : fetch_word AsanUbsan.M.loaded_segments (0x658dc : word) = Some W_65894.
Proof. vm_refl. Qed.
Lemma D_65894 : decode_any W_65894 = Some (Store SZ8 10 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_65898 : bv 32 := 0x06b53423.
Lemma F_65898 : fetch_word AsanUbsan.M.loaded_segments (0x658e0 : word) = Some W_65898.
Proof. vm_refl. Qed.
Lemma D_65898 : decode_any W_65898 = Some (Store SZ8 10 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_6589c : bv 32 := 0x06b53823.
Lemma F_6589c : fetch_word AsanUbsan.M.loaded_segments (0x658e4 : word) = Some W_6589c.
Proof. vm_refl. Qed.
Lemma D_6589c : decode_any W_6589c = Some (Store SZ8 10 11 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_658a0 : bv 32 := 0x06b53c23.
Lemma F_658a0 : fetch_word AsanUbsan.M.loaded_segments (0x658e8 : word) = Some W_658a0.
Proof. vm_refl. Qed.
Lemma D_658a0 : decode_any W_658a0 = Some (Store SZ8 10 11 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_658a4 : bv 32 := 0x08b53023.
Lemma F_658a4 : fetch_word AsanUbsan.M.loaded_segments (0x658ec : word) = Some W_658a4.
Proof. vm_refl. Qed.
Lemma D_658a4 : decode_any W_658a4 = Some (Store SZ8 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_658a8 : bv 32 := 0x08b53423.
Lemma F_658a8 : fetch_word AsanUbsan.M.loaded_segments (0x658f0 : word) = Some W_658a8.
Proof. vm_refl. Qed.
Lemma D_658a8 : decode_any W_658a8 = Some (Store SZ8 10 11 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_658ac : bv 32 := 0x08b53823.
Lemma F_658ac : fetch_word AsanUbsan.M.loaded_segments (0x658f4 : word) = Some W_658ac.
Proof. vm_refl. Qed.
Lemma D_658ac : decode_any W_658ac = Some (Store SZ8 10 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_658b0 : bv 32 := 0x08b53c23.
Lemma F_658b0 : fetch_word AsanUbsan.M.loaded_segments (0x658f8 : word) = Some W_658b0.
Proof. vm_refl. Qed.
Lemma D_658b0 : decode_any W_658b0 = Some (Store SZ8 10 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_658b4 : bv 32 := 0x0ab53023.
Lemma F_658b4 : fetch_word AsanUbsan.M.loaded_segments (0x658fc : word) = Some W_658b4.
Proof. vm_refl. Qed.
Lemma D_658b4 : decode_any W_658b4 = Some (Store SZ8 10 11 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_658b8 : bv 32 := 0x0ab53423.
Lemma F_658b8 : fetch_word AsanUbsan.M.loaded_segments (0x65900 : word) = Some W_658b8.
Proof. vm_refl. Qed.
Lemma D_658b8 : decode_any W_658b8 = Some (Store SZ8 10 11 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_658bc : bv 32 := 0x0ab53823.
Lemma F_658bc : fetch_word AsanUbsan.M.loaded_segments (0x65904 : word) = Some W_658bc.
Proof. vm_refl. Qed.
Lemma D_658bc : decode_any W_658bc = Some (Store SZ8 10 11 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_658c0 : bv 32 := 0x0ab53c23.
Lemma F_658c0 : fetch_word AsanUbsan.M.loaded_segments (0x65908 : word) = Some W_658c0.
Proof. vm_refl. Qed.
Lemma D_658c0 : decode_any W_658c0 = Some (Store SZ8 10 11 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_658c4 : bv 32 := 0x0cb53023.
Lemma F_658c4 : fetch_word AsanUbsan.M.loaded_segments (0x6590c : word) = Some W_658c4.
Proof. vm_refl. Qed.
Lemma D_658c4 : decode_any W_658c4 = Some (Store SZ8 10 11 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_658c8 : bv 32 := 0x0cb53423.
Lemma F_658c8 : fetch_word AsanUbsan.M.loaded_segments (0x65910 : word) = Some W_658c8.
Proof. vm_refl. Qed.
Lemma D_658c8 : decode_any W_658c8 = Some (Store SZ8 10 11 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_658cc : bv 32 := 0x0cb53823.
Lemma F_658cc : fetch_word AsanUbsan.M.loaded_segments (0x65914 : word) = Some W_658cc.
Proof. vm_refl. Qed.
Lemma D_658cc : decode_any W_658cc = Some (Store SZ8 10 11 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_658d0 : bv 32 := 0x0cb53c23.
Lemma F_658d0 : fetch_word AsanUbsan.M.loaded_segments (0x65918 : word) = Some W_658d0.
Proof. vm_refl. Qed.
Lemma D_658d0 : decode_any W_658d0 = Some (Store SZ8 10 11 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_658d4 : bv 32 := 0x0eb53023.
Lemma F_658d4 : fetch_word AsanUbsan.M.loaded_segments (0x6591c : word) = Some W_658d4.
Proof. vm_refl. Qed.
Lemma D_658d4 : decode_any W_658d4 = Some (Store SZ8 10 11 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_658d8 : bv 32 := 0x0eb53423.
Lemma F_658d8 : fetch_word AsanUbsan.M.loaded_segments (0x65920 : word) = Some W_658d8.
Proof. vm_refl. Qed.
Lemma D_658d8 : decode_any W_658d8 = Some (Store SZ8 10 11 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_658dc : bv 32 := 0x0eb53823.
Lemma F_658dc : fetch_word AsanUbsan.M.loaded_segments (0x65924 : word) = Some W_658dc.
Proof. vm_refl. Qed.
Lemma D_658dc : decode_any W_658dc = Some (Store SZ8 10 11 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_658e0 : bv 32 := 0x0eb53c23.
Lemma F_658e0 : fetch_word AsanUbsan.M.loaded_segments (0x65928 : word) = Some W_658e0.
Proof. vm_refl. Qed.
Lemma D_658e0 : decode_any W_658e0 = Some (Store SZ8 10 11 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_658e4 : bv 32 := 0x00813083.
Lemma F_658e4 : fetch_word AsanUbsan.M.loaded_segments (0x6592c : word) = Some W_658e4.
Proof. vm_refl. Qed.
Lemma D_658e4 : decode_any W_658e4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_658e8 : bv 32 := 0x00013403.
Lemma F_658e8 : fetch_word AsanUbsan.M.loaded_segments (0x65930 : word) = Some W_658e8.
Proof. vm_refl. Qed.
Lemma D_658e8 : decode_any W_658e8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_658ec : bv 32 := 0x01010113.
Lemma F_658ec : fetch_word AsanUbsan.M.loaded_segments (0x65934 : word) = Some W_658ec.
Proof. vm_refl. Qed.
Lemma D_658ec : decode_any W_658ec = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_658f0 : bv 32 := 0x00008067.
Lemma F_658f0 : fetch_word AsanUbsan.M.loaded_segments (0x65938 : word) = Some W_658f0.
Proof. vm_refl. Qed.
Lemma D_658f0 : decode_any W_658f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_658f4 : bv 32 := 0x000ef597.
Lemma F_658f4 : fetch_word AsanUbsan.M.loaded_segments (0x6593c : word) = Some W_658f4.
Proof. vm_refl. Qed.
Lemma D_658f4 : decode_any W_658f4 = Some (Auipc 11 239, 4%Z).
Proof. vm_refl. Qed.

Definition W_658f8 : bv 32 := 0xbc45b583.
Lemma F_658f8 : fetch_word AsanUbsan.M.loaded_segments (0x65940 : word) = Some W_658f8.
Proof. vm_refl. Qed.
Lemma D_658f8 : decode_any W_658f8 = Some (Load SZ8 true 11 11 3012, 4%Z).
Proof. vm_refl. Qed.

Definition W_658fc : bv 32 := 0x0005b583.
Lemma F_658fc : fetch_word AsanUbsan.M.loaded_segments (0x65944 : word) = Some W_658fc.
Proof. vm_refl. Qed.
Lemma D_658fc : decode_any W_658fc = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65900 : bv 32 := 0xfff58613.
Lemma F_65900 : fetch_word AsanUbsan.M.loaded_segments (0x65948 : word) = Some W_65900.
Proof. vm_refl. Qed.
Lemma D_65900 : decode_any W_65900 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65904 : bv 32 := 0x00c5b6b3.
Lemma F_65904 : fetch_word AsanUbsan.M.loaded_segments (0x6594c : word) = Some W_65904.
Proof. vm_refl. Qed.
Lemma D_65904 : decode_any W_65904 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_65908 : bv 32 := 0xfff68693.
Lemma F_65908 : fetch_word AsanUbsan.M.loaded_segments (0x65950 : word) = Some W_65908.
Proof. vm_refl. Qed.
Lemma D_65908 : decode_any W_65908 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6590c : bv 32 := 0x00c6f6b3.
Lemma F_6590c : fetch_word AsanUbsan.M.loaded_segments (0x65954 : word) = Some W_6590c.
Proof. vm_refl. Qed.
Lemma D_6590c : decode_any W_6590c = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_65910 : bv 32 := 0x04a6f263.
Lemma F_65910 : fetch_word AsanUbsan.M.loaded_segments (0x65958 : word) = Some W_65910.
Proof. vm_refl. Qed.
Lemma D_65910 : decode_any W_65910 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_65914 : bv 32 := 0x000ef697.
Lemma F_65914 : fetch_word AsanUbsan.M.loaded_segments (0x6595c : word) = Some W_65914.
Proof. vm_refl. Qed.
Lemma D_65914 : decode_any W_65914 = Some (Auipc 13 239, 4%Z).
Proof. vm_refl. Qed.

Definition W_65918 : bv 32 := 0xbac6b683.
Lemma F_65918 : fetch_word AsanUbsan.M.loaded_segments (0x65960 : word) = Some W_65918.
Proof. vm_refl. Qed.
Lemma D_65918 : decode_any W_65918 = Some (Load SZ8 true 13 13 2988, 4%Z).
Proof. vm_refl. Qed.

Definition W_6591c : bv 32 := 0x000ef717.
Lemma F_6591c : fetch_word AsanUbsan.M.loaded_segments (0x65964 : word) = Some W_6591c.
Proof. vm_refl. Qed.
Lemma D_6591c : decode_any W_6591c = Some (Auipc 14 239, 4%Z).
Proof. vm_refl. Qed.

Definition W_65920 : bv 32 := 0xbac73703.
Lemma F_65920 : fetch_word AsanUbsan.M.loaded_segments (0x65968 : word) = Some W_65920.
Proof. vm_refl. Qed.
Lemma D_65920 : decode_any W_65920 = Some (Load SZ8 true 14 14 2988, 4%Z).
Proof. vm_refl. Qed.

Definition W_65924 : bv 32 := 0x0006b803.
Lemma F_65924 : fetch_word AsanUbsan.M.loaded_segments (0x6596c : word) = Some W_65924.
Proof. vm_refl. Qed.
Lemma D_65924 : decode_any W_65924 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65928 : bv 32 := 0x00073683.
Lemma F_65928 : fetch_word AsanUbsan.M.loaded_segments (0x65970 : word) = Some W_65928.
Proof. vm_refl. Qed.
Lemma D_65928 : decode_any W_65928 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6592c : bv 32 := 0xfff80793.
Lemma F_6592c : fetch_word AsanUbsan.M.loaded_segments (0x65974 : word) = Some W_6592c.
Proof. vm_refl. Qed.
Lemma D_6592c : decode_any W_6592c = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65930 : bv 32 := 0x00a7f463.
Lemma F_65930 : fetch_word AsanUbsan.M.loaded_segments (0x65978 : word) = Some W_65930.
Proof. vm_refl. Qed.
Lemma D_65930 : decode_any W_65930 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65938 : bv 32 := 0x000ef717.
Lemma F_65938 : fetch_word AsanUbsan.M.loaded_segments (0x65980 : word) = Some W_65938.
Proof. vm_refl. Qed.
Lemma D_65938 : decode_any W_65938 = Some (Auipc 14 239, 4%Z).
Proof. vm_refl. Qed.

Definition W_6593c : bv 32 := 0xb9873703.
Lemma F_6593c : fetch_word AsanUbsan.M.loaded_segments (0x65984 : word) = Some W_6593c.
Proof. vm_refl. Qed.
Lemma D_6593c : decode_any W_6593c = Some (Load SZ8 true 14 14 2968, 4%Z).
Proof. vm_refl. Qed.

Definition W_65940 : bv 32 := 0x00073283.
Lemma F_65940 : fetch_word AsanUbsan.M.loaded_segments (0x65988 : word) = Some W_65940.
Proof. vm_refl. Qed.
Lemma D_65940 : decode_any W_65940 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65944 : bv 32 := 0x0032d713.
Lemma F_65944 : fetch_word AsanUbsan.M.loaded_segments (0x6598c : word) = Some W_65944.
Proof. vm_refl. Qed.
Lemma D_65944 : decode_any W_65944 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_65948 : bv 32 := 0x00b708b3.
Lemma F_65948 : fetch_word AsanUbsan.M.loaded_segments (0x65990 : word) = Some W_65948.
Proof. vm_refl. Qed.
Lemma D_65948 : decode_any W_65948 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6594c : bv 32 := 0x00a2ea63.
Lemma F_6594c : fetch_word AsanUbsan.M.loaded_segments (0x65994 : word) = Some W_6594c.
Proof. vm_refl. Qed.
Lemma D_6594c : decode_any W_6594c = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_65950 : bv 32 := 0x00a8f863.
Lemma F_65950 : fetch_word AsanUbsan.M.loaded_segments (0x65998 : word) = Some W_65950.
Proof. vm_refl. Qed.
Lemma D_65950 : decode_any W_65950 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65954 : bv 32 := 0x00355513.
Lemma F_65954 : fetch_word AsanUbsan.M.loaded_segments (0x6599c : word) = Some W_65954.
Proof. vm_refl. Qed.
Lemma D_65954 : decode_any W_65954 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_65958 : bv 32 := 0x00a58533.
Lemma F_65958 : fetch_word AsanUbsan.M.loaded_segments (0x659a0 : word) = Some W_65958.
Proof. vm_refl. Qed.
Lemma D_65958 : decode_any W_65958 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6595c : bv 32 := 0x00008067.
Lemma F_6595c : fetch_word AsanUbsan.M.loaded_segments (0x659a4 : word) = Some W_6595c.
Proof. vm_refl. Qed.
Lemma D_6595c : decode_any W_6595c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

